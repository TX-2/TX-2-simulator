use tracing::{Level, event};
use web_sys::Document;

use base::Unsigned6Bit;
use base::charset::{Colour, DescribedChar, LincolnChar, LincolnState, Script};

/// Generate HTML corresponding to Lincoln Writer character (in the given state).
///
/// While currently we use sup/sub elements here, this does not quite
/// correspond with the way the Lincoln Writer generated
/// superscript/subscript letters.  For the LW, these corresponded to
/// half-line movements of the platen (see pages 9-11) of "The Lincoln
/// Writer" (Lincoln Lab Group Report 51-8).
///
/// Also, the "line feed up" and "line feed down" characters don't
/// affect the script in effect.  Per page 10 of "The Lincoln Writer"
/// (i.e. the same document mentioned above):
///
/// > The line feed selectors do not affect the last remembered script
/// > position of the typewriter. Therefore after one or more line feed selections,
/// > care must be taken to return the typewriter platen to its original
/// > position by the selection of the opposite line feed. For example, if the
/// > typewriter platen were in normal script position and a line feed-up were
/// > selected - followed by printable characters, the printed result would be
/// > the same as if a superscript had been selected. However, if this were to
/// > be followed by a normal script selection there would be no change since
/// > the typewriter would act as if it was already in normal script, (since
/// > no other script had been selected). Consequently the line feed selections
/// > should be used for situations like superscripting a superscript or
/// > subscripting a subscript, etc. On these occasions the opposite line feed
/// > should be used to return the typewriter to its original script position.
fn generate_html_for_char(uch: char, attributes: &LincolnState, _advance: bool) -> String {
    let colour_class = match attributes.colour {
        // These styles are defined in index.html, not in CSS files
        // (because those styles get renamed).
        Colour::Black => "lwb",
        Colour::Red => "lwr",
    };
    let (script_open, script_close) = match attributes.script {
        Script::Normal => ("", ""),
        Script::Super => ("<sup>", "</sup>"),
        Script::Sub => ("<sub>", "</sub>"),
    };
    // TODO: By recalling existing colour and script information we
    // could save on volume of output here.
    format!("<span class=\"{colour_class}\">{script_open}{uch}{script_close}</span>")
}

pub(crate) fn display_lw_unit_output_event(unit: Unsigned6Bit, ch: DescribedChar, doc: Document) {
    event!(
        Level::INFO,
        "display_lw_unit_output_event: handling output event for LW unit {unit:?}"
    );
    let current_line_element_id = format!("lw{unit:o}-current-line");
    let current_line_el = doc
        .get_element_by_id(&current_line_element_id)
        .expect("LW current line element is missing from HTML document");
    let mut current_line_text = current_line_el.inner_html();
    match ch {
        DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar('\r'),
            ..
        } => {
            event!(Level::INFO, "LW: processing a carriage return");
            let history_element_id = format!("lw{unit:o}-history");
            let history_el = doc
                .get_element_by_id(&history_element_id)
                .expect("LW history element is missing from HTML document");
            // Append the current line to the history.
            let mut history_text = history_el.inner_html();
            history_text.push_str(&current_line_text);
            history_text.push_str("<br/>\r\n");
            history_el.set_inner_html(&history_text);
            // Clear the current line.
            current_line_el.set_inner_html("");
        }
        DescribedChar {
            base_char: LincolnChar::Unprintable(_),
            ..
        } => {
            // We don't print unprintable characters.
        }
        DescribedChar {
            base_char: LincolnChar::UnicodeBaseChar(uch),
            attributes,
            advance,
            unicode_representation: _,
            label_matches_unicode: _,
        } => {
            let s: String = generate_html_for_char(uch, &attributes, advance);
            current_line_text.push_str(&s);
            current_line_el.set_inner_html(&current_line_text);
        }
    }
}
