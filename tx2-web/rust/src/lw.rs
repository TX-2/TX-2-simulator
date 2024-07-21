use tracing::{event, Level};
use web_sys::Document;

use base::charset::{Colour, DescribedChar, LincolnChar, LincolnState, Script};
use base::Unsigned6Bit;

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
    let current_line_element_id = format!("lw{:o}-current-line", unit);
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
            let history_element_id = format!("lw{:o}-history", unit);
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
