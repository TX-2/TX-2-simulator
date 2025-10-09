/// Generate bug-report URLs.
use url::{ParseError, Url};

// We have a version override for idna_adapter in the Cargo.toml file,
// because GITHUB_URL is ASCII-only and we want to keep the size of
// the binary down.
use idna_adapter as _;

const GITHUB_URL: &str = "https://github.com/";
const ORG_NAME: &str = "TX-2";
const REPO_NAME: &str = "TX-2-simulator";

#[derive(Debug, Clone, Copy, PartialOrd, Ord, Hash, Eq, PartialEq)]
pub enum IssueType {
    Io,
    Opcode,
}

#[must_use]
pub fn bug_report_url(title: &str, issue_type: Option<IssueType>) -> Url {
    bug_report_url_internal(title, issue_type).expect("bug-report URLs should always be valid")
}

fn bug_report_url_internal(title: &str, issue_type: Option<IssueType>) -> Result<Url, ParseError> {
    let mut url = Url::parse(GITHUB_URL)?.join(&format!("{ORG_NAME}/{REPO_NAME}/issues/new"))?;
    url.query_pairs_mut()
        .append_pair("template", "bug_report.md")
        .append_pair("title", title);
    match issue_type {
        Some(IssueType::Io) => {
            url.query_pairs_mut().append_pair("labels", "I/O");
        }
        Some(IssueType::Opcode) => {
            url.query_pairs_mut().append_pair("labels", "Opcode");
        }
        None => (), // add no labels.
    }
    Ok(url)
}

#[test]
fn test_bug_report_url() {
    assert_eq!(
        bug_report_url("Eat some falafel", Some(IssueType::Io)).to_string(),
        "https://github.com/TX-2/TX-2-simulator/issues/new?template=bug_report.md&title=Eat+some+falafel&labels=I%2FO"
    );
}
