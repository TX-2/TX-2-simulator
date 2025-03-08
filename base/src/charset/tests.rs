use super::super::u6;
use super::{
    lincoln_to_unicode_strict, LincolnChar, LincolnToUnicodeStrictConversionFailure,
    UnicodeToLincolnMapping,
};

#[test]
fn test_lincoln_to_unicode_strict() {
    // Regular script
    assert_eq!(
        // Start in lower case.
        lincoln_to_unicode_strict(&[u6!(0o27), u6!(0o24), u6!(0o33), u6!(0o33), u6!(0o36)]),
        Ok("HELLO".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            u6!(0o64), // Superscript
            u6!(0o27),
            u6!(0o24),
            u6!(0o33),
            u6!(0o33),
            u6!(0o36)
        ]), // HELLO
        Ok("ᴴᴱᴸᴸᴼ".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            u6!(0o65), // Normal
            u6!(0o27), // H
            u6!(0o66), // Subscript
            u6!(0o02), // 2
            u6!(0o65), // Normal
            u6!(0o36)  // O
        ]),
        Ok("H₂O".to_string())
    );

    assert_eq!(
        lincoln_to_unicode_strict(&[
            u6!(0o75), // Upper case
            u6!(0o52), // { (when upper case)
            u6!(0o53), // } (when upper case)
            u6!(0o74), // Lower case
            u6!(0o52), // ( (when lower case)
            u6!(0o53), // ) (when lower case)
        ]),
        Ok("{}()".to_string())
    );
}

#[test]
fn test_lincoln_to_unicode_carriage_return() {
    assert_eq!(
        lincoln_to_unicode_strict(&[
            u6!(0o75), // Upper case
            u6!(0o06), // when upper case, '#'
            u6!(0o74), // Lower case
            u6!(0o06), // when lower case, '6'
            u6!(0o64), // superscript
            u6!(0o20), // A
            u6!(0o60), // carriage return
            // Now lower case, normal script
            u6!(0o06), // when lower case, '6'
        ]),
        Ok("#6ᴬ\r6".to_string())
    );
}

#[test]
fn round_trip() {
    fn must_round_trip(input: &str, mapping: &UnicodeToLincolnMapping) {
        match mapping.to_lincoln(input) {
            Ok(bytes) => match lincoln_to_unicode_strict(bytes.as_slice()) {
                Ok(s) => {
                    assert_eq!(input, s);
                }
                Err(e) => {
                    panic!("failed to convert back to unicode: {}", e);
                }
            },
            Err(e) => {
                panic!("failed to convert [{}] to Lincoln: {}", input, e);
            }
        }
    }

    let ulmap = UnicodeToLincolnMapping::new();
    must_round_trip("HELLO, WORLD.  012345", &ulmap);
    must_round_trip("(){}*", &ulmap);
    must_round_trip("\u{2227}", &ulmap); // Logical And (looks like caret but isn't)
    must_round_trip("iyzjkph", &ulmap);
    must_round_trip("\u{03B1}\u{03B2}", &ulmap); // Greek small letter alpha, Greek beta
    must_round_trip("\t\r", &ulmap);
    must_round_trip("\u{2080}", &ulmap); // ₀
    must_round_trip("\u{2081}", &ulmap); // ₁
    must_round_trip("\u{2082}", &ulmap); // ₂
    must_round_trip("\u{2083}", &ulmap); // ₃
    must_round_trip("\u{2084}", &ulmap); // ₄
    must_round_trip("\u{2085}", &ulmap); // ₅
    must_round_trip("\u{2086}", &ulmap); // ₆
    must_round_trip("\u{2087}", &ulmap); // ₇
    must_round_trip("\u{2088}", &ulmap); // ₈
    must_round_trip("\u{2089}", &ulmap); // ₉
    must_round_trip("\u{208B}", &ulmap); // ₋
    must_round_trip(".", &ulmap);
    must_round_trip("\u{2070}", &ulmap);
    must_round_trip("\u{00B9}", &ulmap);
    must_round_trip("\u{00B2}", &ulmap);
    must_round_trip("\u{00B3}", &ulmap);
    must_round_trip("\u{2074}", &ulmap);
    must_round_trip("\u{2075}", &ulmap);
    must_round_trip("\u{2076}", &ulmap);
    must_round_trip("\u{2077}", &ulmap);
    must_round_trip("\u{2078}", &ulmap);
    must_round_trip("\u{2079}", &ulmap);
    must_round_trip("\u{207A}", &ulmap); // U+207A, superscript plus
    must_round_trip("\u{207B}", &ulmap); // U+207B, superscript minus
    must_round_trip("ᴬ", &ulmap);
    must_round_trip("ᴮ", &ulmap);
    must_round_trip("\u{A7F2}", &ulmap);
    must_round_trip("ᴰ", &ulmap);
    must_round_trip("ᴱ", &ulmap);
    must_round_trip("\u{A7F3}", &ulmap);
    must_round_trip("ᴳ", &ulmap);
    must_round_trip("ᴴ", &ulmap);
    must_round_trip("ᴵ", &ulmap);
    must_round_trip("ᴶ", &ulmap);
    must_round_trip("ᴷ", &ulmap);
    must_round_trip("ᴸ", &ulmap);
    must_round_trip("ᴹ", &ulmap);
    must_round_trip("ᴺ", &ulmap);
    must_round_trip("ᴼ", &ulmap);
    must_round_trip("ᴾ", &ulmap);
    must_round_trip("\u{A7F4}", &ulmap);
    must_round_trip("ᴿ", &ulmap);
    must_round_trip("\u{209B}", &ulmap);
    must_round_trip("ᵀ", &ulmap);
    must_round_trip("ᵁ", &ulmap);
    must_round_trip("ⱽ", &ulmap);
    must_round_trip("ᵂ", &ulmap);
    must_round_trip("\u{2093}", &ulmap);
    must_round_trip("YZ", &ulmap);
    must_round_trip("|\u{2016}", &ulmap); // single, double vertical line

    // Some characters in the Lincoln Writer character set do not
    // advance the carriage (these are 0o12 and 0o13, both upper and
    // lower case for each).  We convert these into Unicode combining
    // characters.
    must_round_trip(
        concat!(
            "\u{0332}", // combining low line
            "\u{0305}", // combining overline
        ),
        &ulmap,
    );
    must_round_trip(
        concat!(
            "\u{20DD}", // combining enclosing circle
            "\u{20DE}", // combining enclosing square
        ),
        &ulmap,
    );
}

#[test]
fn missing_superscript() {
    // There is no superscript uppercase Y in Unicode 14.0.0.  So we
    // expect the mapping to fail.
    //
    // I (James Youngman) believe that the left-hand column in table
    // 7-6 of the Users handbook is "lower case" even though this
    // actually contains upper-case letters.  This is based on the
    // idea that the LW defaults to "lower case" and only there is a
    // full set of block capitals, but not minuscule letters.
    //
    // This is quite confusing and it's another illustration of why
    // it's important to find authentic software to act as a
    // reality-check.
    assert_eq!(
        lincoln_to_unicode_strict(&[
            u6!(0o74), // lower case
            u6!(0o64), // superscript
            u6!(0o50)  // Y
        ]),
        Err(LincolnToUnicodeStrictConversionFailure::CannotSuperscript(
            u6!(0o50),
            LincolnChar::UnicodeBaseChar('Y'),
        ))
    );
}

#[test]
fn no_mapping() {
    assert_eq!(
        lincoln_to_unicode_strict(&[u6!(0o14)]), // "READ IN"
        Ok("".to_string()),
    );
}
