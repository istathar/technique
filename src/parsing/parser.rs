// parsing machinery

// struct TechniqueParser;

use chumsky::{prelude::*, Span};

pub fn parse_via_chumsky(content: &str) {
    let result = parse_identifier().parse(content);
    println!("{:?}", result);
    std::process::exit(0);
}

type Identifier = String;

// takes a single lower case character then any lower case character, digit,
// or unerscore. Based on the parser code in chumsky::text::ident().

fn parse_identifier() -> impl Parser<char, Identifier, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_lowercase())
        .map(Some)
        .chain::<char, Vec<_>, _>(
            filter(|c: &char| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == '_').repeated(),
        )
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_identifier_rules() {
        let input = "make_dinner";

        let result = parse_identifier().parse(input);

        assert_eq!(result, Ok("make_dinner".to_string()));

        let input = "";

        let result = parse_identifier().parse(input);

        assert!(result.is_err());

        let input = "MakeDinner";

        let result = parse_identifier().parse(input);

        assert!(result.is_err());
    }

    // Import all parent module items
    /*
        #[test]
        fn check_procedure_declaration_explicit() {
            let input = "making_coffee : Beans, Milk -> Coffee";

            // let declaration = TechniqueParser::parse(Rule::declaration, &input)
            //     .expect("Unsuccessful Parse")
            //     .next()
            //     .unwrap();

            assert_eq!(
                input, // FIXME
                "making_coffee : Beans, Milk -> Coffee"
            );

            // assert_eq!(identifier.as_str(), "making_coffee");
            // assert_eq!(identifier.as_rule(), Rule::identifier);

            // assert_eq!(signature.as_str(), "Beans, Milk -> Coffee");
            // assert_eq!(signature.as_rule(), Rule::signature);

            // assert_eq!(domain1.as_str(), "Beans");
            // assert_eq!(domain1.as_rule(), Rule::forma);

            // assert_eq!(domain2.as_str(), "Milk");
            // assert_eq!(domain2.as_rule(), Rule::forma);

            // assert_eq!(range.as_str(), "Coffee");
            // assert_eq!(range.as_rule(), Rule::forma);
        }
    */
    /*
        #[test]
        fn check_procedure_declaration_macro() {
            parses_to! {
                parser: TechniqueParser,
                input: "making_coffee : Beans, Milk -> Coffee",
                rule: Rule::declaration,
                tokens: [
                    declaration(0, 37, [
                        identifier(0, 13),
                        signature(16, 37, [
                            forma(16, 21),
                            forma(23, 27),
                            forma(31, 37)
                        ])
                    ])
                ]
            };
        }

        #[test]
        fn check_header_spdx() {
            parses_to! {
                parser: TechniqueParser,
                input: "! MIT; (c) ACME, Inc.",
                rule: Rule::spdx_line,
                tokens: [
                    spdx_line(0, 21, [
                        license(2, 5),
                        copyright(7, 21, [
                            owner(11, 21)
                        ])
                    ])
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "! MIT; (c) 2024 ACME, Inc.",
                rule: Rule::spdx_line,
                tokens: [
                    spdx_line(0, 26, [
                        license(2, 5),
                        copyright(7, 26, [
                            year(11, 15),
                            owner(16, 26)
                        ])
                    ])
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "! PD",
                rule: Rule::spdx_line,
                tokens: [
                    spdx_line(0, 4, [
                        license(2, 4)
                    ])
                ]
            };

            parses_to! {
                parser: TechniqueParser,
                input: "MIT",
                rule: Rule::license,
                tokens: [
                    license(0, 3),
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "Public Domain",
                rule: Rule::license,
                tokens: [
                    license(0, 13),
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "CC BY-SA 3.0 IGO",
                rule: Rule::license,
                tokens: [
                    license(0, 16),
                ]
            };

            parses_to! {
                parser: TechniqueParser,
                input: "2024",
                rule: Rule::year,
                tokens: [
                    year(0, 4),
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "2024-",
                rule: Rule::year,
                tokens: [
                    year(0, 5),
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "2002-2024",
                rule: Rule::year,
                tokens: [
                    year(0, 9),
                ]
            };
            fails_with! {
                parser: TechniqueParser,
                input: "02",
                rule: Rule::year,
                positives: [Rule::year],
                negatives: [],
                pos: 0
            };
            fails_with! {
                parser: TechniqueParser,
                input: "02-24",
                rule: Rule::year,
                positives: [Rule::year],
                negatives: [],
                pos: 0
            };
        }

        #[test]
        fn check_header_template() {
            parses_to! {
                parser: TechniqueParser,
                input: "& checklist",
                rule: Rule::template_line,
                tokens: [
                    template_line(0, 11, [
                        template(2, 11)
                    ])
                ]
            };
            parses_to! {
                parser: TechniqueParser,
                input: "& nasa-flight-plan-v4.0",
                rule: Rule::template_line,
                tokens: [
                    template_line(0, 23, [
                        template(2, 23)
                    ])
                ]
            };
            fails_with! {
                parser: TechniqueParser,
                input: "&",
                rule: Rule::template_line,
                positives: [Rule::template],
                negatives: [],
                pos: 1
            };
        }

    #[test]
    fn check_declaration_syntax() {
        parses_to! {
            parser: TechniqueParser,
            input: "p :",
            rule: Rule::declaration,
            tokens: [
                declaration(0, 3, [
                    identifier(0, 1)
                ])
            ]
        };
        parses_to! {
            parser: TechniqueParser,
            input: "p : A -> B",
            rule: Rule::declaration,
            tokens: [
                declaration(0, 10, [
                    identifier(0, 1),
                    signature(4, 10, [
                        forma(4, 5),
                        forma(9, 10)
                    ])
                ])
            ]
        };
        fails_with! {
            parser: TechniqueParser,
            input: "cook-pizza :",
            rule: Rule::declaration,
            positives: [Rule::declaration],
            negatives: [],
            pos: 0
        };
    }
    */
}
