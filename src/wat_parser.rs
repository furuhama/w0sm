#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WatNode {
    Instruction(String, Vec<WatNode>),
    Identifier(String),
    Number(i32),
}

pub struct WatParser {
    tokens: Vec<String>,
    current: usize,
}

impl WatParser {
    pub fn new(input: &str) -> Self {
        let tokens = input
            .replace('(', " ( ")
            .replace(')', " ) ")
            .split_whitespace()
            .map(String::from)
            .collect();

        WatParser { tokens, current: 0 }
    }

    pub fn parse(&mut self) -> Result<WatNode, String> {
        self.parse_node()
    }

    fn parse_node(&mut self) -> Result<WatNode, String> {
        if self.current >= self.tokens.len() {
            return Err("Unexpected end of input".to_string());
        }

        let token = &self.tokens[self.current];
        self.current += 1;

        match token.as_str() {
            "(" => {
                if self.current >= self.tokens.len() {
                    return Err("Unexpected end of input after '('".to_string());
                }

                let name = self.tokens[self.current].clone();
                self.current += 1;

                let mut args = Vec::new();
                while self.current < self.tokens.len() && self.tokens[self.current] != ")" {
                    args.push(self.parse_node()?);
                }

                if self.current >= self.tokens.len() {
                    return Err("Missing closing ')'".to_string());
                }
                self.current += 1; // Skip ')'

                Ok(WatNode::Instruction(name, args))
            }
            ")" => Err("Unexpected ')'".to_string()),
            _ => {
                if let Ok(num) = token.parse::<i32>() {
                    Ok(WatNode::Number(num))
                } else {
                    Ok(WatNode::Identifier(token.clone()))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_instruction() {
        let input = "(i32.const 42)";
        let mut parser = WatParser::new(input);
        let result = parser.parse().unwrap();
        let expected = WatNode::Instruction("i32.const".to_string(), vec![WatNode::Number(42)]);
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_nested_instruction() {
        let input = "(i32.add (i32.const 1) (i32.const 2))";
        let mut parser = WatParser::new(input);
        let result = parser.parse().unwrap();
        let expected = WatNode::Instruction(
            "i32.add".to_string(),
            vec![
                WatNode::Instruction("i32.const".to_string(), vec![WatNode::Number(1)]),
                WatNode::Instruction("i32.const".to_string(), vec![WatNode::Number(2)]),
            ],
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_identifier() {
        let input = "(global $x i32)";
        let mut parser = WatParser::new(input);
        let result = parser.parse().unwrap();
        let expected = WatNode::Instruction(
            "global".to_string(),
            vec![
                WatNode::Identifier("$x".to_string()),
                WatNode::Identifier("i32".to_string()),
            ],
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_mutable_global() {
        let input = "(global $x (mut i32) (i32.const 42))";
        let mut parser = WatParser::new(input);
        let result = parser.parse().unwrap();
        let expected = WatNode::Instruction(
            "global".to_string(),
            vec![
                WatNode::Identifier("$x".to_string()),
                WatNode::Instruction(
                    "mut".to_string(),
                    vec![WatNode::Identifier("i32".to_string())],
                ),
                WatNode::Instruction("i32.const".to_string(), vec![WatNode::Number(42)]),
            ],
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_module() {
        let input = "(module (func $add (param i32 i32) (result i32)))";
        let mut parser = WatParser::new(input);
        let result = parser.parse().unwrap();
        let expected = WatNode::Instruction(
            "module".to_string(),
            vec![WatNode::Instruction(
                "func".to_string(),
                vec![
                    WatNode::Identifier("$add".to_string()),
                    WatNode::Instruction(
                        "param".to_string(),
                        vec![
                            WatNode::Identifier("i32".to_string()),
                            WatNode::Identifier("i32".to_string()),
                        ],
                    ),
                    WatNode::Instruction(
                        "result".to_string(),
                        vec![WatNode::Identifier("i32".to_string())],
                    ),
                ],
            )],
        );
        assert_eq!(result, expected);
    }

    #[test]
    fn test_parse_error_unexpected_end() {
        let input = "(i32.const";
        let mut parser = WatParser::new(input);
        let result = parser.parse();
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_error_unexpected_paren() {
        let input = ")";
        let mut parser = WatParser::new(input);
        let result = parser.parse();
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_error_missing_closing_paren() {
        let input = "(i32.const 42";
        let mut parser = WatParser::new(input);
        let result = parser.parse();
        assert!(result.is_err());
    }
}
