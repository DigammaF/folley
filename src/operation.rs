use once_cell::sync::Lazy;
use regex::Regex;

use crate::Domain;


static IDENTIFIER_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\d+").unwrap());
static REPR_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\w+").unwrap());
static VALUE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[^,]").unwrap());

static INSTANTIATE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"instantiate *(?<theorem>\d+) *(?:with *(?<values>[^,]+ *(?:, *[^,]+ *)*))? *").unwrap());
static MODUS_PONENS_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"modus ponens *(?<theorem>\d+|G) *").unwrap());
static NAME_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"name *(?<values>[^,]+ *(?:, *[^,]+ *)*) *").unwrap());
static REWRITE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"rewrite with *(?<theorem>\d+) *").unwrap());
static EVAL_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"eval").unwrap());
static QED_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"qed").unwrap());
static CONTRADICT_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"contradict").unwrap());
static COMBINE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"combine *(?<a>\d+) *with *(?<b>\d+) *").unwrap());
static SIMPLIFY_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"simplify *(?<theorem>\d+) *").unwrap());

#[derive(Debug)]
pub enum Operation {
    Instantiate(usize, Vec<Domain>),
    ModusPonens(usize), ModusPonensGoal,
    Name(Vec<Domain>),
    Rewrite(usize),
    Eval,
    QED,
    Contradict,
    Combine(usize, usize),
    Simplify(usize)
}

impl Operation {
    pub fn parse(source: &str) -> Result<Self, String> {
        if let Some(captures) = INSTANTIATE_RE.captures(source) {
            
            let mut values: Vec<Domain> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                if let Ok(value) = hit.as_str().parse::<Domain>() {
                    values.push(value);
                } else { return Err(format!("Unable to parse {} to a domain value", hit.as_str()).to_string()); }
            }

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Instantiate(key, values))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }

        } else if let Some(captures) = MODUS_PONENS_RE.captures(source) {
            
            if captures["theorem"].starts_with("G") { Ok(Operation::ModusPonensGoal) } else {
                if let Ok(key) = captures["theorem"].parse::<usize>() {
                    Ok(Operation::ModusPonens(key))
                } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }
            }    
        
        } else if let Some(captures) = NAME_RE.captures(source) {
            
            let mut values: Vec<Domain> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                if let Ok(value) = hit.as_str().parse::<Domain>() {
                    values.push(value);
                } else { return Err(format!("Unknown symbol {}", hit.as_str()).to_string()); }
            }

            Ok(Operation::Name(values))
        
        } else if let Some(captures) = REWRITE_RE.captures(source) {

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Rewrite(key))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) } 

        } else if EVAL_RE.is_match(&source) {

            Ok(Operation::Eval)

        } else if QED_RE.is_match(&source) {

            Ok(Operation::QED)

        } else if CONTRADICT_RE.is_match(&source) {

            Ok(Operation::Contradict)

        } else if let Some(captures) = COMBINE_RE.captures(source) {

            if let Ok(a) = captures["a"].parse::<usize>() {
                if let Ok(b) = captures["b"].parse::<usize>() {
                    Ok(Operation::Combine(a, b))
                } else { Err(format!("Cannot parse {} as a key", &captures["b"]).to_string()) }
            } else { Err(format!("Cannot parse {} as a key", &captures["a"]).to_string()) }

        } else if let Some(captures) = SIMPLIFY_RE.captures(source) {

            if let Ok(theorem) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Simplify(theorem))
            } else { Err(format!("Cannot parse {} as a key", &captures["theorem"]).to_string()) }

        } else { Err("Couldn't parse source".to_string()) }
    }
}
