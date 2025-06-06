use once_cell::sync::Lazy;
use regex::Regex;

use crate::{formula::BinOpBase, scope::Scope, term::Term};


static IDENTIFIER_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\d+").unwrap());
static REPR_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"\w+").unwrap());
static VALUE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"[^,]*").unwrap());

static INSTANTIATE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"instantiate *(?<theorem>\d+) (?:with (?<values>(?: *[^,] *,?)+))?").unwrap());
static MODUS_PONENS_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"modus ponens *(?<theorem>\d+|G) *").unwrap());
static NAME_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"name *(?<values>(?: *[^,]+ *,?)*) *").unwrap());
static REWRITE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"rewrite with *(?<theorem>\d+) *").unwrap());
static EVAL_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"eval").unwrap());
static QED_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"qed").unwrap());
static CONTRADICT_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"contradict").unwrap());
static COMBINE_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"combine *(?<a>\d+) *with *(?<b>\d+) *").unwrap());
static SIMPLIFY_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"simplify *(?<theorem>\d+) *").unwrap());
static INTRO_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"intro").unwrap());
static WEAKEN_RE: Lazy<Regex> = Lazy::new(|| Regex::new(r"weaken (?<theorem>\d+) to (?<target>\w+)").unwrap());

#[derive(Debug)]
pub enum Operation {
    Instantiate(usize, Vec<Term>),
    ModusPonens(usize), ModusPonensGoal,
    Name(Vec<Term>),
    Rewrite(usize),
    Eval,
    QED,
    Contradict,
    Combine(usize, usize),
    Simplify(usize),
    Intro,
    Weaken(usize, BinOpBase)
}

impl Operation {
    pub fn parse(scope: &Scope, source: &str) -> Result<Self, String> {
        if let Some(captures) = INSTANTIATE_RE.captures(source) {
            
            let mut terms: Vec<Term> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                match scope.parse_term(hit.as_str()) {
                    Err(err) => { return Err(format!("Unable to parse this as a term. '{}' yields '{err}'", hit.as_str())); }
                    Ok(term) => { terms.push(term); }
                }
            }

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Instantiate(key, terms))
            } else { Err(format!("Cannot parse '{}' as a key", &captures["theorem"]).to_string()) }

        } else if let Some(captures) = MODUS_PONENS_RE.captures(source) {
            
            if captures["theorem"].starts_with("G") { Ok(Operation::ModusPonensGoal) } else {
                if let Ok(key) = captures["theorem"].parse::<usize>() {
                    Ok(Operation::ModusPonens(key))
                } else { Err(format!("Cannot parse '{}' as a key", &captures["theorem"]).to_string()) }
            }    
        
        } else if let Some(captures) = NAME_RE.captures(source) {
            
            let mut terms: Vec<Term> = Vec::new();

            for hit in VALUE_RE.find_iter(&captures["values"]) {
                match scope.parse_term(hit.as_str()) {
                    Err(err) => { return Err(format!("Unable to parse this as a term. '{}' yields '{err}'", hit.as_str())); }
                    Ok(term) => { terms.push(term); }
                }
            }

            Ok(Operation::Name(terms))
        
        } else if let Some(captures) = REWRITE_RE.captures(source) {

            if let Ok(key) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Rewrite(key))
            } else { Err(format!("Cannot parse '{}' as a key", &captures["theorem"]).to_string()) } 

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
                } else { Err(format!("Cannot parse '{}' as a key", &captures["b"]).to_string()) }
            } else { Err(format!("Cannot parse '{}' as a key", &captures["a"]).to_string()) }

        } else if let Some(captures) = SIMPLIFY_RE.captures(source) {

            if let Ok(theorem) = captures["theorem"].parse::<usize>() {
                Ok(Operation::Simplify(theorem))
            } else { Err(format!("Cannot parse '{}' as a key", &captures["theorem"]).to_string()) }

        } else if INTRO_RE.is_match(&source) {

            Ok(Operation::Intro)

        } else if let Some(captures) = WEAKEN_RE.captures(source) {

            if let Ok(theorem) = captures["theorem"].parse::<usize>() {
                if let Ok(binop) = BinOpBase::try_from(&captures["target"]) {
                    Ok(Operation::Weaken(theorem, binop))
                } else { Err(format!("Cannot parse '{}' as a binary operator", &captures["target"]).to_string()) }
            } else { Err(format!("Cannot parse '{}' as a key", &captures["theorem"]).to_string()) }

        } else { Err("Couldn't parse source".to_string()) }
    }
}
