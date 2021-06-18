use crate::query_model::{get_quantifiers, BoxType, ExprRef, Model, QGBox, QuantifierRef};
use std::collections::HashSet;
use std::rc::Rc;

pub struct DotGenerator {
    output: String,
    indent: u32,
}

impl DotGenerator {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
        }
    }

    pub fn generate(mut self, m: &Model, sql_string: &str) -> Result<String, String> {
        self.new_line("digraph G {");
        self.inc();
        self.new_line("compound = true");
        self.new_line("labeljust = l");
        self.new_line(&format!("label=\"{}\"", sql_string));
        self.new_line("node [ shape = box ]");

        let mut box_stack = vec![Rc::clone(&m.top_box)];
        let mut quantifiers = Vec::new();
        let mut visited_boxes = HashSet::new();
        while let Some(b) = box_stack.pop() {
            if !visited_boxes.insert(b.as_ptr()) {
                continue;
            }
            let mut arrows: Vec<(ExprRef, QuantifierRef, QuantifierRef)> = Vec::new();
            let mut other_predicates: Vec<ExprRef> = Vec::new();

            let b = b.borrow();
            if let Some(predicates) = &b.predicates {
                for p in predicates {
                    let q = get_quantifiers(p);

                    // at least one quantifier must belong to the current box in order for the predicate to be displayed
                    // as an arrow
                    let mut any: bool = false;
                    for iq in b.quantifiers.iter() {
                        if q.contains(iq) {
                            any = true;
                            break;
                        }
                    }

                    match (any, q.len()) {
                        (true, 1) => {
                            let mut it = q.iter();
                            let q1 = it.next().unwrap();
                            arrows.push((Rc::clone(p), Rc::clone(q1), Rc::clone(q1)));
                        }
                        (true, 2) => {
                            let mut it = q.iter();
                            let q1 = it.next().unwrap();
                            let q2 = it.next().unwrap();
                            arrows.push((Rc::clone(p), Rc::clone(q1), Rc::clone(q2)));
                        }
                        _ => {
                            other_predicates.push(Rc::clone(p));
                        }
                    }
                }
            }

            self.new_line(&format!("subgraph cluster{} {{", b.id));
            self.inc();
            self.new_line(&format!(
                "label = \"Box{}:{}\"",
                b.id,
                Self::get_box_title(&b)
            ));
            self.new_line(&format!(
                "boxhead{} [ shape = record, label=\"{{ {} }}\" ]",
                b.id,
                Self::get_box_head(&b, &other_predicates[..])
            ));

            self.new_line("{");
            self.inc();
            self.new_line("rank = same");

            if b.quantifiers.len() > 0 {
                self.new_line("node [ shape = circle ]");
            }

            for q in b.quantifiers.iter() {
                quantifiers.push(Rc::clone(&q));

                let q = q.borrow();
                box_stack.push(Rc::clone(&q.input_box));
                self.new_line(&format!(
                    "Q{0} [ label=\"Q{0}({1})\" ]",
                    q.id, q.quantifier_type
                ));
            }

            if arrows.len() > 0 {
                self.new_line("edge [ arrowhead = none, style = solid ]");
                for (e, q1, q2) in &arrows {
                    self.new_line(&format!(
                        "Q{0} -> Q{1} [ label=\"{2}\" ]",
                        q1.borrow().id,
                        q2.borrow().id,
                        e.borrow()
                    ));
                }
            }

            self.dec();
            self.new_line("}");
            self.dec();
            self.new_line("}");
        }

        if quantifiers.len() > 0 {
            self.new_line("edge [ arrowhead = none, style = dashed ]");
            for q in quantifiers.iter() {
                let q = q.borrow();
                self.new_line(&format!(
                    "Q{0} -> boxhead{1} [ lhead = cluster{1} ]",
                    q.id,
                    q.input_box.borrow().id
                ));
            }
        }

        self.dec();
        self.new_line("}");
        self.new_line(""); // final empty line
        Ok(self.output)
    }

    fn get_box_head(b: &QGBox, predicates: &[ExprRef]) -> String {
        let mut r = String::new();

        r.push_str(&format!("Distinct: {:?}", b.distinct_operation));
        if b.distinct_tuples() {
            r.push_str(" (DISTINCT TUPLES)")
        }
        if b.one_tuple_at_most() {
            r.push_str("| ONE TUPLE AT MOST")
        }
        for (i, c) in b.columns.iter().enumerate() {
            r.push_str(&format!("| {}: {}", i, c.expr.borrow()));
            if let Some(c) = &c.name {
                r.push_str(&format!(" AS {}", c));
            }
        }
        for expr in predicates {
            r.push_str(&format!("| {}", expr.borrow()));
        }
        match &b.box_type {
            BoxType::Select(s) => {
                if s.order_by.is_some() {
                    r.push_str("| ORDER");
                    for p in s.order_by.as_ref().unwrap().iter() {
                        r.push_str(&format!(" {} {:?}", p.expr.borrow(), p.dir));
                    }
                }
                if s.limit.is_some() {
                    r.push_str(&format!("| LIMIT {}", s.limit.as_ref().unwrap().borrow()));
                }
            }
            BoxType::Grouping(g) => {
                r.push_str("| GROUP");
                for p in g.groups.iter() {
                    r.push_str(&format!(" {} {:?}", p.expr.borrow(), p.dir));
                }
            }
            BoxType::Values(values) => {
                for row in values {
                    r.push_str("| ");
                    for (i, value) in row.iter().enumerate() {
                        if i > 0 {
                            r.push_str(", ");
                        }
                        r.push_str(&format!("{}", value.borrow()));
                    }
                }
            }
            _ => {}
        }
        for key in b.unique_keys.iter() {
            r.push_str(&format!("| UNIQUE KEY {:?}", key));
        }
        r.replace("<", "\\<").replace(">", "\\>")
    }

    fn get_box_title(b: &QGBox) -> String {
        match &b.box_type {
            BoxType::BaseTable(metadata) => format!("{} {}", b.get_box_type_str(), metadata.name),
            _ => b.get_box_type_str().to_string(),
        }
    }

    fn inc(&mut self) {
        self.indent += 1;
    }

    fn dec(&mut self) {
        self.indent -= 1;
    }

    fn append(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn new_line(&mut self, s: &str) {
        if !self.output.is_empty() && self.output.rfind('\n') != Some(self.output.len()) {
            self.end_line();
            for _ in 0..self.indent * 4 {
                self.output.push(' ');
            }
        }
        self.output.push_str(s);
    }

    fn end_line(&mut self) {
        self.output.push('\n');
    }
}
