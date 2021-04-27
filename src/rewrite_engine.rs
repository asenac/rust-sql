pub trait Rule<T> {
    fn name(&self) -> &'static str;
    fn apply_top_down(&self) -> bool;
    fn condition(&mut self, obj: &T) -> bool;
    fn action(&mut self, obj: &mut T) -> Option<T>;
    // @todo prune
    fn begin(&mut self, _obj: &T) {}
    fn end(&mut self, _obj: &T) {}
}

pub trait Traverse<T> {
    fn descend_and_apply(rule: &mut dyn Rule<T>, target: &mut T);
}

fn apply_rule<T>(rule: &mut dyn Rule<T>, target: &mut T) -> Option<T> {
    if rule.condition(target) {
        rule.action(target)
    } else {
        None
    }
}

pub fn deep_apply_rule<T: Clone + Traverse<T>>(
    rule: &mut dyn Rule<T>,
    target: &mut T,
) -> Option<T> {
    rule.begin(target);
    if !rule.apply_top_down() {
        T::descend_and_apply(rule, target);
    }
    let result = apply_rule(rule, target);
    match result {
        Some(mut c) => {
            if rule.apply_top_down() {
                T::descend_and_apply(rule, &mut c);
            }
            rule.end(&c);
            Some(c)
        }
        None => {
            if rule.apply_top_down() {
                T::descend_and_apply(rule, target);
            }
            rule.end(target);
            None
        }
    }
}
