pub trait Rule<T> {
    fn name(&self) -> &'static str;
    fn apply_top_down(&self) -> bool;
    fn condition(&mut self, obj: &T) -> bool;
    fn action(&mut self, obj: &mut T);
    // @todo prune
    fn begin(&mut self, _obj: &T) {}
    fn end(&mut self, _obj: &T) {}
}

pub trait Traverse<T> {
    fn descend_and_apply(rule: &mut dyn Rule<T>, target: &mut T);
}

fn apply_rule<T>(rule: &mut dyn Rule<T>, target: &mut T) {
    if rule.condition(target) {
        rule.action(target)
    }
}

pub fn deep_apply_rule<T: Clone + Traverse<T>>(rule: &mut dyn Rule<T>, target: &mut T) {
    rule.begin(target);
    if !rule.apply_top_down() {
        T::descend_and_apply(rule, target);
    }
    apply_rule(rule, target);
    if rule.apply_top_down() {
        T::descend_and_apply(rule, target);
    }
    rule.end(target);
}
