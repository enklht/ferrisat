use super::*;

#[derive(Debug)]
pub struct VarData {
    num_vars: usize,
    activity_inc: f32,
    values: Vec<i8>,
    levels: Vec<usize>,
    reasons: Vec<Option<usize>>,
    activities: Vec<f32>,
    saved_polarities: Vec<bool>,
    watched_pos: Vec<Vec<ClauseId>>,
    watched_neg: Vec<Vec<ClauseId>>,
}

impl VarData {
    pub fn new(num_vars: usize) -> Self {
        VarData {
            num_vars,
            activity_inc: 1.,
            values: vec![-1; num_vars],
            levels: vec![0; num_vars],
            reasons: vec![None; num_vars],
            activities: vec![0.; num_vars],
            saved_polarities: vec![true; num_vars],
            watched_pos: vec![Vec::new(); num_vars],
            watched_neg: vec![Vec::new(); num_vars],
        }
    }

    pub fn watched_clause(&mut self, lit: Lit) -> &mut Vec<ClauseId> {
        if lit.val() {
            &mut self.watched_pos[lit.var()]
        } else {
            &mut self.watched_neg[lit.var()]
        }
    }

    pub fn assign(&mut self, lit: Lit, reason: Option<usize>, level: usize) -> Assignment {
        let var = lit.var();
        debug_assert!(self.values[var] == -1);

        self.values[var] = if lit.val() { 1 } else { 0 };
        self.levels[var] = level;
        self.reasons[var] = reason;

        self.saved_polarities[var] = lit.val();

        Assignment {
            var,
            val: lit.val(),
            reason,
        }
    }

    pub fn register(&mut self, clause: &Vec<Lit>, cid: usize) {
        debug_assert!(clause.len() >= 2);
        for lit in clause {
            self.activities[lit.var()] += 1.;
        }
        self.watched_clause(clause[0]).push(cid);
        self.watched_clause(clause[1]).push(cid);
    }

    pub fn unassign(&mut self, var: usize) {
        self.values[var] = -1;
    }

    pub fn bump_activity(&mut self, var: usize) {
        self.activities[var] += self.activity_inc;

        if self.activities[var] > RESCALE_THRESHOLD {
            self.activity_inc /= RESCALE_THRESHOLD;
            for a in &mut self.activities {
                *a /= RESCALE_THRESHOLD;
            }
        }
    }

    pub fn decay_activities(&mut self) {
        self.activity_inc /= VAR_DECAY;
    }

    pub fn pick_branch_lit(&self) -> Option<Lit> {
        let var = (0..self.num_vars)
            .filter(|&v| self.values[v] == -1)
            .max_by(|&u, &v| {
                self.activities[u]
                    .partial_cmp(&self.activities[v])
                    .unwrap_or(std::cmp::Ordering::Equal)
            })?;

        Some(Lit::new(var, self.saved_polarities[var]))
    }

    pub fn assigned_val_of(&self, lit: Lit) -> Option<bool> {
        let a = self.values[lit.var()];
        if a < 0 {
            None
        } else {
            Some((a == 1) == lit.val())
        }
    }

    pub fn level_of(&self, var: usize) -> usize {
        debug_assert!(self.values[var] >= 0);
        self.levels[var]
    }

    pub fn reason_of(&self, var: usize) -> &Option<usize> {
        debug_assert!(self.values[var] >= 0);
        &self.reasons[var]
    }
}
