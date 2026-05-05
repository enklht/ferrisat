use super::*;

#[derive(Debug)]
pub struct VarData {
    num_vars: usize,
    activity_inc: f32,
    assignments: Vec<Option<Assignment>>,
    activities: Vec<f32>,
    saved_polarities: Vec<bool>,
    watchers_pos: Vec<Vec<ClauseId>>,
    watchers_neg: Vec<Vec<ClauseId>>,
}

impl VarData {
    pub fn new(num_vars: usize) -> Self {
        VarData {
            num_vars,
            activity_inc: 1.,
            assignments: vec![None; num_vars],
            activities: vec![0.; num_vars],
            saved_polarities: vec![true; num_vars],
            watchers_pos: vec![Vec::new(); num_vars],
            watchers_neg: vec![Vec::new(); num_vars],
        }
    }

    pub fn watching_clauses(&mut self, lit: Lit) -> &mut Vec<ClauseId> {
        if lit.val() {
            &mut self.watchers_pos[lit.var()]
        } else {
            &mut self.watchers_neg[lit.var()]
        }
    }

    pub fn assign(&mut self, lit: Lit, level: usize, reason: Reason) -> Assignment {
        debug_assert!(self.assignments[lit.var()].is_none());

        let var = lit.var();
        let val = lit.val();

        let assignment = Assignment {
            var,
            val,
            level,
            reason,
        };
        self.assignments[var] = Some(assignment.clone());
        self.saved_polarities[var] = val;
        assignment
    }

    pub fn register(&mut self, clause: &Clause, cid: usize) {
        debug_assert!(clause.len() >= 2);
        for lit in clause {
            self.activities[lit.var()] += 1.;
        }
        self.watching_clauses(clause[0]).push(cid);
        self.watching_clauses(clause[1]).push(cid);
    }

    pub fn unassign(&mut self, var: usize) {
        self.assignments[var] = None;
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
            .filter(|&v| self.assignments[v].is_none())
            .max_by(|&u, &v| {
                self.activities[u]
                    .partial_cmp(&self.activities[v])
                    .unwrap_or(std::cmp::Ordering::Equal)
            })?;

        Some(Lit::new(var, self.saved_polarities[var]))
    }

    pub fn assigned_val_of(&self, lit: Lit) -> Option<bool> {
        self.assignments[lit.var()]
            .as_ref()
            .map(|assignment| lit.val() == assignment.val)
    }

    pub fn assignment_of(&self, var: usize) -> &Assignment {
        self.assignments[var].as_ref().unwrap()
    }

    pub fn remap_assignments(&mut self, map: Vec<usize>) {
        for assignment in &mut self.assignments {
            if let Some(assignment) = assignment
                && let Reason::Deduced(old_cid) = &mut assignment.reason
            {
                *old_cid = map[*old_cid];
            }
        }
    }

    pub fn clear_watched_lits(&mut self) {
        self.watchers_pos.fill(vec![]);
        self.watchers_neg.fill(vec![]);
    }
}
