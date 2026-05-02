use super::*;

#[derive(Debug)]
pub struct ClauseData {
    clauses: Vec<Clause>,
    locked: Vec<bool>,
    deleted: Vec<bool>,
    lbds: Vec<u16>,
}

impl ClauseData {
    pub fn new() -> Self {
        ClauseData {
            clauses: Vec::new(),
            locked: Vec::new(),
            deleted: Vec::new(),
            lbds: Vec::new(),
        }
    }

    pub fn get_mut(&mut self, cid: usize) -> &mut Clause {
        &mut self.clauses[cid]
    }

    pub fn get(&self, cid: usize) -> &Clause {
        &self.clauses[cid]
    }

    pub fn deleted(&self, cid: usize) -> bool {
        self.deleted[cid]
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn push(&mut self, clause: Clause, locked: bool, lbd: u16) {
        self.clauses.push(clause);
        self.locked.push(locked);
        self.deleted.push(false);
        self.lbds.push(lbd);
    }

    pub fn lock(&mut self, cid: usize) {
        self.locked[cid] = true;
    }

    pub fn unlock(&mut self, cid: usize) {
        self.locked[cid] = false;
    }

    pub fn reduce(&mut self) {
        let mut cids = (0..self.clauses.len()).collect::<Vec<_>>();
        cids.sort_by_key(|&cid| self.lbds[cid]);

        for &cid in cids
            .iter()
            .rev()
            .take(self.clauses.len() / RECIP_REDUCTION_RATIO)
        {
            if self.lbds[cid] <= 3 {
                break;
            }
            if !self.locked[cid] {
                self.deleted[cid] = true;
            }
        }
    }

    pub fn compact(&mut self) {
        let clauses = std::mem::take(&mut self.clauses);
        let locked = std::mem::take(&mut self.locked);
        let deleted = std::mem::take(&mut self.deleted);
        let lbds = std::mem::take(&mut self.lbds);

        for (old_cid, clause) in clauses.into_iter().enumerate() {
            if !deleted[old_cid] {
                self.push(clause, locked[old_cid], lbds[old_cid]);
            }
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Clause> {
        self.clauses.iter()
    }
}
