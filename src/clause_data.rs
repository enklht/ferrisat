use super::*;

#[derive(Debug)]
pub struct ClauseData {
    num_original: usize,
    clauses: Vec<Clause>,
    locked: Vec<bool>,
    deleted: Vec<bool>,
    lbds: Vec<u16>,
}

impl ClauseData {
    pub fn new() -> Self {
        ClauseData {
            num_original: 0,
            clauses: Vec::new(),
            locked: Vec::new(),
            deleted: Vec::new(),
            lbds: Vec::new(),
        }
    }

    pub fn get(&self, cid: usize) -> &Clause {
        &self.clauses[cid]
    }

    pub fn get_mut(&mut self, cid: usize) -> &mut Clause {
        &mut self.clauses[cid]
    }

    pub fn is_deleted(&self, cid: usize) -> bool {
        self.deleted[cid]
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    pub fn push(&mut self, clause: Clause, locked: bool, lbd: u16) {
        if lbd == 0 {
            self.num_original += 1;
        }

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

    pub fn delete(&mut self, cid: usize) {
        if !self.locked[cid] {
            self.deleted[cid] = true;
        }
    }

    pub fn reduce(&mut self) {
        let mut cids = (self.num_original..self.clauses.len()).collect::<Vec<_>>();
        if cids.is_empty() {
            return;
        }
        let max_deletion = (cids.len() as f32 * REDUCTION_RATIO) as usize;

        let (_, _, candidates) =
            cids.select_nth_unstable_by_key(max_deletion, |&cid| self.lbds[cid]);

        for &cid in candidates.iter() {
            if self.lbds[cid] > 3 && !self.deleted[cid] {
                self.delete(cid);
            }
        }
    }

    pub fn compact(&mut self) -> Vec<usize> {
        self.num_original = 0;
        let clauses = std::mem::take(&mut self.clauses);
        let locked = std::mem::take(&mut self.locked);
        let deleted = std::mem::take(&mut self.deleted);
        let lbds = std::mem::take(&mut self.lbds);

        let mut map = vec![0; clauses.len()];

        let mut new_cid = 0;
        for (old_cid, clause) in clauses.into_iter().enumerate() {
            if !deleted[old_cid] {
                self.push(clause, locked[old_cid], lbds[old_cid]);
                map[old_cid] = new_cid;
                new_cid += 1;
            }
        }

        map
    }

    pub fn iter(&self) -> std::slice::Iter<'_, Clause> {
        self.clauses.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reduction_preserves_locked_reasons() {
        let mut data = ClauseData::new();
        data.push(vec![Lit::pos(0), Lit::pos(1)], false, 4);
        data.push(vec![Lit::pos(0), Lit::pos(1)], false, 5);
        data.push(vec![Lit::pos(0), Lit::pos(1)], true, 100);
        data.reduce();
        assert!(!data.is_deleted(2));
    }

    #[test]
    fn compacted_learned_clauses_remain_eligible_for_reduction() {
        let mut data = ClauseData::new();
        for lbd in [0, 0, 4, 5, 100] {
            data.push(vec![Lit::pos(0), Lit::pos(1)], false, lbd);
        }
        for _ in 0..2 {
            data.compact();
        }
        data.reduce();
        assert!(!data.is_deleted(0));
        assert!(!data.is_deleted(1));
        assert!(data.is_deleted(4));
    }

    #[test]
    fn compaction_updates_the_boundary_after_original_clause_deletion() {
        let mut data = ClauseData::new();
        for lbd in [0, 0, 4, 5, 100] {
            data.push(vec![Lit::pos(0), Lit::pos(1)], false, lbd);
        }
        data.delete(0);
        let map = data.compact();
        data.reduce();
        assert!(!data.is_deleted(map[1]));
        assert!(data.is_deleted(map[4]));
    }
}
