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
        self.deleted[cid] = true;
    }

    pub fn reduce(&mut self) {
        let mut cids = (self.num_original..self.clauses.len()).collect::<Vec<_>>();
        cids.sort_unstable_by_key(|&cid| self.lbds[cid]);

        let max_deletion = (self.clauses.len() as f32 * REDUCTION_RATIO) as usize;
        let mut num_deletion = 0;
        for &cid in cids.iter().rev() {
            if num_deletion > max_deletion || self.lbds[cid] <= 3 {
                break;
            }

            if !self.deleted[cid] {
                self.deleted[cid] = true;
                num_deletion += 1;
            }
        }
    }

    pub fn compact(&mut self) -> Vec<usize> {
        let clauses = std::mem::take(&mut self.clauses);
        let locked = std::mem::take(&mut self.locked);
        let deleted = std::mem::take(&mut self.deleted);
        let lbds = std::mem::take(&mut self.lbds);

        let mut map = vec![0; clauses.len()];

        let mut new_cid = 0;
        for (old_cid, clause) in clauses.into_iter().enumerate() {
            if locked[old_cid] || !deleted[old_cid] {
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
