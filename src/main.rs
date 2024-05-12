// Brute-force implementation of [Polyamorous Scheduling](https://arxiv.org/pdf/2403.00465) task
// (c) ProgramCrafter, 2024

use std::{collections::BTreeMap, num::NonZeroUsize, thread::scope, time::Instant};
use rand::prelude::*;


trait SelfInspect : Clone {
    fn self_inspect(self, mut f: impl FnMut(Self)) -> Self {
        f(self.clone());
        self
    }
}
impl<T: Clone> SelfInspect for T {}


type Nzu = NonZeroUsize;

#[derive(Clone, Copy, Debug)] struct Edge {lhs: usize, rhs: usize, weight: usize}
impl Edge {
    fn insert_left_handle<const N: usize>(self, i: usize, dest: &mut [BTreeMap<usize, usize>; N], max_degree: &mut usize) {
        dest[self.lhs].insert(self.rhs, i);
        if dest[self.lhs].len() > *max_degree {
            *max_degree = dest[self.lhs].len();
        }
    }
    fn insert_right_handle<const N: usize>(self, i: usize, dest: &mut [BTreeMap<usize, usize>; N], max_degree: &mut usize) {
        dest[self.rhs].insert(self.lhs, i);
        if dest[self.rhs].len() > *max_degree {
            *max_degree = dest[self.rhs].len();
        }
    }
}


#[derive(Debug)]
#[allow(dead_code)]
struct InputCfg<const VERTS: usize> {
    adjacent: [BTreeMap<usize, usize>; VERTS],
    max_degree: usize,
    edges: Vec<Edge>,
}
impl<const N: usize> InputCfg<N> {
    fn from_edges(e: Vec<Edge>) -> Self {
        let mut adjacent = core::array::from_fn(|_| BTreeMap::new());
        let mut max_degree = 0;
        
        for (i, edge) in e.iter().enumerate() {
            edge.insert_left_handle(i, &mut adjacent, &mut max_degree);
            edge.insert_right_handle(i, &mut adjacent, &mut max_degree);
        }
        
        Self {adjacent, max_degree, edges: e}
    }
}


#[derive(Clone)]
struct CertificatePoly<'a, const VERTS: usize> {
    matching: Vec<[Nzu; VERTS]>,
    cfg: &'a InputCfg<VERTS>,
    edge_use: Vec<Vec<usize>>,
    unused_edges: usize,
}
impl<'cert, const N: usize> CertificatePoly<'cert, N> {
    fn empty_for(cfg: &'cert InputCfg<N>) -> Self {
        let m = cfg.edges.len();
        Self {matching: Vec::new(), cfg, edge_use: vec![vec![]; m], unused_edges: m}
    }
    fn start_new_day<'a>(&'a mut self) -> CertificateDayGuard<'a, 'cert, N> {
        CertificateDayGuard {certificate: self, meetings: [None; N], unmet_people: N, edge_use: vec![], meeting_id: 0}
    }
    #[cfg(debug_assertions)]
    fn evaluate(&self) -> usize {
        assert_eq!(self.unused_edges, 0);
        
        let d = self.matching.len();
        
        self.edge_use
            .iter()
            .map(|v| {
                let it: Vec<_> = (0..v.len()).map(|j| {
                        if j == 0 {d - v.last().unwrap() + v[0]} else {v[j] - v[j-1]}
                    })
                    .collect();
                let m = *it.iter().max().unwrap();
                (it, m)
            })
            .self_inspect(|f| {println!("{:?}", f.collect::<Vec<_>>());})
            .enumerate()
            .map(|(i, v)| self.cfg.edges[i].weight * v.1)
            .self_inspect(|f| {println!("{:?}", f.collect::<Vec<_>>());})
            .max().unwrap()
    }
    #[cfg(not(debug_assertions))]
    fn evaluate(&self) -> usize {self.evaluate_raw()}
    fn evaluate_raw(&self) -> usize {
        let d = self.matching.len();
        
        self.edge_use
            .iter()
            .map(|v| {
                (0..v.len()).map(|j| {
                        if j == 0 {d - v.last().unwrap() + v[0]} else {v[j] - v[j-1]}
                    })
                    .max().unwrap()
            })
            .enumerate()
            .map(|(i, v)| self.cfg.edges[i].weight * v)
            .max().unwrap()
    }
    fn print(&self) {
        assert_eq!(self.unused_edges, 0);
        let score = self.evaluate();
        println!("Score: {score}");
        for (i, row) in self.matching.iter().enumerate() {
            println!("{:3} | {}", i+1, row.map(|v| v.to_string()).join(" "));
        }
    }
}

struct CertificateDayGuard<'a, 'cert: 'a, const N: usize> {
    certificate: &'a mut CertificatePoly<'cert, N>,
    meetings: [Option<Nzu>; N],
    unmet_people: usize,
    edge_use: Vec<usize>,
    meeting_id: usize,
}
impl<'a, 'cert: 'a, const N: usize> CertificateDayGuard<'a, 'cert, N> {
    fn select_unmet(&self, rng: &mut impl Rng) -> usize {
        assert_ne!(self.unmet_people, 0);
        if self.unmet_people > 4 {
            loop {
                let x = rng.gen_range(0..N);
                if self.meetings[x].is_none() {break x}
            }
        } else {
            self.meetings.iter()
                .enumerate()
                .find(|p| p.1.is_none())
                .unwrap().0
        }
    }
    fn establish_meeting(&mut self, people: &[usize]) -> bool {
        for a in people {
            if self.meetings[*a].is_some() {return false;}
        }
        let mut used = vec![];
        for (i, a) in people.iter().enumerate() {
            for j in 0..i {
                let tree = &self.certificate.cfg.adjacent[people[j]];
                let Some(edge_id) = tree.get(a) else {return false};
                used.push(*edge_id);
            }
        }
        
        self.unmet_people -= people.len();
        self.edge_use.append(&mut used);
        self.meeting_id += 1;
        for a in people {
            self.meetings[*a] = Nzu::new(self.meeting_id);
        }
        
        true
    }
    fn apply(self) {
        let CertificateDayGuard {certificate, meetings, unmet_people, mut edge_use, ..} = self;
        assert_eq!(unmet_people, 0);
        let day = certificate.matching.len();
        for e in edge_use.drain(..) {
            if certificate.edge_use[e].is_empty() {
                certificate.unused_edges -= 1;
            }
            certificate.edge_use[e].push(day);
        }
        certificate.matching.push(meetings.map(|x| x.unwrap()));
    }
}

fn generate_input_bipartite(rng: &mut impl Rng) -> InputCfg<64> {
    let mut edges = Vec::new();
    for i in 0..32_usize {
        let j_mask: u32 = rng.gen();
        for j in 0..32_usize {
            if (j_mask >> j) & 1 == 1 {
                edges.push(Edge {lhs: i, rhs: j + 32, weight: rng.gen_range(1..=20)});
            }
        }
    }
    InputCfg::from_edges(edges)
}

fn poly_random_solve<'a>(rng: &mut impl Rng, cfg: &'a InputCfg<64>) -> CertificatePoly<'a, 64> {
    let mut cert = CertificatePoly::empty_for(cfg);
    
    while cert.unused_edges > 0 {
        let mut day = cert.start_new_day();
        while day.unmet_people > 0 {
            let mut group: Vec<usize> = Vec::with_capacity(4);
            group.push(day.select_unmet(rng));
            
            for _attempt in 0..(rng.gen_range(0..128_usize)) {
                let join = rng.gen_range(0..64_usize);
                if group.contains(&join) || day.meetings[join].is_some() {continue;}
                if group.iter().all(|i| cfg.adjacent[join].contains_key(i)) {
                    group.push(join);
                }
            }
            
            day.establish_meeting(&group);
        }
        
        if rng.gen_range(0..4) == 0 || day.edge_use.len() > 6 {
            day.apply();
        }
    }
    
    cert
}



fn main() {
    let mut rng = rand_chacha::ChaCha20Rng::seed_from_u64(0x11052024);
    
    let cfg = generate_input_bipartite(&mut rng);
    let cert = poly_random_solve(&mut rng, &cfg);
    let score = cert.evaluate_raw();
    cert.print();
    
    let results = scope(|spawner| {
        let thread_search = || {
            let mut rng = thread_rng();
            
            let start = Instant::now();
            let mut p16 = None;
            
            let (best_score, best_cert) = (0..256).map(|i| {
                let cert = poly_random_solve(&mut rng, &cfg);
                let e = (cert.evaluate_raw(), cert);
                if i == 16 {p16 = Some(Instant::now());}
                e
            }).min_by_key(|(i, _)| *i).unwrap();
            
            (best_score, best_cert, p16.unwrap().duration_since(start))
        };
        
        let threads: [_; 6] = core::array::from_fn(|_| spawner.spawn(thread_search));
        threads.map(|t| t.join().expect("multithreading failure"))
    });
    let (best_score, best_cert, time_16) = results.iter().min_by_key(|(i, _, _)| *i).unwrap();
    println!("Time to get 16 solutions: {time_16:?}");
    
    best_cert.print();
    
    println!("Improvement: {score} -> {best_score}, -{:.3}% from {} iterations",
        (1.0 - *best_score as f32 / score as f32) * 100.0, 256 * 6);
}
