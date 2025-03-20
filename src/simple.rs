use std::{collections::VecDeque, ops::{Index, IndexMut}};

struct StateArray([bool; 5*5*W]);

const L: usize = 6;
const W: usize = 1<<L;
const B: usize = W*5*5;
const NR: usize = 24;

impl Index<(usize, usize, usize)> for StateArray {
    type Output := bool;

    fn index(&self, index: (usize, usize, usize)) -> &Self::Output {
        let (x,y,z) = index;
        &self.0[W*(5*y + x) + z]
    }
}

impl IndexMut<(usize, usize, usize)> for StateArray {
    fn index_mut(&mut self, index: (usize, usize, usize)) -> &mut Self::Output {
        let (x,y, z) = index;
        &mut self.0[W*(5*y + x) + z]
    }
}

fn theta(a: &mut StateArray) {
    let mut c = [[false; W]; 5];
    for x in 0..5 {
        for z in 0..W {
            c[x][z] = a[(x,0,z)] ^ a[(x,1,z)] ^ a[(x,2,z)] ^ a[(x,3,z)] ^ a[(x,4,z)];
        }
    }
    let mut d = [[false; W]; 5];
    for x in 0..5 {
        for z in 0..W {
            let x_ = ((x as isize - 1) % 5) as usize;
            let z_ = ((z as isize - 1) % W as isize) as usize;
            d[x][z] = c[x_][z] ^ c[(x+1)%5][z_]
        }
    }
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..W {
                a[(x,y,z)] = a[(x,y,z)] ^ d[x][z];
            }
        }
    }
}

fn rho_offset(t: usize) -> isize {
    ((t + 1) * (t + 2) / 2) as isize
}
fn rho(a: &mut StateArray) {
    let (mut x, mut y) = (1,0);
    for t in 0..24 {
        for z in 0..W {
            let z2 = ((z as isize - rho_offset(t)) % W as isize) as usize;
            a[(x,y,z)] = a[(x,y,z2)]
        }
        (x,y) = (y, (2*x + 3*y) % 5);
    }
}

fn pi(a: &mut StateArray) {
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..W {
                let x2 = (x + 3*y) % 5;
                let y2 = x;
                a[(x,y,z)] = a[(x2,y2,z)];
            }
        }
    }
}

fn chi(a: &mut StateArray) {
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..W {
                let x1 = (x+1)%5;
                let x2 = (x+2)%5;
                a[(x,y,z)] = a[(x,y,z)] ^ ((a[(x1,y,z)] ^ true) & a[(x2,y,z)]);
            }
        }
    }
}

fn iota_rc(t: usize) -> bool {
    let t = t % 255;
    if t == 0 { return true; }
    let mut r = VecDeque::from([1,0,0,0, 0,0,0,0]);
    for _ in 1..=t {
        r.push_front(0);
        r[0] = r[0] ^ r[8];
        r[4] = r[4] ^ r[8];
        r[5] = r[5] ^ r[8];
        r[6] = r[6] ^ r[8];
        r.pop_back();
    }
    return r[0] == 1;
}
fn iota(ir: usize, a: &mut StateArray) {
    let mut rc = [false; W];
    for j in 0..=L {
        rc[(1<<j) - 1] = iota_rc(j + 7*ir);
    }
    for z in 0..W {
        a[(0,0,z)] = a[(0,0,z)] ^ rc[z];
    }
}

fn round(a: &mut StateArray, ir: usize) {
    theta(a);
    rho(a);
    pi(a);
    chi(a);
    iota(ir, a);
}

fn keccak_p(s: &mut [bool; B]) {
    let mut a = StateArray(*s);
    for ir in 0..24 {
        round(&mut a, ir);
    }
    *s = a.0;
}

fn pad10_1(x: usize, m: usize) -> Vec<bool> {
    let j = (- (m as isize) - 2) % (x as isize);
    let mut res = vec![true];
    for _ in 0..j {
        res.push(false);
    }
    res.push(true);
    res
}

fn sponge(r: usize, bs: impl IntoIterator<Item=bool>, d: usize) -> Vec<bool> {
    let bs: Vec<bool> = bs.into_iter().collect();
    let m = bs.len();
    let p = [bs, pad10_1(r,m)].concat();
    let chunks = p.chunks(r);
    let mut s = [false; B];
    for chunk in chunks {
        for i in 0..B {
            s[i] = s[i] ^ chunk[i];
        }
        keccak_p(&mut s);
    }
    let mut z = vec![];
    return loop {
        z.extend(s.iter().take(r));
        if d <= z.len() {
            z.truncate(d);
            break z
        } else {
            keccak_p(&mut s);
        }
    }
}

pub fn sha3_224(bs: Vec<bool>) -> Vec<bool> { sponge(B - 2*224, bs, 224) }
pub fn sha3_256(bs: Vec<bool>) -> Vec<bool> { sponge(B - 2*256, bs, 256) }
pub fn sha3_384(bs: Vec<bool>) -> Vec<bool> { sponge(B - 2*384, bs, 384) }
pub fn sha3_512(bs: Vec<bool>) -> Vec<bool> { sponge(B - 2*512, bs, 512) }

pub fn shake128(bs: Vec<bool>, d: usize) -> Vec<bool> { sponge(B - 2*128, bs.into_iter().chain([true;4]), d) }
pub fn shake256(bs: Vec<bool>, d: usize) -> Vec<bool> { sponge(B - 2*256, bs.into_iter().chain([true;4]), d) }
