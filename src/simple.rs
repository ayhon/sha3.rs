#![allow(dead_code)]

use std::collections::VecDeque;

const L: usize = 6;
const W: usize = 1<<L;
const B: usize = 5*5*W;
const NR: usize = 24;

fn add_to_vec<'a, A: Copy>(dst: &'a mut Vec<A>, src: &'a [A], n: usize) {
    let mut iter = 0..n;
    while let Some(i) = iter.next() {
        dst.push(src[i]);
    }
}

fn binxor(a: bool, b: bool) -> bool {
    (a && !b) || (b && !a)
}


#[derive(Clone)]
struct StateArray([bool; B]);

impl Default for StateArray {
    fn default() -> Self {
        Self([false; B])
    }
}

impl StateArray {
    fn index(&self, index: (u8, u8, usize)) -> &bool {
        let (x,y,z) = index;
        &self.0[W*(5*(y as usize) + x as usize) + z]
    }

    fn index_mut(&mut self, index: (u8, u8, usize)) -> &mut bool {
        let (x,y,z) = index;
        &mut self.0[W*(5*(y as usize) + x as usize) + z]
    }
}

fn theta(a: &StateArray) -> StateArray {
    fn theta_c(a: &StateArray, x: u8, z: usize) -> bool {
        binxor(
            *a.index((x,0,z)),
            binxor(
                *a.index((x,1,z)),
                binxor(
                    *a.index((x,2,z)),
                    binxor(
                        *a.index((x,3,z)),
                        *a.index((x,4,z)),
                    )
                )
            )
        )
    }
    fn theta_d(a: &StateArray, x: u8, z: usize) -> bool {
        let x1 = (x as i8 - 1).rem_euclid(5) as u8;
        let x2 = (x       + 1).rem_euclid(5);
        let z2 = (z as isize - 1).rem_euclid(W as isize) as usize;
        binxor(theta_c(a,x1,z), theta_c(a, x2, z2))
    }
    let mut res = StateArray::default();
    let mut iter = 0..5;
    while let Some(x) =  iter.next() {
        #[inline] fn theta_apply_a_inner(res: &mut StateArray, a: &StateArray, x: u8){
            let mut iter = 0..5;
            while let Some(y) = iter.next() {
                #[inline] fn theta_apply_a_inner2(res: &mut StateArray, a: &StateArray, x: u8, y: u8){
                    let mut iter = 0..W;
                    while let Some(z) =  iter.next() {
                        *res.index_mut((x,y,z)) = binxor(*a.index((x,y,z)), theta_d(a, x, z));
                    }
                } theta_apply_a_inner2(res, &a, x, y);
            }
        } theta_apply_a_inner(&mut res, &a, x);
    }
    return res;
}

fn rho_offset(t: usize) -> isize {
    ((t + 1) * (t + 2) / 2) as isize
}
fn rho(a: &StateArray) -> StateArray {
    let (mut x, mut y) = (1,0);
    let mut res = a.clone();
    let mut iter = 0..24;
    while let Some( t ) = iter.next() {
        #[inline]
        fn rho_inner(res: &mut StateArray, a: &StateArray, t: usize, x: u8, y: u8) {
            let mut iter = 0..W;
            while let Some( z ) = iter.next() {
                let z2 = (z as isize - rho_offset(t)).rem_euclid(W as isize) as usize;
                *res.index_mut((x,y,z)) = *a.index((x,y,z2));
            }
        }
        rho_inner(&mut res, a, t, x, y);
        (x,y) = (y, (2*x + 3*y) % 5);
    }
    return res
}

fn pi(a: &StateArray) -> StateArray {
    let mut res = a.clone();
    let mut iter = 0..5;
    while let Some( x ) = iter.next() {
        #[inline]
        fn pi_inner(res: &mut StateArray, a:&StateArray, x: u8){
            let mut iter = 0..5;
            while let Some( y ) = iter.next() {
                #[inline]
                fn pi_inner2(res: &mut StateArray, a:&StateArray, x: u8, y: u8){
                    let mut iter = 0..W;
                    while let Some( z ) = iter.next() {
                        let x2 = (x + 3*y) % 5;
                        let y2 = x;
                        *res.index_mut((x,y,z)) = *a.index((x2,y2,z));
                    }
                }
                pi_inner2(res, a, x, y);
            }
        }
        pi_inner(&mut res, a, x);
    }
    return res;
}

fn chi(a: &StateArray) -> StateArray {
    let mut res = a.clone();
    let mut iter = 0..5;
    while let Some( x ) = iter.next() {
        #[inline]
        fn chi_inner(res: &mut StateArray, a: &StateArray, x: u8){
            let mut iter = 0..5;
            while let Some( y ) = iter.next() {
                #[inline]
                fn chi_inner2(res: &mut StateArray, a: &StateArray, x: u8, y: u8){
                    let mut iter = 0..W;
                    while let Some( z ) = iter.next() {
                        let x1 = (x+1)%5;
                        let x2 = (x+2)%5;
                        *res.index_mut((x,y,z)) = binxor(*a.index((x,y,z)),
                            binxor(*a.index((x1,y,z)), true) & a.index((x2,y,z)));
                    }
                }
                chi_inner2(res, a, x, y);
            }
        }
        chi_inner(&mut res, a, x);
    }
    return res;
}

fn iota_rc_loop(t: usize, r: &mut VecDeque<bool>){
    for _ in 1..=t {
        r.push_front(false);
        r[0] = binxor(r[0], r[8]);
        r[4] = binxor(r[4], r[8]);
        r[5] = binxor(r[5], r[8]);
        r[6] = binxor(r[6], r[8]);
        r.pop_back();
    }
}

fn iota_rc_point(t: usize) -> bool {
    let t = t % 255;
    if t == 0 { return true; }
    let mut r = VecDeque::from([true, false, false, false, false, false, false, false]);
    iota_rc_loop(t, &mut r);
    return r[0];
}

fn iota_rc_init(ir: usize, rc: &mut [bool; W]) {
    let mut iter = 0..=L;
    while let Some( j ) = iter.next() {
        rc[(1<<j) - 1] = iota_rc_point(j + 7*ir);
    }
}

fn iota_a(res: &mut StateArray, a: &StateArray, rc: &[bool; W]){
    let mut iter = 0..W;
    while let Some( z ) = iter.next() {
        *res.index_mut((0,0,z)) = binxor(*a.index((0,0,z)),rc[z]);
    }
}

fn iota(ir: usize, a: &StateArray) -> StateArray {
    let mut rc = [false; W];
    iota_rc_init(ir, &mut rc);
    let mut res = a.clone();
    iota_a(&mut res, a, &rc);
    return res;
}

fn round(a: &mut StateArray, ir: usize) {
    *a = theta(a);
    *a = rho(a);
    *a = pi(a);
    *a = chi(a);
    *a = iota(ir, a);
}

fn keccak_p(s: &mut [bool; B]) {
    let mut a = StateArray(*s);
    for ir in 0..24 {
        round(&mut a, ir);
    }
    *s = a.0;
}

fn pad10_1(x: usize, m: usize) -> Vec<bool> {
    let j = ((x as isize - 1) + (m as isize) - 2).rem_euclid(x as isize);
    let mut res = vec![true];
    let mut iter = 0..j;
    while let Some( _ ) = iter.next() {
        res.push(false);
    }
    res.push(true);
    return res;
}

fn xor_long(s: &mut [bool], other: &[bool]){
    // TODO: Remove once fixed in Aeneas
    let n = if s.len() < other.len() { s.len() } else { other.len() };
    let mut iter = 0..n;
    while let Some( i ) = iter.next() {
        s[i] = binxor(s[i], other[i]);
    }
}

fn sponge_absorb(bs: &Vec<bool>, r: usize, s: &mut [bool; B]) {
    let n = bs.len() / r;
    let mut iter = 0..n;
    while let Some( i ) = iter.next() {
        let chunk = &bs[r*i..r*(i+1)];
        xor_long(s, chunk);
        keccak_p(s)
    }
}

fn sponge_squeze(d: usize, r: usize, z: &mut Vec<bool>, s: &mut [bool; B]) {
    loop {
        // z.extend(s.iter().take(r));
        add_to_vec::<bool>(z, s, r);
        if d <= z.len() {
            z.truncate(d);
            break
        } else {
            keccak_p(s);
        }
    }
}

fn my_extend(bs: &mut Vec<bool>, other: &Vec<bool>){
    add_to_vec::<bool>(bs, other, other.len());
}

fn sponge(r: usize, bs: &mut Vec<bool>, d: usize) {
    let m = bs.len();
    my_extend(bs, &pad10_1(r,m));
    let mut s = [false; B];
    sponge_absorb(bs, r, &mut s);
    bs.clear();
    sponge_squeze(d, r, bs, &mut s);
}

const SHA3_SUFFIX: [bool; 2] = [false, true];
pub fn sha3_224(bs: &mut Vec<bool>)           { my_extend(bs, &SHA3_SUFFIX.to_vec());  sponge(B - 2*224, bs, 224) }
pub fn sha3_256(bs: &mut Vec<bool>)           { my_extend(bs, &SHA3_SUFFIX.to_vec());  sponge(B - 2*256, bs, 256) }
pub fn sha3_384(bs: &mut Vec<bool>)           { my_extend(bs, &SHA3_SUFFIX.to_vec());  sponge(B - 2*384, bs, 384) }
pub fn sha3_512(bs: &mut Vec<bool>)           { my_extend(bs, &SHA3_SUFFIX.to_vec());  sponge(B - 2*512, bs, 512) }

const SHAKE_SUFFIX: [bool; 4] = [true; 4];
pub fn shake128(bs: &mut Vec<bool>, d: usize) { my_extend(bs, &SHAKE_SUFFIX.to_vec()); sponge(B - 2*128, bs,   d) }
pub fn shake256(bs: &mut Vec<bool>, d: usize) { my_extend(bs, &SHAKE_SUFFIX.to_vec()); sponge(B - 2*256, bs,   d) }


