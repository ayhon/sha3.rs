#![allow(dead_code)]

const L:  usize = 6;
const W:  usize = 1<<L;
const B:  usize = 5*5*W;
const NR: usize = 24;

fn add_to_vec<'a, A: Copy>(dst: &'a mut Vec<A>, src: &'a [A], n: usize) {
    let mut i= 0;
    while i < n {
        dst.push(src[i]);
        i += 1;
    }
}

fn binxor(a: bool, b: bool) -> bool {
    (a && !b) || (b && !a)
}

fn rem_euclid_i8(a: i8, b: i8) -> i8 {
    let a = a % b;
    if a < 0 { if b < 0 { a - b } else { a + b } } else { a }
}
fn rem_euclid_isize(a: isize, b: isize) -> isize {
    let a = a % b;
    if a < 0 { if b < 0 { a - b } else { a + b } } else { a }
}


struct StateArray([bool; B]);

impl Default for StateArray {
    fn default() -> Self {
        Self([false; B])
    }
}

impl Clone for StateArray {
    fn clone(&self) -> Self {
        Self(self.0)
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
        let x1 = rem_euclid_i8(x as i8 - 1,5) as u8;
        let x2 = (x + 1) % 5;
        let z2 = rem_euclid_isize(z as isize - 1, W as isize) as usize;
        binxor(theta_c(a,x1,z), theta_c(a, x2, z2))
    }
    let mut res = StateArray::default();
    let mut x = 0;
    while x < 5 {
        #[inline] fn theta_apply_a_inner(res: &mut StateArray, a: &StateArray, x: u8){
            
            let mut y = 0;
            while y < 5 {
                #[inline] fn theta_apply_a_inner2(res: &mut StateArray, a: &StateArray, x: u8, y: u8){
                    let mut z = 0;
                    while z < W {
                        *res.index_mut((x,y,z)) = binxor(*a.index((x,y,z)), theta_d(a, x, z));
                        z += 1;
                    }
                } theta_apply_a_inner2(res, &a, x, y);
                y += 1;
            }
        } theta_apply_a_inner(&mut res, &a, x);
        x += 1;
    }
    return res;
}

fn rho_offset(t: usize) -> isize {
    ((t + 1) * (t + 2) / 2) as isize
}
fn rho(a: &StateArray) -> StateArray {
    let (mut x, mut y) = (1,0);
    let mut res = a.clone();
    let mut t = 0;
    while t < 24 {
        #[inline]
        fn rho_inner(res: &mut StateArray, a: &StateArray, t: usize, x: u8, y: u8) {
            let mut z = 0;
            while z < W {
                let z2 = rem_euclid_isize(z as isize - rho_offset(t), W as isize) as usize;
                *res.index_mut((x,y,z)) = *a.index((x,y,z2));
                 z  += 1;
            }
        }
        rho_inner(&mut res, a, t, x, y);
        (x,y) = (y, (2*x + 3*y) % 5);
        t  += 1;
    }
    return res
}

fn pi(a: &StateArray) -> StateArray {
    let mut res = a.clone();
    let mut x = 0;
    while x < 5 {
        #[inline]
        fn pi_inner(res: &mut StateArray, a:&StateArray, x: u8){
            let mut y = 0;
            while y < 5 {
                #[inline]
                fn pi_inner2(res: &mut StateArray, a:&StateArray, x: u8, y: u8){
                    let mut z = 0;
                    while z < W {
                        let x2 = (x + 3*y) % 5;
                        let y2 = x;
                        *res.index_mut((x,y,z)) = *a.index((x2,y2,z));
                        z += 1;
                    }
                }
                pi_inner2(res, a, x, y);
                y += 1;
            }
        }
        pi_inner(&mut res, a, x);
        x += 1;
    }
    return res;
}

fn chi(a: &StateArray) -> StateArray {
    let mut res = a.clone();
    let mut x = 0;
    while x < 5 {
        #[inline]
        fn chi_inner(res: &mut StateArray, a: &StateArray, x: u8){
            let mut y = 0;
            while y < 5 {
                #[inline]
                fn chi_inner2(res: &mut StateArray, a: &StateArray, x: u8, y: u8){
                    let mut z = 0;
                    while z < W {
                        let x1 = (x+1)%5;
                        let x2 = (x+2)%5;
                        *res.index_mut((x,y,z)) = binxor(*a.index((x,y,z)),
                            binxor(*a.index((x1,y,z)), true) && *a.index((x2,y,z)));
                        z += 1;
                    }
                }
                chi_inner2(res, a, x, y);
                y += 1;
            }
        }
        chi_inner(&mut res, a, x);
        x += 1;
    }
    return res;
}

// const IOTA_RC_POINTS: [u64; 4] = [0x018d17fe09e5ab0e, 0x46cdf47b76a752a4, 0xc59cc786e87afbb0, 0xacad2037c9c0258e];
const IOTA_RC_POINTS: [bool; 255] = [true, false, false, false, false, false, false, false, true, false, true, true, false, false, false, true, true, true,
 true, false, true, false, false, false, false, true, true, true, true, true, true, true, true, false, false, true,
 false, false, false, false, true, false, true, false, false, true, true, true, true, true, false, true, false, true,
 false, true, false, true, true, true, false, false, false, false, false, true, true, false, false, false, true, false,
 true, false, true, true, false, false, true, true, false, false, true, false, true, true, true, true, true, true,
 false, true, true, true, true, false, false, true, true, false, true, true, true, false, true, true, true, false,
 false, true, false, true, false, true, false, false, true, false, true, false, false, false, true, false, false, true,
 false, true, true, false, true, false, false, false, true, true, false, false, true, true, true, false, false, true,
 true, true, true, false, false, false, true, true, false, true, true, false, false, false, false, true, false, false,
 false, true, false, true, true, true, false, true, false, true, true, true, true, false, true, true, false, true, true,
 true, true, true, false, false, false, false, true, true, false, true, false, false, true, true, false, true, false,
 true, true, false, true, true, false, true, false, true, false, false, false, false, false, true, false, false, true,
 true, true, false, true, true, false, false, true, false, false, true, false, false, true, true, false, false, false,
 false, false, false, true, true, true, false, true, false, false, true, false, false, false, true, true, true, false,
 false, false];

fn iota_rc_point(t: usize) -> bool {
    let t = t % 255;
    // ((IOTA_RC_POINTS[t / 64] >> (t % 4)) & 1) == 1
    IOTA_RC_POINTS[t]
}

fn iota_rc_init(ir: usize, rc: &mut [bool; W]) {
    let mut j = 0;
    while j < L {
        rc[(1<<j) - 1] = iota_rc_point(j + 7*ir);
        j += 1;
    }
}

fn iota_a(res: &mut StateArray, a: &StateArray, rc: &[bool; W]){
    let mut z = 0;
    while z < W {
        *res.index_mut((0,0,z)) = binxor(*a.index((0,0,z)),rc[z]);
        z += 1;
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
    let mut ir = 0;
    while ir < 24 {
        round(&mut a, ir);
        ir += 1;
    }
    *s = a.0;
}

fn pad10_1(x: usize, m: usize) -> Vec<bool> {
    let j = rem_euclid_isize(- (m as isize) - 2,x as isize);
    let mut res = Vec::new();
    res.push(true);
    let mut i = 0;
    while i < j {
        res.push(false);
        i += 1;
    }
    res.push(true);
    return res;
}

fn xor_long(s: &mut [bool], other: &[bool]){
    // TODO: Remove once fixed in Aeneas
    let n = if s.len() < other.len() { s.len() } else { other.len() };
    let mut i = 0;
    while i < n {
        s[i] = binxor(s[i], other[i]);
        i += 1;
    }
}

fn sponge_absorb(bs: &Vec<bool>, r: usize, s: &mut [bool; B]) {
    let n = bs.len() / r;
    let mut i = 0;
    while i < n {
        let chunk = &bs[r*i..r*(i+1)];
        xor_long(s, chunk);
        keccak_p(s);
        i += 1;
    }
}

fn sponge_squeze(d: usize, r: usize, z: &mut Vec<bool>, s: &mut [bool; B]) {
    loop {
        // z.extend(s.iter().take(r));
        add_to_vec::<bool>(z, s, r);
        if d <= z.len() {
            *z = z[0..d].to_vec();
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
    *bs = Vec::new();
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


