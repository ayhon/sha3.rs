-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [simple]
import Aeneas
open Aeneas.Std Result Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace simple

/- [simple::L]
   Source: 'src/simple.rs', lines 3:0-3:20 -/
@[global_simps] def L_body : Result Usize := ok 6#usize
@[global_simps, irreducible] def L : Usize := eval_global L_body

/- [simple::W]
   Source: 'src/simple.rs', lines 4:0-4:23 -/
@[global_simps] def W_body : Result Usize := 1#usize <<< L
@[global_simps, irreducible] def W : Usize := eval_global W_body (by native_decide)

/- [simple::B]
   Source: 'src/simple.rs', lines 5:0-5:24 -/
@[global_simps]
def B_body : Result Usize := do
                             let i ← 5#usize * 5#usize
                             i * W
@[global_simps, irreducible] def B : Usize := eval_global B_body (by native_decide)

/- [simple::NR]
   Source: 'src/simple.rs', lines 6:0-6:21 -/
@[global_simps] def NR_body : Result Usize := ok 24#usize
@[global_simps, irreducible] def NR : Usize := eval_global NR_body

/- [simple::add_to_vec]: loop 0:
   Source: 'src/simple.rs', lines 1:0-14:5 -/
def add_to_vec_loop
  {A : Type} (coremarkerCopyInst : core.marker.Copy A) (dst : Slice A)
  (o : Usize) (src : Slice A) (n : Usize) (i : Usize) :
  Result (Usize × (Slice A))
  :=
  if i < n
  then
    do
    let i1 ← o + i
    let i2 := Slice.len dst
    if i1 < i2
    then
      do
      let t ← Slice.index_usize src i
      let dst1 ← Slice.update dst i1 t
      let i3 ← i + 1#usize
      add_to_vec_loop coremarkerCopyInst dst1 o src n i3
    else ok (i, dst)
  else ok (i, dst)
partial_fixpoint

/- [simple::add_to_vec]:
   Source: 'src/simple.rs', lines 9:0-16:1 -/
@[reducible]
def add_to_vec
  {A : Type} (coremarkerCopyInst : core.marker.Copy A) (dst : Slice A)
  (o : Usize) (src : Slice A) (n : Usize) :
  Result (Usize × (Slice A))
  :=
  add_to_vec_loop coremarkerCopyInst dst o src n 0#usize

/- [simple::binxor]:
   Source: 'src/simple.rs', lines 18:0-20:1 -/
def binxor (a : Bool) (b : Bool) : Result Bool :=
  if a
  then if b
       then ok (¬ true)
       else ok true
  else if b
       then ok (¬ false)
       else ok false

/- [simple::xor_long_at]: loop 0:
   Source: 'src/simple.rs', lines 26:4-29:5 -/
def xor_long_at_loop
  (s : Slice Bool) (other : Slice Bool) (pos : Usize) (n : Usize)
  (pos1 : Usize) :
  Result (Slice Bool)
  :=
  if pos1 < n
  then
    do
    let b ← Slice.index_usize s pos1
    let i ← pos1 - pos
    let b1 ← Slice.index_usize other i
    let b2 ← binxor b b1
    let s1 ← Slice.update s pos1 b2
    let i1 ← pos1 + 1#usize
    xor_long_at_loop s1 other pos n i1
  else ok s
partial_fixpoint

/- [simple::xor_long_at]:
   Source: 'src/simple.rs', lines 22:0-30:1 -/
def xor_long_at
  (s : Slice Bool) (other : Slice Bool) (pos : Usize) : Result (Slice Bool) :=
  do
  let i := Slice.len s
  let i1 := Slice.len other
  let i2 ← i1 + pos
  let n ← (↑(core.cmp.impls.OrdUsize.min i i2) : Result Usize)
  xor_long_at_loop s other pos n pos

/- [simple::xor_long]:
   Source: 'src/simple.rs', lines 31:0-33:1 -/
def xor_long (s : Slice Bool) (other : Slice Bool) : Result (Slice Bool) :=
  xor_long_at s other 0#usize

/- [simple::StateArray]
   Source: 'src/simple.rs', lines 35:0-35:29 -/
@[reducible] def StateArray := (Array Bool 1600#usize)

/- Trait declaration: [core::default::Default]
   Source: '/rustc/library/core/src/default.rs', lines 107:0-107:24
   Name pattern: core::default::Default -/
structure core.default.Default (Self : Type) where
  default : Result Self

/- [simple::{core::default::Default for simple::StateArray}::default]:
   Source: 'src/simple.rs', lines 38:4-40:5 -/
def DefaultsimpleStateArray.default : Result StateArray :=
  let a := Array.repeat 1600#usize false
  ok a

/- Trait implementation: [simple::{core::default::Default for simple::StateArray}]
   Source: 'src/simple.rs', lines 37:0-41:1 -/
@[reducible]
def core.default.DefaultsimpleStateArray : core.default.Default StateArray := {
  default := DefaultsimpleStateArray.default
}

/- [simple::{core::clone::Clone for simple::StateArray}#1::clone]:
   Source: 'src/simple.rs', lines 44:4-46:5 -/
def ClonesimpleStateArray.clone (self : StateArray) : Result StateArray :=
  ok self

/- Trait implementation: [simple::{core::clone::Clone for simple::StateArray}#1]
   Source: 'src/simple.rs', lines 43:0-47:1 -/
@[reducible]
def core.clone.ClonesimpleStateArray : core.clone.Clone StateArray := {
  clone := ClonesimpleStateArray.clone
}

/- [simple::{simple::StateArray}#2::index]:
   Source: 'src/simple.rs', lines 50:4-53:5 -/
def StateArray.index
  (self : StateArray) (index : (Usize × Usize × Usize)) : Result Bool :=
  do
  let (x, y, z) := index
  let i ← 5#usize * y
  let i1 ← i + x
  let i2 ← W * i1
  let i3 ← i2 + z
  Array.index_usize self i3

/- [simple::{simple::StateArray}#2::index_mut]:
   Source: 'src/simple.rs', lines 55:4-58:5 -/
def StateArray.index_mut
  (self : StateArray) (index : (Usize × Usize × Usize)) :
  Result (Bool × (Bool → StateArray))
  :=
  do
  let (x, y, z) := index
  let i ← 5#usize * y
  let i1 ← i + x
  let i2 ← W * i1
  let i3 ← i2 + z
  let (b, index_mut_back) ← Array.index_mut_usize self i3
  let back := fun ret => let a := index_mut_back ret
                         a
  ok (b, back)

/- [simple::theta::c]:
   Source: 'src/simple.rs', lines 62:4-76:5 -/
def theta.c (a : StateArray) (x : Usize) (z : Usize) : Result Bool :=
  do
  let b ← StateArray.index a (x, 0#usize, z)
  let b1 ← StateArray.index a (x, 1#usize, z)
  let b2 ← StateArray.index a (x, 2#usize, z)
  let b3 ← StateArray.index a (x, 3#usize, z)
  let b4 ← StateArray.index a (x, 4#usize, z)
  let b5 ← binxor b3 b4
  let b6 ← binxor b2 b5
  let b7 ← binxor b1 b6
  binxor b b7

/- [simple::theta::d]:
   Source: 'src/simple.rs', lines 77:4-82:5 -/
def theta.d (a : StateArray) (x : Usize) (z : Usize) : Result Bool :=
  do
  let i ← x + 4#usize
  let x1 ← i % 5#usize
  let i1 ← x + 1#usize
  let x2 ← i1 % 5#usize
  let i2 ← W - 1#usize
  let i3 ← z + i2
  let z2 ← i3 % W
  let b ← theta.c a x1 z
  let b1 ← theta.c a x2 z2
  binxor b b1

/- [simple::theta::inner::inner]: loop 0:
   Source: 'src/simple.rs', lines 92:20-95:21 -/
def theta.inner.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) (z : Usize) :
  Result StateArray
  :=
  if z < W
  then
    do
    let b ← StateArray.index a (x, y, z)
    let b1 ← theta.d a x z
    let b2 ← binxor b b1
    let (_, index_mut_back) ← StateArray.index_mut res (x, y, z)
    let z1 ← z + 1#usize
    let res1 := index_mut_back b2
    theta.inner.inner_loop res1 a x y z1
  else ok res
partial_fixpoint

/- [simple::theta::inner::inner]:
   Source: 'src/simple.rs', lines 90:26-96:17 -/
@[reducible]
def theta.inner.inner
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  theta.inner.inner_loop res a x y 0#usize

/- [simple::theta::inner]: loop 0:
   Source: 'src/simple.rs', lines 89:12-98:13 -/
def theta.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  if y < 5#usize
  then
    do
    let res1 ← theta.inner.inner res a x y
    let y1 ← y + 1#usize
    theta.inner_loop res1 a x y1
  else ok res
partial_fixpoint

/- [simple::theta::inner]:
   Source: 'src/simple.rs', lines 86:18-99:9 -/
@[reducible]
def theta.inner
  (res : StateArray) (a : StateArray) (x : Usize) : Result StateArray :=
  theta.inner_loop res a x 0#usize

/- [simple::theta]: loop 0:
   Source: 'src/simple.rs', lines 85:4-101:5 -/
def theta_loop
  (a : StateArray) (res : StateArray) (x : Usize) : Result StateArray :=
  if x < 5#usize
  then
    do
    let res1 ← theta.inner res a x
    let x1 ← x + 1#usize
    theta_loop a res1 x1
  else ok res
partial_fixpoint

/- [simple::theta]:
   Source: 'src/simple.rs', lines 61:0-103:1 -/
def theta (a : StateArray) : Result StateArray :=
  do
  let res ← DefaultsimpleStateArray.default
  theta_loop a res 0#usize

/- [simple::rho_offset]:
   Source: 'src/simple.rs', lines 105:0-107:1 -/
def rho_offset (t : Usize) : Result Usize :=
  do
  let i ← t + 1#usize
  let i1 ← t + 2#usize
  let i2 ← i * i1
  let i3 ← i2 / 2#usize
  i3 % W

/- [simple::rho::inner]: loop 0:
   Source: 'src/simple.rs', lines 115:12-119:13 -/
def rho.inner_loop
  (res : StateArray) (a : StateArray) (t : Usize) (x : Usize) (y : Usize)
  (z : Usize) :
  Result StateArray
  :=
  if z < W
  then
    do
    let i ← rho_offset t
    let i1 ← W - i
    let i2 ← z + i1
    let z2 ← i2 % W
    let b ← StateArray.index a (x, y, z2)
    let (_, index_mut_back) ← StateArray.index_mut res (x, y, z)
    let z1 ← z + 1#usize
    let res1 := index_mut_back b
    rho.inner_loop res1 a t x y z1
  else ok res
partial_fixpoint

/- [simple::rho::inner]:
   Source: 'src/simple.rs', lines 113:18-120:9 -/
@[reducible]
def rho.inner
  (res : StateArray) (a : StateArray) (t : Usize) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  rho.inner_loop res a t x y 0#usize

/- [simple::rho]: loop 0:
   Source: 'src/simple.rs', lines 112:4-123:5 -/
def rho_loop
  (a : StateArray) (x : Usize) (y : Usize) (res : StateArray) (t : Usize) :
  Result StateArray
  :=
  if t < 24#usize
  then
    do
    let res1 ← rho.inner res a t x y
    let i ← 2#usize * x
    let i1 ← 3#usize * y
    let i2 ← i + i1
    let lhs ← i2 % 5#usize
    let t1 ← t + 1#usize
    rho_loop a y lhs res1 t1
  else ok res
partial_fixpoint

/- [simple::rho]:
   Source: 'src/simple.rs', lines 108:0-125:1 -/
def rho (a : StateArray) : Result StateArray :=
  do
  let res ← ClonesimpleStateArray.clone a
  rho_loop a 1#usize 0#usize res 0#usize

/- [simple::pi::inner::inner]: loop 0:
   Source: 'src/simple.rs', lines 136:20-141:21 -/
def pi.inner.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) (z : Usize) :
  Result StateArray
  :=
  if z < W
  then
    do
    let i ← 3#usize * y
    let i1 ← x + i
    let x2 ← i1 % 5#usize
    let b ← StateArray.index a (x2, x, z)
    let (_, index_mut_back) ← StateArray.index_mut res (x, y, z)
    let z1 ← z + 1#usize
    let res1 := index_mut_back b
    pi.inner.inner_loop res1 a x y z1
  else ok res
partial_fixpoint

/- [simple::pi::inner::inner]:
   Source: 'src/simple.rs', lines 134:26-142:17 -/
@[reducible]
def pi.inner.inner
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  pi.inner.inner_loop res a x y 0#usize

/- [simple::pi::inner]: loop 0:
   Source: 'src/simple.rs', lines 133:12-144:13 -/
def pi.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  if y < 5#usize
  then
    do
    let res1 ← pi.inner.inner res a x y
    let y1 ← y + 1#usize
    pi.inner_loop res1 a x y1
  else ok res
partial_fixpoint

/- [simple::pi::inner]:
   Source: 'src/simple.rs', lines 131:18-145:9 -/
@[reducible]
def pi.inner
  (res : StateArray) (a : StateArray) (x : Usize) : Result StateArray :=
  pi.inner_loop res a x 0#usize

/- [simple::pi]: loop 0:
   Source: 'src/simple.rs', lines 130:4-147:5 -/
def pi_loop
  (a : StateArray) (res : StateArray) (x : Usize) : Result StateArray :=
  if x < 5#usize
  then
    do
    let res1 ← pi.inner res a x
    let x1 ← x + 1#usize
    pi_loop a res1 x1
  else ok res
partial_fixpoint

/- [simple::pi]:
   Source: 'src/simple.rs', lines 127:0-149:1 -/
def pi (a : StateArray) : Result StateArray :=
  do
  let res ← ClonesimpleStateArray.clone a
  pi_loop a res 0#usize

/- [simple::chi::inner::inner]: loop 0:
   Source: 'src/simple.rs', lines 160:20-166:21 -/
def chi.inner.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) (z : Usize) :
  Result StateArray
  :=
  if z < W
  then
    do
    let i ← x + 1#usize
    let x1 ← i % 5#usize
    let i1 ← x + 2#usize
    let x2 ← i1 % 5#usize
    let b ← StateArray.index a (x, y, z)
    let b1 ← StateArray.index a (x1, y, z)
    let b2 ← binxor b1 true
    if b2
    then
      do
      let b3 ← StateArray.index a (x2, y, z)
      let b4 ← binxor b b3
      let (_, index_mut_back) ← StateArray.index_mut res (x, y, z)
      let z1 ← z + 1#usize
      let res1 := index_mut_back b4
      chi.inner.inner_loop res1 a x y z1
    else
      do
      let b3 ← binxor b false
      let (_, index_mut_back) ← StateArray.index_mut res (x, y, z)
      let z1 ← z + 1#usize
      let res1 := index_mut_back b3
      chi.inner.inner_loop res1 a x y z1
  else ok res
partial_fixpoint

/- [simple::chi::inner::inner]:
   Source: 'src/simple.rs', lines 158:26-167:17 -/
@[reducible]
def chi.inner.inner
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  chi.inner.inner_loop res a x y 0#usize

/- [simple::chi::inner]: loop 0:
   Source: 'src/simple.rs', lines 157:12-169:13 -/
def chi.inner_loop
  (res : StateArray) (a : StateArray) (x : Usize) (y : Usize) :
  Result StateArray
  :=
  if y < 5#usize
  then
    do
    let res1 ← chi.inner.inner res a x y
    let y1 ← y + 1#usize
    chi.inner_loop res1 a x y1
  else ok res
partial_fixpoint

/- [simple::chi::inner]:
   Source: 'src/simple.rs', lines 155:18-170:9 -/
@[reducible]
def chi.inner
  (res : StateArray) (a : StateArray) (x : Usize) : Result StateArray :=
  chi.inner_loop res a x 0#usize

/- [simple::chi]: loop 0:
   Source: 'src/simple.rs', lines 154:4-172:5 -/
def chi_loop
  (a : StateArray) (res : StateArray) (x : Usize) : Result StateArray :=
  if x < 5#usize
  then
    do
    let res1 ← chi.inner res a x
    let x1 ← x + 1#usize
    chi_loop a res1 x1
  else ok res
partial_fixpoint

/- [simple::chi]:
   Source: 'src/simple.rs', lines 151:0-174:1 -/
def chi (a : StateArray) : Result StateArray :=
  do
  let res ← ClonesimpleStateArray.clone a
  chi_loop a res 0#usize

/- [simple::IOTA_RC_POINTS]
   Source: 'src/simple.rs', lines 177:0-191:15 -/
@[global_simps]
def IOTA_RC_POINTS_body : Result (Array Bool 255#usize) :=
  ok
  (Array.make 255#usize [
    true, false, false, false, false, false, false, false, true, false, true,
    true, false, false, false, true, true, true, true, false, true, false,
    false, false, false, true, true, true, true, true, true, true, true, false,
    false, true, false, false, false, false, true, false, true, false, false,
    true, true, true, true, true, false, true, false, true, false, true, false,
    true, true, true, false, false, false, false, false, true, true, false,
    false, false, true, false, true, false, true, true, false, false, true,
    true, false, false, true, false, true, true, true, true, true, true, false,
    true, true, true, true, false, false, true, true, false, true, true, true,
    false, true, true, true, false, false, true, false, true, false, true,
    false, false, true, false, true, false, false, false, true, false, false,
    true, false, true, true, false, true, false, false, false, true, true,
    false, false, true, true, true, false, false, true, true, true, true,
    false, false, false, true, true, false, true, true, false, false, false,
    false, true, false, false, false, true, false, true, true, true, false,
    true, false, true, true, true, true, false, true, true, false, true, true,
    true, true, true, false, false, false, false, true, true, false, true,
    false, false, true, true, false, true, false, true, true, false, true,
    true, false, true, false, true, false, false, false, false, false, true,
    false, false, true, true, true, false, true, true, false, false, true,
    false, false, true, false, false, true, true, false, false, false, false,
    false, false, true, true, true, false, true, false, false, true, false,
    false, false, true, true, true, false, false, false
    ] (by native_decide))
@[global_simps, irreducible]
def IOTA_RC_POINTS : Array Bool 255#usize := eval_global IOTA_RC_POINTS_body (by native_decide)

/- [simple::iota_rc_point]:
   Source: 'src/simple.rs', lines 193:0-197:1 -/
def iota_rc_point (t : Usize) : Result Bool :=
  do
  let t1 ← t % 255#usize
  Array.index_usize IOTA_RC_POINTS t1

/- [simple::iota_rc_init]: loop 0:
   Source: 'src/simple.rs', lines 201:4-204:5 -/
def iota_rc_init_loop
  (ir : Usize) (rc : Array Bool 64#usize) (j : Usize) :
  Result (Array Bool 64#usize)
  :=
  if j <= L
  then
    do
    let i ← 7#usize * ir
    let i1 ← j + i
    let b ← iota_rc_point i1
    let i2 ← 1#usize <<< j
    let i3 ← i2 - 1#usize
    let rc1 ← Array.update rc i3 b
    let j1 ← j + 1#usize
    iota_rc_init_loop ir rc1 j1
  else ok rc
partial_fixpoint

/- [simple::iota_rc_init]:
   Source: 'src/simple.rs', lines 199:0-205:1 -/
@[reducible]
def iota_rc_init
  (ir : Usize) (rc : Array Bool 64#usize) : Result (Array Bool 64#usize) :=
  iota_rc_init_loop ir rc 0#usize

/- [simple::iota_a]: loop 0:
   Source: 'src/simple.rs', lines 209:4-212:5 -/
def iota_a_loop
  (res : StateArray) (a : StateArray) (rc : Array Bool 64#usize) (z : Usize) :
  Result StateArray
  :=
  if z < W
  then
    do
    let b ← StateArray.index a (0#usize, 0#usize, z)
    let b1 ← Array.index_usize rc z
    let b2 ← binxor b b1
    let (_, index_mut_back) ← StateArray.index_mut res (0#usize, 0#usize, z)
    let z1 ← z + 1#usize
    let res1 := index_mut_back b2
    iota_a_loop res1 a rc z1
  else ok res
partial_fixpoint

/- [simple::iota_a]:
   Source: 'src/simple.rs', lines 207:0-213:1 -/
@[reducible]
def iota_a
  (res : StateArray) (a : StateArray) (rc : Array Bool 64#usize) :
  Result StateArray
  :=
  iota_a_loop res a rc 0#usize

/- [simple::iota]:
   Source: 'src/simple.rs', lines 215:0-221:1 -/
def iota (ir : Usize) (a : StateArray) : Result StateArray :=
  do
  let rc := Array.repeat 64#usize false
  let rc1 ← iota_rc_init ir rc
  let res ← ClonesimpleStateArray.clone a
  iota_a res a rc1

/- [simple::round]:
   Source: 'src/simple.rs', lines 223:0-229:1 -/
def round (a : StateArray) (ir : Usize) : Result StateArray :=
  do
  let a1 ← theta a
  let a2 ← rho a1
  let a3 ← pi a2
  let a4 ← chi a3
  iota ir a4

/- [simple::keccak_p]: loop 0:
   Source: 'src/simple.rs', lines 234:4-237:5 -/
def keccak_p_loop (a : StateArray) (ir : Usize) : Result Unit :=
  if ir < 24#usize
  then do
       let a1 ← round a ir
       let ir1 ← ir + 1#usize
       keccak_p_loop a1 ir1
  else ok ()
partial_fixpoint

/- [simple::keccak_p]:
   Source: 'src/simple.rs', lines 231:0-239:1 -/
def keccak_p (s : Array Bool 1600#usize) : Result (Array Bool 1600#usize) :=
  do
  keccak_p_loop s 0#usize
  ok s

/- [simple::sponge_absorb]: loop 0:
   Source: 'src/simple.rs', lines 244:4-249:5 -/
def sponge_absorb_loop
  (bs : Slice Bool) (r : Usize) (s : Array Bool 1600#usize)
  (suffix : Slice Bool) (n : Usize) (i : Usize) :
  Result (Array Bool 1600#usize)
  :=
  if i < n
  then
    do
    let i1 ← r * i
    let i2 ← i + 1#usize
    let i3 ← r * i2
    let chunk ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSliceInst Bool) bs
        { start := i1, end_ := i3 }
    let (s1, to_slice_mut_back) ←
      (↑(Array.to_slice_mut s) : Result ((Slice Bool) × (Slice Bool →
         Array Bool 1600#usize)))
    let s2 ← xor_long s1 chunk
    let s3 := to_slice_mut_back s2
    let s4 ← keccak_p s3
    sponge_absorb_loop bs r s4 suffix n i2
  else
    do
    let i1 ← r * n
    let rest ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice Bool) bs
        { start := i1 }
    let i2 := Slice.len rest
    let i3 := Slice.len suffix
    let nb_left ← i2 + i3
    let (s1, to_slice_mut_back) ←
      (↑(Array.to_slice_mut s) : Result ((Slice Bool) × (Slice Bool →
         Array Bool 1600#usize)))
    let s2 ← xor_long s1 rest
    let s3 := to_slice_mut_back s2
    let (s4, to_slice_mut_back1) ←
      (↑(Array.to_slice_mut s3) : Result ((Slice Bool) × (Slice Bool →
         Array Bool 1600#usize)))
    let i4 := Slice.len rest
    let s5 ← xor_long_at s4 suffix i4
    let leftover ←
      (↑(core.num.Usize.saturating_sub nb_left r) : Result Usize)
    if leftover > 0#usize
    then
      do
      let s6 := to_slice_mut_back1 s5
      let s7 ← keccak_p s6
      let (s8, to_slice_mut_back2) ←
        (↑(Array.to_slice_mut s7) : Result ((Slice Bool) × (Slice Bool →
           Array Bool 1600#usize)))
      let s9 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice Bool) suffix
          { start := leftover }
      let s10 ← xor_long s8 s9
      let s11 := to_slice_mut_back2 s10
      let (s12, to_slice_mut_back3) ←
        (↑(Array.to_slice_mut s11) : Result ((Slice Bool) × (Slice Bool →
           Array Bool 1600#usize)))
      let s13 ←
        (↑(Array.to_slice (Array.make 1#usize [ true ])) : Result (Slice
           Bool))
      let i5 := Slice.len suffix
      let i6 ← i5 - leftover
      let s14 ← xor_long_at s12 s13 i6
      let s15 := to_slice_mut_back3 s14
      let (s16, to_slice_mut_back4) ←
        (↑(Array.to_slice_mut s15) : Result ((Slice Bool) × (Slice Bool →
           Array Bool 1600#usize)))
      let s17 ←
        (↑(Array.to_slice (Array.make 1#usize [ true ])) : Result (Slice
           Bool))
      let i7 ← r - 1#usize
      let s18 ← xor_long_at s16 s17 i7
      let s19 := to_slice_mut_back4 s18
      keccak_p s19
    else
      do
      let s6 := to_slice_mut_back1 s5
      let (s7, to_slice_mut_back2) ←
        (↑(Array.to_slice_mut s6) : Result ((Slice Bool) × (Slice Bool →
           Array Bool 1600#usize)))
      let s8 ←
        (↑(Array.to_slice (Array.make 1#usize [ true ])) : Result (Slice
           Bool))
      let s9 ← xor_long_at s7 s8 nb_left
      let i5 ← nb_left + 1#usize
      if i5 < r
      then
        do
        let s10 := to_slice_mut_back2 s9
        let (s11, to_slice_mut_back3) ←
          (↑(Array.to_slice_mut s10) : Result ((Slice Bool) × (Slice Bool
             → Array Bool 1600#usize)))
        let s12 ←
          (↑(Array.to_slice (Array.make 1#usize [ true ])) : Result (Slice
             Bool))
        let i6 ← r - 1#usize
        let s13 ← xor_long_at s11 s12 i6
        let s14 := to_slice_mut_back3 s13
        keccak_p s14
      else
        do
        let s10 := to_slice_mut_back2 s9
        let s11 ← keccak_p s10
        let (s12, to_slice_mut_back3) ←
          (↑(Array.to_slice_mut s11) : Result ((Slice Bool) × (Slice Bool
             → Array Bool 1600#usize)))
        let s13 ←
          (↑(Array.to_slice (Array.make 1#usize [ true ])) : Result (Slice
             Bool))
        let i6 ← r - 1#usize
        let s14 ← xor_long_at s12 s13 i6
        let s15 := to_slice_mut_back3 s14
        keccak_p s15
partial_fixpoint

/- [simple::sponge_absorb]:
   Source: 'src/simple.rs', lines 241:0-276:1 -/
def sponge_absorb
  (bs : Slice Bool) (r : Usize) (s : Array Bool 1600#usize)
  (suffix : Slice Bool) :
  Result (Array Bool 1600#usize)
  :=
  do
  let i := Slice.len bs
  let n ← i / r
  sponge_absorb_loop bs r s suffix n 0#usize

/- Trait implementation: [core::marker::{core::marker::Copy for bool}#53]
   Source: '/rustc/library/core/src/marker.rs', lines 48:25-48:62
   Name pattern: core::marker::Copy<bool> -/
@[reducible]
def core.marker.CopyBool : core.marker.Copy Bool := {
  cloneInst := core.clone.CloneBool
}

/- [simple::sponge_squeeze]: loop 0:
   Source: 'src/simple.rs', lines 282:4-291:5 -/
def sponge_squeeze_loop
  (r : Usize) (z : Slice Bool) (s : Array Bool 1600#usize) (i : Usize) :
  Result (Slice Bool)
  :=
  do
  let s1 ← (↑(Array.to_slice s) : Result (Slice Bool))
  let (added, z1) ← add_to_vec core.marker.CopyBool z i s1 r
  let i1 ← i + added
  let i2 := Slice.len z1
  if i2 <= i1
  then ok z1
  else do
       let s2 ← keccak_p s
       sponge_squeeze_loop r z1 s2 i1
partial_fixpoint

/- [simple::sponge_squeeze]:
   Source: 'src/simple.rs', lines 279:0-292:1 -/
@[reducible]
def sponge_squeeze
  (r : Usize) (z : Slice Bool) (s : Array Bool 1600#usize) :
  Result (Slice Bool)
  :=
  sponge_squeeze_loop r z s 0#usize

/- [simple::sponge]:
   Source: 'src/simple.rs', lines 294:0-298:1 -/
def sponge
  (r : Usize) (bs : Slice Bool) (output : Slice Bool) (suffix : Slice Bool) :
  Result (Slice Bool)
  :=
  do
  let s := Array.repeat 1600#usize false
  let s1 ← sponge_absorb bs r s suffix
  sponge_squeeze r output s1

/- [simple::SHA3_SUFFIX]
   Source: 'src/simple.rs', lines 300:0-300:45 -/
@[global_simps]
def SHA3_SUFFIX_body : Result (Array Bool 2#usize) :=
  ok (Array.make 2#usize [ false, true ])
@[global_simps, irreducible]
def SHA3_SUFFIX : Array Bool 2#usize := eval_global SHA3_SUFFIX_body

/- [simple::sha3_224]:
   Source: 'src/simple.rs', lines 301:0-301:141 -/
def sha3_224 (bs : Slice Bool) : Result (Array Bool 224#usize) :=
  do
  let output := Array.repeat 224#usize false
  let i ← 2#usize * 224#usize
  let i1 ← B - i
  let (s, to_slice_mut_back) ←
    (↑(Array.to_slice_mut output) : Result ((Slice Bool) × (Slice Bool →
       Array Bool 224#usize)))
  let s1 ← (↑(Array.to_slice SHA3_SUFFIX) : Result (Slice Bool))
  let s2 ← sponge i1 bs s s1
  ok (to_slice_mut_back s2)

/- [simple::sha3_256]:
   Source: 'src/simple.rs', lines 302:0-302:141 -/
def sha3_256 (bs : Slice Bool) : Result (Array Bool 256#usize) :=
  do
  let output := Array.repeat 256#usize false
  let i ← 2#usize * 256#usize
  let i1 ← B - i
  let (s, to_slice_mut_back) ←
    (↑(Array.to_slice_mut output) : Result ((Slice Bool) × (Slice Bool →
       Array Bool 256#usize)))
  let s1 ← (↑(Array.to_slice SHA3_SUFFIX) : Result (Slice Bool))
  let s2 ← sponge i1 bs s s1
  ok (to_slice_mut_back s2)

/- [simple::sha3_384]:
   Source: 'src/simple.rs', lines 303:0-303:141 -/
def sha3_384 (bs : Slice Bool) : Result (Array Bool 384#usize) :=
  do
  let output := Array.repeat 384#usize false
  let i ← 2#usize * 384#usize
  let i1 ← B - i
  let (s, to_slice_mut_back) ←
    (↑(Array.to_slice_mut output) : Result ((Slice Bool) × (Slice Bool →
       Array Bool 384#usize)))
  let s1 ← (↑(Array.to_slice SHA3_SUFFIX) : Result (Slice Bool))
  let s2 ← sponge i1 bs s s1
  ok (to_slice_mut_back s2)

/- [simple::sha3_512]:
   Source: 'src/simple.rs', lines 304:0-304:141 -/
def sha3_512 (bs : Slice Bool) : Result (Array Bool 512#usize) :=
  do
  let output := Array.repeat 512#usize false
  let i ← 2#usize * 512#usize
  let i1 ← B - i
  let (s, to_slice_mut_back) ←
    (↑(Array.to_slice_mut output) : Result ((Slice Bool) × (Slice Bool →
       Array Bool 512#usize)))
  let s1 ← (↑(Array.to_slice SHA3_SUFFIX) : Result (Slice Bool))
  let s2 ← sponge i1 bs s s1
  ok (to_slice_mut_back s2)

/- [simple::SHAKE_SUFFIX]
   Source: 'src/simple.rs', lines 306:0-306:42 -/
@[global_simps]
def SHAKE_SUFFIX_body : Result (Array Bool 4#usize) :=
  ok (Array.repeat 4#usize true)
@[global_simps, irreducible]
def SHAKE_SUFFIX : Array Bool 4#usize := eval_global SHAKE_SUFFIX_body

/- [simple::shake128]:
   Source: 'src/simple.rs', lines 307:0-307:99 -/
def shake128 (bs : Slice Bool) (output : Slice Bool) : Result (Slice Bool) :=
  do
  let i ← 2#usize * 128#usize
  let i1 ← B - i
  let s ← (↑(Array.to_slice SHAKE_SUFFIX) : Result (Slice Bool))
  sponge i1 bs output s

/- [simple::shake256]:
   Source: 'src/simple.rs', lines 308:0-308:99 -/
def shake256 (bs : Slice Bool) (output : Slice Bool) : Result (Slice Bool) :=
  do
  let i ← 2#usize * 256#usize
  let i1 ← B - i
  let s ← (↑(Array.to_slice SHAKE_SUFFIX) : Result (Slice Bool))
  sponge i1 bs output s

end simple
