-- -- NOTE: Adapted from Lean 4.18.0
-- /-
-- Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Kim Morrison
-- -/
-- prelude
-- import Init.Data.Array.Lemmas
-- import Init.Data.List.Nat.TakeDrop

-- /-!
-- # Lemmas about `Array.extract`

-- This file follows the contents of `Init.Data.List.TakeDrop` and `Init.Data.List.Nat.TakeDrop`.
-- -/


-- open Nat
-- namespace Array

-- /-! ### extract -/

-- @[simp] theorem extract_of_size_lt {as : Array α} {i j : Nat} (h : as.size < j) :
--     as.extract i j = as.extract i as.size := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract] at h₁ h₂
--     simp [h]

-- theorem size_extract_le {as : Array α} {i j : Nat} :
--     (as.extract i j).size ≤ j - i := by
--   simp
--   omega

-- theorem size_extract_le' {as : Array α} {i j : Nat} :
--     (as.extract i j).size ≤ as.size - i := by
--   simp
--   omega

-- theorem size_extract_of_le {as : Array α} {i j : Nat} (h : j ≤ as.size) :
--     (as.extract i j).size = j - i := by
--   simp
--   omega

-- @[simp]
-- theorem extract_push {as : Array α} {b : α} {start stop : Nat} (h : stop ≤ as.size) :
--     (as.push b).extract start stop = as.extract start stop := by
--   ext i h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, size_push] at h₁ h₂
--     simp only [getElem_extract, getElem_push]
--     rw [dif_pos (by omega)]

-- @[simp]
-- theorem extract_eq_pop {as : Array α} {stop : Nat} (h : stop = as.size - 1) :
--     as.extract 0 stop = as.pop := by
--   ext i h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, size_pop] at h₁ h₂
--     simp [getElem_extract, getElem_pop]

-- @[simp]
-- theorem extract_append_extract {as : Array α} {i j k : Nat} :
--     as.extract i j ++ as.extract j k = as.extract (min i j) (max j k) := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_append, size_extract] at h₁ h₂
--     simp only [getElem_append, size_extract, getElem_extract]
--     split <;>
--     · congr 1
--       omega

-- @[simp]
-- theorem extract_eq_empty_iff {as : Array α} :
--     as.extract i j = #[] ↔ min j as.size ≤ i := by
--   constructor
--   · intro h
--     replace h := congrArg Array.size h
--     simp at h
--     omega
--   · intro h
--     exact eq_empty_of_size_eq_zero (by simp; omega)

-- theorem extract_eq_empty_of_le {as : Array α} (h : min j as.size ≤ i) :
--     as.extract i j = #[] :=
--   extract_eq_empty_iff.2 h

-- theorem lt_of_extract_ne_empty {as : Array α} (h : as.extract i j ≠ #[]) :
--     i < min j as.size :=
--   gt_of_not_le (mt extract_eq_empty_of_le h)

-- @[simp]
-- theorem extract_eq_self_iff {as : Array α} :
--     as.extract i j = as ↔ as.size = 0 ∨ i = 0 ∧ as.size ≤ j := by
--   constructor
--   · intro h
--     replace h := congrArg Array.size h
--     simp at h
--     omega
--   · intro h
--     ext l h₁ h₂
--     · simp
--       omega
--     · simp only [size_extract] at h₁
--       simp only [getElem_extract]
--       congr 1
--       omega

-- theorem extract_eq_self_of_le {as : Array α} (h : as.size ≤ j) :
--     as.extract 0 j = as :=
--   extract_eq_self_iff.2 (.inr ⟨rfl, h⟩)

-- theorem le_of_extract_eq_self {as : Array α} (h : as.extract i j = as) :
--     as.size ≤ j := by
--   replace h := congrArg Array.size h
--   simp at h
--   omega

-- @[simp]
-- theorem extract_size_left {as : Array α} :
--     as.extract as.size j = #[] := by
--   simp
--   omega

-- @[simp]
-- theorem push_extract_getElem {as : Array α} {i j : Nat} (h : j < as.size) :
--     (as.extract i j).push as[j] = as.extract (min i j) (j + 1) := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_push, size_extract] at h₁ h₂
--     simp only [getElem_push, size_extract, getElem_extract]
--     split <;>
--     · congr
--       omega

-- theorem extract_succ_right {as : Array α} {i j : Nat} (w : i < j + 1) (h : j < as.size) :
--     as.extract i (j + 1) = (as.extract i j).push as[j] := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, push_extract_getElem] at h₁ h₂
--     simp only [getElem_extract, push_extract_getElem]
--     congr
--     omega

-- theorem extract_sub_one {as : Array α} {i j : Nat} (h : j < as.size) :
--     as.extract i (j - 1) = (as.extract i j).pop := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, size_pop] at h₁ h₂
--     simp only [getElem_extract, getElem_pop]

-- @[simp]
-- theorem getElem?_extract_of_lt {as : Array α} {i j k : Nat} (h : k < min j as.size - i) :
--     (as.extract i j)[k]? = some (as[i + k]'(by omega)) := by
--   simp [getElem?_extract, h]

-- theorem getElem?_extract_of_succ {as : Array α} {j : Nat} :
--     (as.extract 0 (j + 1))[j]? = as[j]? := by
--   simp [getElem?_extract]
--   omega

-- /- @[simp] theorem extract_extract {as : Array α} {i j k l : Nat} : -/
-- /-     (as.extract i j).extract k l = as.extract (i + k) (min (i + l) j) := by -/
-- /-   ext m h₁ h₂ -/
-- /-   · simp -/
-- /-     omega -/
-- /-   · simp only [size_extract] at h₁ h₂ -/
-- /-     simp [Nat.add_assoc] -/

-- theorem extract_eq_empty_of_eq_empty {as : Array α} {i j : Nat} (h : as = #[]) :
--     as.extract i j = #[] := by
--   simp [h]

-- theorem ne_empty_of_extract_ne_empty {as : Array α} {i j : Nat} (h : as.extract i j ≠ #[]) :
--     as ≠ #[] :=
--   mt extract_eq_empty_of_eq_empty h

-- theorem extract_set {as : Array α} {i j k : Nat} (h : k < as.size) {a : α} :
--     (as.set k a).extract i j =
--       if _ : k < i then
--         as.extract i j
--       else if _ : k < min j as.size then
--         (as.extract i j).set (k - i) a (by simp; omega)
--       else as.extract i j := by
--   split
--   · ext l h₁ h₂
--     · simp
--     · simp at h₁ h₂
--       simp [getElem_set]
--       omega
--   · split
--     · ext l h₁ h₂
--       · simp
--       · simp only [getElem_extract, getElem_set]
--         split
--         · rw [if_pos]; omega
--         · rw [if_neg]; omega
--     · ext l h₁ h₂
--       · simp
--       · simp at h₁ h₂
--         simp [getElem_set]
--         omega

-- theorem set_extract {as : Array α} {i j k : Nat} (h : k < (as.extract i j).size) {a : α} :
--     (as.extract i j).set k a = (as.set (i + k) a (by simp at h; omega)).extract i j := by
--   ext l h₁ h₂
--   · simp
--   · simp_all [getElem_set]

-- @[simp]
-- theorem extract_append {as bs : Array α} {i j : Nat} :
--     (as ++ bs).extract i j = as.extract i j ++ bs.extract (i - as.size) (j - as.size) := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, size_append] at h₁ h₂
--     simp only [getElem_extract, getElem_append, size_extract]
--     split
--     · split
--       · rfl
--       · omega
--     · split
--       · omega
--       · congr 1
--         omega

-- /- theorem extract_append_left {as bs : Array α} : -/
-- /-     (as ++ bs).extract 0 as.size = as.extract 0 as.size := by -/
-- /-   simp -/

-- /- @[simp] theorem extract_append_right {as bs : Array α} : -/
-- /-     (as ++ bs).extract as.size (as.size + i) = bs.extract 0 i := by -/
-- /-   simp only [extract_append, extract_size_left, Nat.sub_self, empty_append] -/
-- /-   congr 1 -/
-- /-   omega -/

-- @[simp] theorem map_extract {as : Array α} {i j : Nat} :
--     (as.extract i j).map f = (as.map f).extract i j := by
--   ext l h₁ h₂
--   · simp
--   · simp only [size_map, size_extract] at h₁ h₂
--     simp only [getElem_map, getElem_extract]


-- theorem extract_eq_extract_right {as : Array α} {i j j' : Nat} :
--     as.extract i j = as.extract i j' ↔ min (j - i) (as.size - i) = min (j' - i) (as.size - i) := by
--   rcases as with ⟨as⟩
--   simp

-- theorem extract_eq_extract_left {as : Array α} {i i' j : Nat} :
--     as.extract i j = as.extract i' j ↔ min j as.size - i = min j as.size - i' := by
--   constructor
--   · intro h
--     replace h := congrArg Array.size h
--     simpa using h
--   · intro h
--     ext l h₁ h₂
--     · simpa
--     · simp only [size_extract] at h₁ h₂
--       simp only [getElem_extract]
--       congr 1
--       omega

-- /- theorem extract_add_left {as : Array α} {i j k : Nat} : -/
-- /-     as.extract (i + j) k = (as.extract i k).extract j (k - i) := by -/
-- /-   simp [extract_eq_extract_right] -/
-- /-   omega -/

-- theorem mem_extract_iff_getElem {as : Array α} {a : α} {i j : Nat} :
--     a ∈ as.extract i j ↔ ∃ (k : Nat) (hm : k < min j as.size - i), as[i + k] = a := by
--   rcases as with ⟨as⟩
--   simp [List.mem_take_iff_getElem]
--   constructor <;>
--   · rintro ⟨k, h, rfl⟩
--     exact ⟨k, by omega, rfl⟩

-- theorem set_eq_push_extract_append_extract {as : Array α} {i : Nat} (h : i < as.size) {a : α} :
--     as.set i a = (as.extract 0 i).push a ++ (as.extract (i + 1) as.size) := by
--   rcases as with ⟨as⟩
--   simp at h
--   simp [List.set_eq_take_append_cons_drop, h, List.take_of_length_le]

-- theorem extract_reverse {as : Array α} {i j : Nat} :
--     as.reverse.extract i j = (as.extract (as.size - j) (as.size - i)).reverse := by
--   ext l h₁ h₂
--   · simp
--     omega
--   · simp only [size_extract, size_reverse] at h₁ h₂
--     simp only [getElem_extract, getElem_reverse, size_extract]
--     congr 1
--     omega

-- theorem reverse_extract {as : Array α} {i j : Nat} :
--     (as.extract i j).reverse = as.reverse.extract (as.size - j) (as.size - i) := by
--   rw [extract_reverse]
--   simp
--   by_cases h : j ≤ as.size
--   · have : as.size - (as.size - j) = j := by omega
--     simp [this, extract_eq_extract_left]
--     omega
--   · have : as.size - (as.size - j) = as.size := by omega
--     simp only [Nat.not_le] at h
--     simp [h, this, extract_eq_extract_left]
--     omega

-- /-! ### takeWhile -/

-- theorem takeWhile_map {f : α → β} {p : β → Bool} {as : Array α} :
--     (as.map f).takeWhile p = (as.takeWhile (p ∘ f)).map f := by
--   rcases as with ⟨as⟩
--   simp [List.takeWhile_map]

-- theorem takeWhile_filterMap {f : α → Option β} {p : β → Bool} {as : Array α} :
--     (as.filterMap f).takeWhile p = (as.takeWhile fun a => (f a).all p).filterMap f := by
--   rcases as with ⟨as⟩
--   simp [List.takeWhile_filterMap]

-- theorem takeWhile_filter {p q : α → Bool} {as : Array α} :
--     (as.filter p).takeWhile q = (as.takeWhile fun a => !p a || q a).filter p := by
--   rcases as with ⟨as⟩
--   simp [List.takeWhile_filter]


-- @[simp] theorem takeWhile_append_of_pos {p : α → Bool} {xs ys : Array α} (h : ∀ a ∈ xs, p a) :
--     (xs ++ ys).takeWhile p = xs ++ ys.takeWhile p := by
--   rcases xs with ⟨xs⟩
--   rcases ys with ⟨ys⟩
--   simp at h
--   simp [List.takeWhile_append_of_pos h]


-- theorem extract_takeWhile {as : Array α} {i : Nat} :
--     (as.takeWhile p).extract 0 i = (as.extract 0 i).takeWhile p := by
--   rcases as with ⟨as⟩
--   simp [List.take_takeWhile]

-- @[simp] theorem all_takeWhile {as : Array α} :
--     (as.takeWhile p).all p = true := by
--   rcases as with ⟨as⟩
--   rw [List.takeWhile_toArray] -- Not sure why this doesn't fire with `simp`.
--   simp

-- theorem takeWhile_eq_extract_findIdx_not {xs : Array α} {p : α → Bool} :
--     takeWhile p xs = xs.extract 0 (xs.findIdx (fun a => !p a)) := by
--   rcases xs with ⟨xs⟩
--   simp [List.takeWhile_eq_take_findIdx_not]

-- end Array
