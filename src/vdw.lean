import data.finset.card
import data.fintype.basic
import data.bitvec.core
import data.fin.basic
import combinatorics.pigeonhole
import data.nat.lattice
import tactic.fin_cases

import data.nat.cast
import data.nat.basic

import .pick_tactic

structure arithprog (α : Type) (length : ℕ) [has_add α] := (start : α) (diff : α)

instance {α : Type} {l : ℕ} [has_add α] : has_mem α (arithprog α l) := ⟨λ a s, ∃ (i : fin l), a = nat.iterate (λ j : α, j + s.diff) i.val s.start⟩

def vdW_prop (N : ℕ) (k : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → fin r, ∃ (s : arithprog ℕ k) (c : fin r), s.diff > 0 ∧ (∀ e ∈ s, e < N ∧ f e = c)

lemma vdW_monotone : ∀ n k r, vdW_prop n k r → ∀ m, n ≤ m → vdW_prop m k r :=
begin
unfold vdW_prop,
intros _ _ _ vdwn _  nleqm _,
rcases (vdwn f) with ⟨s, c, sdiff, eprop⟩,
-- use { start := s.start, diff := s.diff},
use [s, c],
split,
assumption,
intros _ eins,
rcases (eprop e eins) with ⟨eltn, ecolor⟩,
split,
apply lt_of_lt_of_le eltn nleqm,
assumption,
end

example : ∀ f : fin 5 → fin 2, ∃ a b c, (a ≠ b) ∧ (b ≠ c) ∧ (a ≠ c) ∧ (f a = f b) ∧ (f b = f c) :=
begin
intros,

--2*2<5
have inq : fintype.card (fin 2) • 2 < ↑(fintype.card (fin 5)),
{simp,
linarith,},

--exist y<2 st. the set of x st. f(x)=y have cardinality >2
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f inq,
cases fh' with y fh'',
pick 3 from (finset.filter (λ (x : fin 5), f x = y) finset.univ) with a b c,
use [a, b, c],
simp at a.elem b.elem c.elem,

repeat{split},
apply ne_of_lt a.lt.b,
apply ne_of_lt b.lt.c,

have a.lt.c : a < c,
transitivity b,
exact a.lt.b, 
exact b.lt.c,

apply ne_of_lt a.lt.c,

rw [a.elem, b.elem],
rw [b.elem, c.elem],
end

example : ∀ f : fin 5 → fin 2, ∃ a b c, (a < b) ∧ (b < c) ∧ (f a = f b) ∧ (f b = f c) := 
begin
intros,

--2*2<5
have inq : fintype.card (fin 2) • 2 < ↑(fintype.card (fin 5)),
{simp,
linarith,},

--exist y<2 st. the set of x st. f(x)=y have cardinality >2
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f inq,
cases fh' with y fh'',
pick 3 from (finset.filter (λ (x : fin 5), f x = y) finset.univ) with a b c,
use [a,b,c],

simp at a.elem b.elem c.elem,
repeat {split},
exact a.lt.b,
exact b.lt.c,
rw [a.elem,b.elem],
rw [b.elem,c.elem],
end

lemma vdW325 : vdW_prop 325 3 2 :=
begin
unfold vdW_prop,
intros,
-- f is the color function
-- Define g: takes any number between 1-33 groups, and return the color combination of that group
let g : fin 33 → bitvec 5 := λ k, vector.of_fn (λ i, f (5 * k + i) = 0),
-- There are only 32 types of coloring, thus 32<33
have fin533 : fintype.card (bitvec 5) • 1 < fintype.card (fin 33),
simp,
linarith,
-- There exists more than 1 blocks that have the same color combination
have ghyp := fintype.exists_lt_card_fiber_of_mul_lt_card g fin533,
rcases ghyp with ⟨y₅, y₅hyp⟩,
-- pick 2 blocks with same color combination
pick 2 from (finset.filter (λ (x : fin 33), g x = y₅) finset.univ) with block₁ block₂,
simp at block₁.elem block₂.elem,

have notc : ∀ {c : fin 2}, ∀ {x y : ℕ}, f x ≠ c → f y ≠ c → f x = f y,
intros c x y h₁ h₂,
let c₁ := f x, 
let c₂ := f y,
change c₁ = c₂,

fin_cases c,

fin_cases c₁ using h_1,
contradiction,
fin_cases c₂ using h_2,
contradiction,
rw [h_1, h_2],

fin_cases c₁ using h_1,
fin_cases c₂ using h_2,
rw [h_1, h_2],
contradiction,
contradiction,

have blockeq : ∀ (i : fin 5), f (5 * ↑block₁ + i) = f (5 * ↑block₂ + i),
intro,
have fb₁b₂ := congr_arg (λ v, vector.nth v i) (eq.trans block₂.elem (eq.symm block₁.elem)),
let fb := f (5 * ↑block₁ + ↑i),
simp [← fb] at fb₁b₂ ⊢,
fin_cases i; {
  fin_cases fb using fbeq,
  simp [fbeq] at fb₁b₂ ⊢,
  rw fb₁b₂,
  have fbneq0 : fb ≠ 0,
  simp [fbeq],
  simp [← fb, fbeq] at fb₁b₂,
  exact notc fbneq0 fb₁b₂,
},

clear fin533 y₅hyp block₂.elem block₁.elem y₅,

-- let targetfinset be the first three element in block1
let targetfinset := (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))),
-- at least two elememts have the same color
have fin25 : fintype.card (fin 2) • 1 <  fintype.card ↥targetfinset := by simp,
-- Define f': takes one of the elemnet in finset ∅, return its color
let f' : (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))) → fin 2 := λ k, f k,
-- There exists more than 1 elements that have the same color
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25,
rcases fh' with ⟨c, chyp⟩,
-- Among the selected three elements, pick two elements that have the same color
pick 2 from (finset.filter (λ (x : ↥{5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}), f' x = c) finset.univ) with a₁ a₂,
simp at a₁.elem a₂.elem,
clear fin25 chyp,

have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂, 
-- express a2 as 5b2+i and prove
have out₂ : ∃ i, (↑a₂ = 5 * ↑block₁ + i) ∧ (i < 3),
-- three cases for a2: i =0,1,2
rcases a₂.elem.left with rfl | rfl | rfl,
use 0,
simp,
use 1,
simp,
use 2,
simp,
rcases out₂ with ⟨i₂, a₂eq, i₂ineq⟩,
simp [a₂eq] at a₁.lt.a₂.cast_bound,

-- express a1 as 5b1+i and prove
have out₁ : ∃ i, (↑a₁ = 5 * ↑block₁ + i) ∧ (i < i₂),
-- three cases for a1: i =0,1,2
rcases a₁.elem.left with rfl | rfl | rfl,
use 0,
simp at a₁.lt.a₂.cast_bound ⊢,
exact a₁.lt.a₂.cast_bound,
use 1,
simp at a₁.lt.a₂.cast_bound ⊢,
exact a₁.lt.a₂.cast_bound,
use 2,
simp at a₁.lt.a₂.cast_bound ⊢,
exact a₁.lt.a₂.cast_bound,
rcases out₁ with ⟨i₁, a₁eq, i₁ineq⟩,
simp [a₁eq, a₂eq, tsub_add_eq_tsub_tsub],
clear targetfinset a₁.lt.a₂ a₁.lt.a₂.cast_bound,

let I := i₂ - i₁,
let B : ℕ := ↑block₂ - ↑block₁,
have Ibound : i₁ + I < 3,
change i₁ + (i₂ - i₁) < 3,
rw ← nat.add_sub_assoc (le_of_lt i₁ineq) i₁,
simp,
exact i₂ineq,

have Bbound : ↑block₁ + B < 33,
change ↑block₁ + (↑block₂ - ↑block₁) < 33,
have block₁.lt.block₂.cast_bound : ↑block₁ < ↑block₂ := by exact block₁.lt.block₂,
rw ← nat.add_sub_assoc (le_of_lt block₁.lt.block₂.cast_bound) block₁,
simp,
have b₂.cast_bound: ↑block₂ < 33 := by exact block₂.property,
exact b₂.cast_bound,

let a₃ : ℕ := ↑a₁ + (I + I),
-- two cases: same color vs. different color
cases (fin.decidable_eq 2) (f a₃) (f a₁),
rotate,

--- Same color case
-- Case I: 5block₁ + i₁, 5block₁ + i₂, 5block₁ + i₃
use {start := a₁, diff := I},
simp,
split,

assumption,
use c,
intros,
cases H with i ehyp,
split,

--Prove a₁ a₂ a₃ < 325
fin_cases i; simp [ehyp]; linarith,

-- Prove a₁ a₂ a₃ have same color
fin_cases i,
simp [ehyp], 
exact a₁.elem.right,

--f(a₂) = c
simp [ehyp],

have temp: ↑a₁ + I = ↑a₂,
change ↑a₁ + (i₂ - i₁) = ↑a₂,
rw a₁eq,
rw add_assoc (5*↑block₁) i₁ (i₂-i₁),
rw (add_tsub_cancel_of_le (le_of_lt i₁ineq)),
rw ← a₂eq,

rw temp,
exact a₂.elem.right,

-- f(a₃) = c
simp [← a₃, ehyp, h],
exact a₁.elem.right,
cases (fin.decidable_eq 2) (f (↑a₁ + (I + 5 * B + (I + 5 * B)))) (f a₁),
rotate,

--Case II: 5block₁ + i₁, 5block₂ + i₂, 5block₃ + i₃
use {start := a₁, diff := I + 5*B},
simp,
split,

left,
assumption,

use c,
intros,
cases H with i ehyp,
split,

have b₁.cast_bound: ↑block₁ < 33 := by exact block₁.property,

--prove <325
fin_cases i,

simp [ehyp],
transitivity 170,
rcases a₁.elem.left with rfl | rfl | rfl; simp; linarith only [b₁.cast_bound],
simp,

simp [ehyp],
linarith,

simp [ehyp, a₁eq],
linarith only [Ibound, Bbound, b₁.cast_bound, i₁ineq],
--prove color = c
fin_cases i,

simp [ehyp], 
exact a₁.elem.right,

admit,

simp [ehyp, h_1],
exact a₁.elem.right,

--Case III:  5block₁ + i₃, 5block₂ + i₃, 5block₃ + i₃
use {start := a₃, diff := 5*B},
simp,
split,

assumption,

use f(a₃),
intros,
cases H with i ehyp,
split,
--prove < 325
fin_cases i; simp [ehyp]; linarith,
--prove color ≠ c
fin_cases i,

simp at ehyp, 
tauto,

simp [ehyp],

end

noncomputable def vdW (k : ℕ) (r : ℕ) : ℕ := Inf { n : ℕ | vdW_prop n k r }

theorem vdW3 : vdW 3 2 = 9 :=
begin
unfold vdW,
have hs : ∀ (k₁ k₂ : ℕ), k₁ ≤ k₂ → k₁ ∈ {n : ℕ | vdW_prop n 3 2} → k₂ ∈ {n : ℕ | vdW_prop n 3 2},
intros _ _ k₁leqk₂ k₁elem,
simp at k₁elem ⊢,
intro f,
apply vdW_monotone k₁; assumption,
rw (nat.Inf_upward_closed_eq_succ_iff hs 8),
simp,
sorry
end
