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
let f𝔹 : ℕ → bool := λ k, f k = 0,
let g : fin 33 → bitvec 5 := λ k, f𝔹 (5 * k) ::ᵥ (f𝔹 (5 * k + 1) ::ᵥ (f𝔹 (5 * k + 2) ::ᵥ (f𝔹 (5 * k + 3) ::ᵥ (f𝔹 (5 * k + 4) ::ᵥ vector.nil)))),
have fin533 : fintype.card (bitvec 5) • 1 < fintype.card (fin 33),
simp,
linarith,
have ghyp := fintype.exists_lt_card_fiber_of_mul_lt_card g fin533,
rcases ghyp with ⟨y₅, y₅hyp⟩,
pick 2 from (finset.filter (λ (x : fin 33), g x = y₅) finset.univ) with block₁ block₂,
simp at block₁.elem block₂.elem,
let targetfinset := (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))),
have fin25 : fintype.card (fin 2) • 1 <  fintype.card ↥targetfinset := by simp,
let f' : (insert (5 * block₁.val) (insert (5 * block₁.val + 1) (insert (5 * block₁.val + 2) (∅:(finset ℕ))))) → fin 2 := λ k, f k,
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25,
rcases fh' with ⟨c, chyp⟩,
pick 2 from (finset.filter (λ (x : ↥{5 * block₁.val, 5 * block₁.val + 1, 5 * block₁.val + 2}), f' x = c) finset.univ) with a₁ a₂,
simp at a₁.elem a₂.elem,

have a₁.lt.a₂.cast_bound : ↑a₁ < ↑a₂ := by exact a₁.lt.a₂,
have out₂ : ∃ i, (↑a₂ = 5 * ↑block₁ + i) ∧ (i < 3),
rcases a₂.elem.left with rfl | rfl | rfl,
use 0,
simp,
use 1,
simp,
use 2,
simp,
rcases out₂ with ⟨i₂, a₂eq, i₂ineq⟩,
simp [a₂eq] at a₁.lt.a₂.cast_bound,
have out₁ : ∃ i, (↑a₁ = 5 * ↑block₁ + i) ∧ (i < i₂),
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
let I := i₂ - i₁,
let B : ℕ := ↑block₂ - ↑block₁,
have Abound : i₁ + I < 3,
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

have a₁.color : f' a₁ = c, from and.right a₁.elem,
have a₂.color : f' a₂ = c, from and.right a₂.elem,
simp [f'] at a₁.color a₂.color,

cases (fin.decidable_eq 2) (f a₃) (f a₁),
rotate,

-- Case I
rw a₁.color at h,
use {start := a₁, diff := I},
simp,
split,

assumption,
use c,
intros,
cases H with i ehyp,
split,

--Prove a₁ a₂ a₃ < 325
fin_cases i,
repeat{simp at ehyp,rw ehyp,linarith},

-- Prove a₁ a₂ a₃ have same color
fin_cases i,
--f(a₁) = c
simp at ehyp, 
rw ehyp, 
apply a₁.color,

--f(a₂) = c
simp at ehyp, 
rw ehyp,

have temp: ↑a₁ + I = ↑a₂,
change ↑a₁ + (i₂ - i₁) = ↑a₂,
rw a₁eq,
rw add_assoc (5*↑block₁) i₁ (i₂-i₁),
rw (add_tsub_cancel_of_le (le_of_lt i₁ineq)),
rw ← a₂eq,

rw temp,
apply a₂.color,

-- f(a₃) = c
simp at ehyp, 
rw ehyp, 
apply h,
rw a₁.color at h,


cases (fin.decidable_eq 2) (f (↑a₁ + (I + 5 * B + (I + 5 * B)))) (f a₁),
rotate,
--Case II
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

fin_cases i,

simp at ehyp,
rw ehyp,
transitivity 170,
rcases a₁.elem.left with rfl | rfl | rfl; simp; linarith only [b₁.cast_bound],
simp,

simp at ehyp,
rw ehyp,
linarith,

simp at ehyp,
rw ehyp,
rw a₁eq,
linarith only [Abound, Bbound, b₁.cast_bound, i₁ineq],

fin_cases i,

simp at ehyp, 
rw ehyp, 
apply a₁.color,

admit,

simp at ehyp, 
rw ehyp, 
rw a₁.color at h_1,
apply h_1,

--Case III
use {start := a₃, diff := 5*B},
simp,
split,

assumption,

use c,
intros,
cases H with i ehyp,
split,

fin_cases i,
repeat{simp at ehyp,rw ehyp,linarith},

fin_cases i,

simp at ehyp, 
rw ehyp, 



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
