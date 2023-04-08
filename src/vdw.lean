import data.finset.card
import data.fintype.basic
import algebra.big_operators.basic
import data.bitvec.core
import data.fin.basic
import combinatorics.pigeonhole

import .pick_tactic

def arithprog(a b c:ℕ):Prop:=∃ k:ℕ, (b=a+k) ∧ (c=b+k)

def vdW_prop (N : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → fin r, ∃ (a b c : fin N), (arithprog a b c) ∧ (f a = f b) ∧ (f b = f c)

lemma vdW_monotone : ∀ n r, vdW_prop n r → ∀ m, n ≤ m → vdW_prop m r :=
begin
intros,
unfold vdW_prop,
intro,
unfold vdW_prop at ᾰ,
have abc: ∃ (a b c : fin n), arithprog ↑a ↑b ↑c ∧ f ↑a = f ↑b ∧ f ↑b = f ↑c,
apply ᾰ,
rcases abc with ⟨x, y, z, xyz_h⟩,
use [⟨x, lt_of_lt_of_le x.2 ᾰ_1⟩, ⟨y, lt_of_lt_of_le y.2 ᾰ_1⟩, ⟨z, lt_of_lt_of_le z.2 ᾰ_1⟩],
apply xyz_h,
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
pick 3 from (finset.filter (λ (x : fin 5), f x = y) finset.univ),
sorry
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
sorry
end

lemma vdW325 : vdW_prop 325 2 :=
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
pick 2 from (finset.filter (λ (x : fin 33), g x = y₅) finset.univ),
simp at wr wr_1,

let targetfinset := (insert (5 * a.val) (insert (5 * a.val + 1) (insert (5 * a.val + 2) (∅:(finset ℕ))))),
have fin25 : fintype.card (fin 2) • 1 <  fintype.card ↥targetfinset := by simp,
let f' : (insert (5 * a.val) (insert (5 * a.val + 1) (insert (5 * a.val + 2) (∅:(finset ℕ))))) → fin 2 := λ k, f k,
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f' fin25,
rcases fh' with ⟨c, chyp⟩,
pick 2 from (finset.filter (λ (x : ↥{5 * a.val, 5 * a.val + 1, 5 * a.val + 2}), f' x = c) finset.univ),
sorry
end
