import data.finset.card
import data.fintype.basic
import algebra.big_operators.basic

def arithprog(a b c:ℕ):Prop:=∃ k:ℕ, (b=a+k) ∧ (c=b+k)

def vdW_prop (N : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → fin r, ∃ (a b c : fin N), (arithprog a b c) ∧ (f a = f b) ∧ (f b = f c)

lemma vdW_monotone : ∀ n r, vdW_prop n r → ∀ m, n ≤ m → vdW_prop m r :=
begin
intros _ _ vdWn _ nleqm,
unfold vdW_prop,
intro,
unfold vdW_prop at vdWn,
have david : ∃ (a b c : fin n), arithprog ↑a ↑b ↑c ∧ f ↑a = f ↑b ∧ f ↑b = f ↑c,
apply vdWn,
cases david with x,
cases david_h with y,
cases david_h_h with z,
use x,
apply lt_of_lt_of_le,
-- FIX THIS
sorry,
use y,
sorry,
use z,
sorry,
apply david_h_h_h,
end

def fin_preim {α : Type} [decidable_eq α] {n : ℕ} (f : fin n → α) (i : α) : finset (fin n) := finset.filter (λ j, f j = i) (fin.fintype n).elems

lemma pigeonhole_principle : ∀ m n : ℕ, ∀ f : (fin m) → (fin n), ∃ i : fin n, (fin_preim f i).card >= m / n :=
begin
intros,
by_contra,
simp at h,
have h' : ((fin.fintype n).elems.bUnion (fin_preim f)).card = m,

end
