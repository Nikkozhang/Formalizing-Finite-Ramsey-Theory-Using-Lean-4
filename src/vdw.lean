import data.finset.card
import data.fintype.basic
import algebra.big_operators.basic

def arithprog(a b c:ℕ):Prop:=∃ k:ℕ, (b=a+k) ∧ (c=b+k)

def vdW_prop (N : ℕ) (r : ℕ) : Prop := ∀ f : fin N → fin r, ∃ (a b c : fin N), (arithprog a b c) ∧ (f a = f b) ∧ (f b = f c)

lemma vdW_monotone : ∀ n r, vdW_prop n r → ∀ m, m ≥ n → vdW_prop m r := sorry

def fin_preim {α : Type} [decidable_eq α] {n : ℕ} (f : fin n → α) (i : α) : finset (fin n) := finset.filter (λ j, f j = i) (fin.fintype n).elems

lemma pigeonhole_principle : ∀ m n : ℕ, ∀ f : (fin m) → (fin n), ∃ i : fin n, (fin_preim f i).card >= m / n :=
begin
intros,
by_contra,
simp at h,
have h' : ((fin.fintype n).elems.bUnion (fin_preim f)).card = m,

end
