import data.finset.card

import data.fintype.basic
import algebra.big_operators.basic
import data.fin.basic

def arithprog(a b c:ℕ):Prop:=∃ k:ℕ, (b=a+k) ∧ (c=b+k)

def vdW_prop (N : ℕ) (r : ℕ) : Prop := ∀ f : ℕ → fin r, ∃ (a b c : fin N), (arithprog a b c) ∧ (f a = f b) ∧ (f b = f c)

--def is_lt (n:ℕ )(a : fin n) : (a : ℕ) < n := a.2

--def cast_lt (n m:ℕ )(i : fin n) (h : i.1 < m) : fin m := ⟨i.1, h⟩

--def cast_le (n m:ℕ )(h : n ≤ m) : fin n ↪o fin m :=
--order_embedding.of_strict_mono (λ a, cast_lt a (lt_of_lt_of_le a.2 h)) $ λ a b h, h

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

def fin_preim {α : Type} [decidable_eq α] {n : ℕ} (f : fin n → α) (i : α) : finset (fin n) := finset.filter (λ j, f j = i) (fin.fintype n).elems

lemma pigeonhole_principle : ∀ m n : ℕ, ∀ f : (fin m) → (fin n), ∃ i : fin n, (fin_preim f i).card >= m / n :=
begin
intros,
by_contra,
simp at h,
have h' : ((fin.fintype n).elems.bUnion (fin_preim f)).card = m,
end
