import data.real.basic
import data.finset.basic

def nx (n:ℕ)(x:ℝ) := ↑n*x

def arithprog(a b c:ℕ):Prop:=∃ k:ℕ, (b=a+k) ∧ (c=b+k)

def vdw(N:ℕ)(r:ℕ):Prop := ∀ f:fin N → fin r,∃ (a b c:fin N), (arithprog a b c) ∧ (f a = f b)∧ (f b=f c)


lemma pigeonhole_principle : ∀ m n :ℕ , ∀ f:(fin m)→ (fin n), ∃ i:fin n, (finset.card {j:fin m | f j = i}) >= m/n :=sorry
lemma pigeonhole_principle : ∀ m n : ℕ, ∀ f : (fin m) → (fin n), ∃ i : fin n, (finset.card ({ j : fin m | f j = i }: finset ℕ )>= m / n := sorry

lemma vdw2: vdw 325 2 :=
begin
unfold vdw,
intro,


end

