import data.finset.card
import data.fintype.basic
import algebra.big_operators.basic
import data.fin.basic
import combinatorics.pigeonhole

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

lemma pick_one {α : Type} {s : finset α} [decidable_eq α] : 0 < s.card → ∃ (a : α) (t : finset α), (t.card = s.card.pred) ∧ (a ∉ t) ∧ (insert a t = s) := 
begin
intro sp,
have scard: s.card = s.card.pred +1,
have bb:= nat.eq_zero_or_eq_succ_pred s.card,
cases bb,
-- bb in "or"
rw bb at sp,
cases sp,
exact bb,
rw finset.card_eq_succ at scard,
rcases scard with ⟨ a,t,x ⟩ ,
use [a,t],
--tauto,
rcases x with ⟨ x1,x2,x3⟩ ,
-- x in "and"
-- rcases split more than two assumptions
split,
exact x3,
split,
exact x1,
exact x2,
end

example : ∀ f : fin 5 → fin 2, ∃ a b c, (a ≠ b) ∧ (b ≠ c) ∧ (a ≠ c) ∧ (f a = f b) ∧ (f b = f c) :=
begin
intros,
have inq : fintype.card (fin 2) • 2 < ↑(fintype.card (fin 5)),
simp,
linarith,
have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f inq,
cases fh' with y fh'',

sorry
end

