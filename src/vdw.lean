import data.finset.card
import data.fintype.basic
import algebra.big_operators.basic
import data.fin.basic
import combinatorics.pigeonhole
import tactic

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

example: ∀ f : fin 5 → fin 2, ∃ a b c, (a ≠ b) ∧ (b ≠ c) ∧ (a ≠ c) ∧ (f a = f b) ∧ (f b = f c):=
begin
intros,
have inq : fintype.card (fin 2) • 2 < ↑(fintype.card (fin 5)) ,
{simp,linarith,},

have fh' := fintype.exists_lt_card_fiber_of_mul_lt_card f inq,
cases fh' with y fh'',
have fh''_1:(finset.filter (λ (x : fin 5), f x = y) finset.univ).card>0,
have zero2:2>0,
simp,
--apply nat.lt_trans zero2,
--assumption,
exact lt_trans zero2 fh'',
have pickone:= pick_one fh''_1,
rcases pickone with ⟨a,t,tcard,anotint,insert⟩,
have tcard1:1<t.card,
rw tcard,
--have one2:1<2,
--simp,
exact nat.lt_pred_iff.mpr fh'',
have tcard0:0<t.card,
have zero1:0<1,
simp,
exact lt_trans zero1 tcard1,
have pickone2:=pick_one tcard0,
rcases pickone2 with ⟨b,t2,t2card,bnotin2,insert2⟩,
have t2card0:0<t2.card,
rw t2card,
--rw tcard,
exact nat.lt_pred_iff.mpr tcard1, -- is this right
have pickone3:=pick_one t2card0,
rcases pickone3 with ⟨c,t3,t3card,cnotin3,insert3⟩,
use [a,b,c],
repeat {split},
by_contra,
rw h at anotint,
rw ← insert2 at anotint,
simp at anotint,
assumption,
by_contra,
rw h at bnotin2,
rw ← insert3 at bnotin2,
simp at bnotin2,
assumption,
by_contra,
have fact1:=finset.mem_insert_self c t3,
rw insert3 at fact1,
have fact2:=finset.subset_insert b t2,
rw insert2 at fact2,
have fact3 := finset.mem_of_subset fact2 fact1,
rw ← h at fact3,
--cases anotint fact3,
contradiction,
have amember :=  finset.mem_insert_self a t,
rw insert at amember,
simp at amember,
--have b_in_t :=  finset.mem_insert_self b t2,
--rw insert2 at b_in_t,
have bmember :=  finset.mem_insert_self b t,
have cmember :=  finset.mem_insert_self c t,

sorry

end
