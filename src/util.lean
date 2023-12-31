import combinatorics.simple_graph.degree_sum
import combinatorics.double_counting
import data.rat.floor
import tactic.fin_cases
import tactic.induction


lemma bijection_of_eq_card {α β : Type} [decidable_eq α] [decidable_eq β] : ∀ {s : finset α} {t : finset β}, s.card = t.card → ((s = ∅ ∧ t = ∅) ∨ ∃ f : ↥s → ↥t, function.bijective f) :=
begin
intro,
induction s using finset.induction with a s anotins ih,
simp,
intros t h,
left,
rw ← finset.card_eq_zero,
symmetry,
exact h,
intros _ tcard,
right,
rw (finset.card_insert_of_not_mem anotins) at tcard,
have tinsert := eq.symm tcard,
rw finset.card_eq_succ at tinsert,
rcases tinsert with ⟨b, t', bnotint', bins, tcards⟩,
cases (ih (eq.symm tcards)) with stempt fbij,
simp [stempt.right] at bins,
rw [stempt.left, ← bins],
have bobv : b ∈ t,
rw ← bins,
exact finset.mem_singleton_self b,
lift b to t using bobv,
rw bins,
use (λ x : ↥{a}, b),
split,
intros _ _ fa₁a₂,
apply subtype.ext,
have a₁prop := a₁.prop,
have a₂prop := a₂.prop,
simp at a₁prop a₂prop,
simp [a₁prop, a₂prop],
intros b',
use a,
simp,
simp,
apply subtype.ext,
have b'prop := b'.prop,
simp [← bins] at b'prop,
simp [b'prop],
rcases fbij with ⟨f, fbij⟩,
have bint : b ∈ t := by rw ← bins; simp,
have fhelper : ∀ x, ↑(f x) ∈ t,
intros,
simp [← bins],
use (λ x, match finset.decidable_mem ↑x s with
| is_true p := ⟨f ⟨↑x, p⟩, fhelper ⟨↑x, p⟩⟩
| is_false _ := ⟨b, bint⟩
end),
split,
intros _ _ fa₁a₂,
simp at fa₁a₂,
cases (finset.decidable_mem ↑a₁ s) with a₁notins a₁ins; cases (finset.decidable_mem ↑a₂ s) with a₂notins a₂ins; simp at fa₁a₂,
have a₁a := a₁.prop,
have a₂a := a₂.prop,
simp [a₁notins, a₂notins] at a₁a a₂a,
apply subtype.ext,
simp [a₁a, a₂a],
have fa₂prop := (f ⟨↑a₂, a₂ins⟩).prop,
rw ← fa₁a₂ at fa₂prop,
contradiction,
have fa₁prop := (f ⟨↑a₁, a₁ins⟩).prop,
rw fa₁a₂ at fa₁prop,
contradiction,
have japf := fbij.left (subtype.ext fa₁a₂),
simp at japf,
apply subtype.ext,
assumption,
intros b',
have b'prop := b'.prop,
simp [← bins] at b'prop,
cases b'prop,
use a,
simp,
simp,
cases ains : (finset.decidable_mem a s),
simp [← b'prop],
contradiction,
have boysc := fbij.right ⟨↑b', b'prop⟩,
rcases boysc with ⟨a', fa'⟩,
use a',
simp,
simp,
cases (finset.decidable_mem ↑a' s),
cases h a'.prop,
simp [fa'],
end

lemma floormagic : ∀ (n m : ℕ) (q : ℚ), q < 1 → ↑n ≤ ⌊(↑m + q)⌋  → n ≤ m :=
begin
intros _ _ _ smallqat nlemfloor,
rw  int.floor_nat_add at nlemfloor,
have qflrle0 : ⌊q⌋ ≤ 0,
by_contra qflrpos,
simp at qflrpos,
rw int.floor_pos at qflrpos,
cases (lt_irrefl 1 (lt_of_le_of_lt qflrpos smallqat)),
have mqlem := int.add_le_add_left qflrle0 ↑m,
have nleqm := int.le_trans nlemfloor mqlem,
simp at nleqm,
exact nleqm,
end

lemma xor_even_le_implies_lt : ∀ {m n : ℕ}, xor (even m) (even n) → m ≤ n → m < n :=
begin
intros _ _ xoreven mlen,
cases xoreven; {
rw le_iff_lt_or_eq at mlen,
cases mlen,
exact mlen,
simp [mlen] at xoreven,
cases xoreven }
end

lemma notc : ∀ {c x y : fin 2}, x ≠ c → y ≠ c → x = y :=
begin
intros c x y h₁ h₂,
fin_cases c,

fin_cases x using h_1,
contradiction,
fin_cases y using h_2,
contradiction,

fin_cases x using h_1,
fin_cases y using h_2,
contradiction,
contradiction,
end

lemma missing_pigeonhole {α β : Type} [decidable_eq α] [linear_ordered_semiring β] : ∀ {s : finset α}, finset.nonempty s → ∀ {f g : α → β}, s.sum f ≤ s.sum g → ∃ a : α, a ∈ s ∧ f a ≤ g a :=
begin
intros _ sne _ _ fgsum,
induction s using finset.induction with a t anotint ih,
cases sne,
cases sne_h,
cases finset.eq_empty_or_nonempty t,
simp [h] at fgsum ⊢,
assumption,
rw (finset.sum_insert anotint) at fgsum,
rw (finset.sum_insert anotint) at fgsum,
simp at fgsum,
cases (le_or_lt (f a) (g a)) with fleg gltf,
use a,
simp,
assumption,
cases (le_or_lt (t.sum f) (t.sum g)) with tfleg tgltf,
rcases (ih h tfleg) with ⟨b, bint, bprop⟩,
use b,
simp,
tauto,
cases (not_le_of_lt (add_lt_add gltf tgltf) fgsum)
end

lemma halflt1 : rat.mk_pnat 1 2 < 1 :=
begin
simp [rat.lt_one_iff_num_lt_denom, rat.mk_pnat_num,
rat.mk_pnat_denom];
linarith,
end

lemma dblcnt (M' N': ℕ) (f : sym2 (fin (M'+ N').succ) → fin 2): ∀ c : fin 2, 2 * (finset.filter (λ (e : sym2 (fin (M' + N').succ)), f e = c) (⊤ : simple_graph (fin (M' + N').succ)).edge_finset).card = (finset.filter (λ (x : (⊤ : simple_graph (fin (M' + N').succ)).dart), f ⟦x.to_prod⟧ = c) finset.univ).card:=
begin
let r: sym2 (fin (M' + N').succ) → (⊤ : simple_graph (fin (M' + N').succ)).dart → Prop 
:= λ x y, x = ⟦y.to_prod⟧ ∨ x = ⟦y.to_prod.swap⟧,
intro c,
let s := finset.filter (λ (e : sym2 (fin (M' + N').succ)), f e = c) (⊤ : simple_graph (fin (M' + N').succ)).edge_finset,
let t := finset.filter (λ (x : (⊤ : simple_graph (fin (M' + N').succ)).dart), f ⟦x.to_prod⟧ = c) finset.univ, 
have hm : ∀ (a : sym2 (fin (M' + N').succ)), a ∈ s
→ (finset.bipartite_above r t a).card = 2,
intros a ains,
simp [finset.bipartite_above,r, finset.card_eq_two ],
simp[simple_graph.mem_edge_set, ←  simple_graph.complete_graph_eq_top,complete_graph] at ains,
cases ains,

use a.out,
have temp : a = ⟦(a.out.1, a.out.2)⟧ := by simp,
rw [temp] at ains_left,
exact ains_left,

use a.out.swap,
have temp : a = ⟦(a.out.2, a.out.1)⟧,
rw[ sym2.eq_swap], simp,
rw [temp] at ains_left,
exact ains_left,

simp,

split,
by_contra,
simp[prod.ext_iff] at h,
cases h,
have temp : a = ⟦(a.out.1, a.out.2)⟧ := by simp,
rw [temp] at ains_left,
simp[h_left] at ains_left,
exact ains_left,

simp[finset.subset.antisymm_iff,finset.subset_iff],
split, 
intros _ _ aeqx, 
cases' quotient.mk_out (x.to_prod.1, x.to_prod.2),
left,
apply simple_graph.dart.ext,
simp[aeqx],
have temp: x.to_prod = (x.to_prod.1, x.to_prod.2) := by simp,
rw[temp],
exact cases_eq,
right,
apply simple_graph.dart.ext,
simp[aeqx],
have temp: x.to_prod = (x.to_prod.2, x.to_prod.1).swap := by simp[prod.swap_prod_mk],
rw[temp,prod.swap_inj],
rw[← temp],
simp[cases_eq],

exact ains_right,

have hn : ∀ (b : (⊤ : simple_graph (fin (M' + N').succ)).dart), b ∈ t
→ (finset.bipartite_below r s b).card = 1,
intros _ bint,
simp [finset.bipartite_below, r, finset.card_eq_one],
simp[←  simple_graph.complete_graph_eq_top,complete_graph] at bint,
use b.edge,
simp[finset.subset.antisymm_iff,finset.subset_iff,simple_graph.mem_edge_set,←  simple_graph.complete_graph_eq_top,complete_graph],
have to_edge : b.edge = ⟦b.to_prod⟧ := by simp[simple_graph.dart_edge_eq_mk_iff],
split,
intros x _ _ xeqb,
rw[xeqb],
simp[to_edge],
split,
split,
have temp:= simple_graph.dart.edge_mem b,
simp[←  simple_graph.complete_graph_eq_top,complete_graph] at temp,
exact temp,
simp[to_edge,bint],
exact to_edge,
have temp := finset.card_mul_eq_card_mul r hm hn,
simp[mul_one (t.card)] at temp,
simp[← s,← t, ← temp,mul_comm],
end

lemma univexpand : (@finset.univ (fin 2) _) = {0, 1} :=
begin
symmetry,
rw finset.eq_univ_iff_forall,
intros,
fin_cases x; simp,
end