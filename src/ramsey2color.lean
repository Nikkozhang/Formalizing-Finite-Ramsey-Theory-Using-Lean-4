import combinatorics.pigeonhole
import combinatorics.simple_graph.clique
import data.fin.vec_notation
import data.rat.floor
import algebra.order.floor

import tactic.fin_cases
import tactic.induction

import .pick_tactic

def graph_at_color {N : ℕ} (G : simple_graph (fin N)) (ϕ : sym2 (fin N) → fin 2)
 (i : fin 2): simple_graph (fin N) := {
  adj := λ u v, (G.adj u v) ∧ (ϕ ⟦(u, v)⟧ = i),
  symm := begin
  unfold symmetric,
  intros _ _ h,
  rcases h with ⟨Gxy,ϕxy⟩, 
  split,
  apply G.adj_symm Gxy,
  rw sym2.eq_swap,
  exact ϕxy,
  end,
  loopless := begin
  unfold irreflexive,
  intro _,
  simp,
  end,
 }

def Ramsey_prop (N s t : ℕ) : Prop := N > 0 ∧
∀ f : sym2 (fin N) → fin 2, 
(∃ S, (graph_at_color (complete_graph (fin N)) f 0).is_n_clique s S) 
∨ (∃ T, (graph_at_color (complete_graph (fin N)) f 1).is_n_clique t T)

lemma Ramsey_monotone : ∀ {N s t}, Ramsey_prop N s t → ∀ {M}, N ≤ M 
→ Ramsey_prop M s t :=
begin
unfold Ramsey_prop,
intros _ _ _ R _ NleqM,
rcases R with ⟨ Ngt0, R⟩,
split, 
linarith only[Ngt0, NleqM],
intros,
let f' : sym2 (fin N) → fin 2 := λ e, f (sym2.map (fin.cast_le NleqM) e),
cases (R f'),
rcases h with ⟨S, Sprop⟩,
cases Sprop,
left,
use (finset.map (fin.cast_le NleqM).to_embedding S),
have cliqueproof : (graph_at_color (complete_graph (fin M)) f 0).is_clique 
(finset.map (fin.cast_le NleqM).to_embedding S),
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Sprop_clique ⊢,
intros x xinS y yinS xneqy,
split,
exact xneqy,
have fxy := (Sprop_clique xinS yinS xneqy).right,
exact fxy,
rw ← (finset.card_map (fin.cast_le NleqM).to_embedding) at Sprop_card_eq,
use { clique := cliqueproof, card_eq := Sprop_card_eq },

rcases h with ⟨T, Tprop⟩,
cases Tprop,
right,
use (finset.map (fin.cast_le NleqM).to_embedding T),
have cliqueproof : (graph_at_color (complete_graph (fin M)) f 1).is_clique 
(finset.map (fin.cast_le NleqM).to_embedding T),
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Tprop_clique ⊢,
intros x xinT y yinT xneqy,
split,
exact xneqy,
have fxy := (Tprop_clique xinT yinT xneqy).right,
exact fxy,
rw ← (finset.card_map (fin.cast_le NleqM).to_embedding) at Tprop_card_eq,
use { clique := cliqueproof, card_eq := Tprop_card_eq },
end


theorem Ramsey_prop_symm : ∀ N s t : ℕ, Ramsey_prop N s t ↔ Ramsey_prop N t s :=
begin
have helper : ∀ N s t, Ramsey_prop N s t → Ramsey_prop N t s,
unfold Ramsey_prop,
intros _ _ _ R,
rcases R with ⟨Ngt0, R⟩,
split,
exact Ngt0,
intro,
let f' : sym2 (fin N) → fin 2 := λ e, if f e = 0 then 1 else 0,
cases (R f'),
rcases h with ⟨S, ⟨Sclique, Scard⟩⟩,
right,
use S,
have cliqueproof : (graph_at_color (complete_graph (fin N)) f 1).is_clique S,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Sclique ⊢,
intros _ xinS _ yinS xneqy,
split,
exact xneqy,
have fxyneq0 := (Sclique xinS yinS xneqy).right,
let e := f⟦(x, y)⟧, change e = 1,
fin_cases e,contradiction,assumption,
rw simple_graph.is_n_clique_iff,
split,assumption, assumption,

rcases h with ⟨T, ⟨Tclique, Tcard⟩⟩,
left,
use T,
have cliqueproof : (graph_at_color (complete_graph (fin N)) f 0).is_clique T,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Tclique ⊢,
intros _ xinT _ yinT xneqy,
split,
exact xneqy,
have fxyneq1 := (Tclique xinT yinT xneqy).right,
by_contra, 
apply fxyneq1 h,
rw simple_graph.is_n_clique_iff,
split,assumption, assumption,

intros,
use ⟨helper N s t, helper N t s⟩,
end

theorem friendship_upper_bound : Ramsey_prop 6 3 3 :=
begin
unfold Ramsey_prop,
split,
simp,
intros,
let g : ((complete_graph (fin 6)).neighbor_set 0) → fin 2 := λ x, f ⟦(0, x)⟧,
have ghyp : fintype.card (fin 2) • 2 < fintype.card ↥((complete_graph (fin 6)).neighbor_set 0),
simp,
linarith,
have ghyp := fintype.exists_lt_card_fiber_of_mul_lt_card g ghyp,
rcases ghyp with ⟨c, chyp⟩,
pick 3 from (finset.filter (λ (x : ↥((complete_graph (fin 6)).neighbor_set 0)), g x = c) finset.univ) with x y z,
simp [g] at x.elem y.elem z.elem,
cases nat.eq_zero_or_pos (finset.filter (λ e, e = c) (insert (f ⟦(↑x, ↑y)⟧) (insert (f ⟦(↑y, ↑z)⟧) (insert (f ⟦(↑x, ↑z)⟧) (∅:(finset (fin 2))))))).card,
rotate,
pick 1 from (finset.filter (λ (e : fin 2), e = c) {f ⟦(↑x, ↑y)⟧, f ⟦(↑y, ↑z)⟧, f ⟦(↑x, ↑z)⟧}) with e,
simp at e.elem,
rcases e.elem with ⟨eval, ecolor⟩,
have c0 : ∃ a b : (fin 6), (graph_at_color (complete_graph (fin 6)) f c).is_n_clique 3 {0, a, b},
rcases eval with eval | ⟨eval | eval⟩; rw eval at ecolor,

use [↑x, ↑y],
simp [graph_at_color, complete_graph],
constructor,
simp [simple_graph.is_clique_iff, set.pairwise],
rw [@sym2.eq_swap (fin 6) ↑x 0, @sym2.eq_swap (fin 6) ↑y 0, @sym2.eq_swap (fin 6) ↑y ↑x],
tauto,
rw finset.card_eq_three,
use [0, ↑x, ↑y],
simp,
split,
exact x.prop,
split,
exact y.prop,
intro xeqy,
change ↑x < ↑y at x.lt.y,
simp [xeqy] at x.lt.y,
exact x.lt.y,

use [↑y, ↑z],
simp [graph_at_color, complete_graph],
constructor,
simp [simple_graph.is_clique_iff, set.pairwise],
rw [@sym2.eq_swap (fin 6) ↑y 0, @sym2.eq_swap (fin 6) ↑z 0, @sym2.eq_swap (fin 6) ↑z ↑y],
tauto,
rw finset.card_eq_three,
use [0, ↑y, ↑z],
simp,
split,
exact y.prop,
split,
exact z.prop,
intro yeqz,
change ↑y < ↑z at y.lt.z,
simp [yeqz] at y.lt.z,
exact y.lt.z,

use [↑x, ↑z],
simp [graph_at_color, complete_graph],
constructor,
simp [simple_graph.is_clique_iff, set.pairwise],
rw [@sym2.eq_swap (fin 6) ↑x 0, @sym2.eq_swap (fin 6) ↑z 0, @sym2.eq_swap (fin 6) ↑z ↑x],
tauto,
rw finset.card_eq_three,
use [0, ↑x, ↑z],
simp,
split,
exact x.prop,
split,
exact z.prop,
intro xeqz,
have x.lt.z : x < z,
transitivity y,
exact x.lt.y,
exact y.lt.z,
change ↑x < ↑z at x.lt.z,
simp [xeqz] at x.lt.z,
exact x.lt.z,

rcases c0 with ⟨a, b, clique0ab⟩,
fin_cases c,

left,
use {0, a, b},
assumption,

right,
use {0, a, b},
assumption,

simp at h,
rw finset.filter_eq_empty_iff {f ⟦(↑x, ↑y)⟧, f ⟦(↑y, ↑z)⟧, f ⟦(↑x, ↑z)⟧} at h,
simp at h,
rcases h with ⟨fxyneqc, fyzneqc, fxzneqc⟩,

have notc : ∀ {c : fin 2}, ∀ {x y : sym2(fin 6)}, f x ≠ c → f y ≠ c → f x = f y,
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


have temp1: f ⟦(↑x, ↑y)⟧ = f ⟦(↑y, ↑z)⟧ := notc fxyneqc fyzneqc,
have temp2: f ⟦(↑x, ↑y)⟧ = f ⟦(↑x, ↑z)⟧:= notc fxyneqc fxzneqc,
have d0 :(graph_at_color (complete_graph (fin 6)) f  (f ⟦(↑x, ↑y)⟧)) .is_n_clique 3 {↑x, ↑ y, ↑ z},
simp [graph_at_color, complete_graph],
constructor,
simp [simple_graph.is_clique_iff, set.pairwise],
rw [@sym2.eq_swap (fin 6) ↑y x, @sym2.eq_swap (fin 6) ↑z y, @sym2.eq_swap (fin 6) ↑z ↑x],
tauto,
rw finset.card_eq_three,
use [↑x, ↑y, ↑z],
simp,
split,

intro xeqy,
change ↑x < ↑y at x.lt.y,
simp [xeqy] at x.lt.y,
exact x.lt.y,

split,

intro xeqz,
have x.lt.z : x < z,
transitivity y,
exact x.lt.y,
exact y.lt.z,
change ↑x < ↑z at x.lt.z,
simp [xeqz] at x.lt.z,
exact x.lt.z,

intro yeqz,
change ↑y < ↑z at y.lt.z,
simp [yeqz] at y.lt.z,
exact y.lt.z,

let d := f ⟦(↑x, ↑y)⟧,
fin_cases d using hd; simp [← d, hd] at d0,

left,
use {↑x,↑y,↑z},
assumption,

right,
use {↑x,↑y,↑z},
assumption,

end

noncomputable def Ramsey (s t : ℕ) : ℕ := Inf { N : ℕ | Ramsey_prop N s t }

theorem Ramsey2 : ∀ k : ℕ, Ramsey 2 k.succ = k.succ :=
begin
intros,
unfold Ramsey,
have Ramsey2_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey_prop N 2 k.succ } 
→ M₂ ∈ { N : ℕ | Ramsey_prop N 2 k.succ },
intros M₁ M₂ M₁leM₂,
simp,
intro M₁Ramsey,
apply Ramsey_monotone M₁Ramsey M₁leM₂,
rewrite nat.Inf_upward_closed_eq_succ_iff (Ramsey2_monotone),
simp,
split,
unfold Ramsey_prop,
split,
simp,
intros,
cases finset.eq_empty_or_nonempty (finset.filter 
(λ (x : sym2 (fin k.succ)), (x.out.1 ≠ x.out.2) ∧ f x = 0) finset.univ),
rw finset.filter_eq_empty_iff at h,
simp at h,
right,
use finset.univ,
have cliqueproof : (graph_at_color (complete_graph (fin (k + 1))) f 1).is_clique
 (fintype.elems (fin k.succ)),
rw simple_graph.is_clique_iff,
simp [set.pairwise, graph_at_color],
intros x xin y yin xneqy,
split,
exact xneqy,
let fxy := f ⟦(x, y)⟧,
fin_cases fxy using fxyval,
simp [fxy] at fxyval,
cases (fin.decidable_eq (k + 1) ⟦(x, y)⟧.out.fst  ⟦(x, y)⟧.out.snd) with xyoutneq xyouteq,
cases h ⟦(x, y)⟧ xyoutneq fxyval,
rw ← sym2.is_diag_iff_proj_eq at xyouteq,
simp at xyouteq,
contradiction,
simp [← fxy, fxyval],
have cardproof : (fintype.elems (fin k.succ)).card = k.succ,
change finset.univ.card = k.succ,
simp,
use { clique := cliqueproof, card_eq := cardproof },
rw finset.filter_nonempty_iff at h,
rcases h with ⟨e, ein, ⟨fxynoloop, fe0⟩⟩,
left,
use (insert e.out.1 (insert e.out.2 finset.empty)),
have cliqueproof : (graph_at_color (complete_graph (fin (k + 1))) f 0).is_clique 
(insert e.out.fst (insert e.out.snd ∅)),
rw simple_graph.is_clique_iff,
simp [set.pairwise, graph_at_color],
split,
intro h,
split; assumption,
intro h,
rw [sym2.eq_swap, prod.mk.eta, e.out_eq],
split; assumption,
rw simple_graph.is_n_clique_iff,
simp,
split,
exact cliqueproof,
rw finset.card_eq_two,
use [(quotient.out e).fst, (quotient.out e).snd],
tauto,
unfold Ramsey_prop,
simp,
intro,
let f : sym2 (fin k) → fin 2 := λ e, 1,
use f,
intro h,
cases h,
rcases h with ⟨ S, S_prop ⟩,

rw simple_graph.is_n_clique_iff at S_prop,
rcases S_prop with ⟨SisClique,S_card⟩,
unfold graph_at_color at SisClique,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at SisClique,
rw finset.card_eq_two at S_card,
rcases S_card with ⟨x,y,⟨xneqy,Sxy⟩ ⟩  ,
have xins : x ∈ S := by rw Sxy; simp,
have yins : y ∈ S := by rw Sxy; simp,
exact SisClique xins yins xneqy,

rcases h with ⟨T,TisClique⟩,
have kcard : fintype.card (fin k) < k.succ := by simp; apply nat.le_refl,
have cliquefree : (graph_at_color (complete_graph (fin k)) f 1).clique_free k.succ := 
by apply simple_graph.clique_free_of_card_lt kcard,
unfold simple_graph.clique_free at cliquefree,
have Tcontra :=  cliquefree T,
contradiction,
end

lemma missing_pigeonhole {α : Type} [decidable_eq α] : ∀ {s : finset α}, finset.nonempty s → ∀ {f g : α → ℚ}, s.sum f ≤ s.sum g → ∃ a : α, a ∈ s ∧ f a ≤ g a :=
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
exact nleqm
end

theorem Ramsey1_prop : ∀ N k : ℕ, Ramsey_prop N.succ 1 k :=
begin
intros,
unfold Ramsey_prop,
simp,
intros,
left,
use {0},
constructor,
simp [simple_graph.is_clique_iff, set.pairwise],
simp
end

theorem Ramsey1 : ∀ k : ℕ, Ramsey 1 k.succ = 1 :=
begin
intro,
unfold Ramsey,
have Ramsey1_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey_prop N 1 k.succ } 
→ M₂ ∈ { N : ℕ | Ramsey_prop N 1 k.succ },
intros M₁ M₂ M₁leM₂,
simp,
intro M₁Ramsey,
apply Ramsey_monotone M₁Ramsey M₁leM₂,
rewrite nat.Inf_upward_closed_eq_succ_iff (Ramsey1_monotone),
simp,
split,
apply Ramsey1_prop 0 k.succ,
unfold Ramsey_prop,
simp,
end

theorem Ramsey_prop_ineq : ∀ M N s t : ℕ, Ramsey_prop M s.succ t.succ.succ → Ramsey_prop N s.succ.succ t.succ → Ramsey_prop (M + N) s.succ.succ t.succ.succ :=
begin
intros _ _ _ _ RamseyM RamseyN,
have NMpos : M + N > 0 := by simp [nat.add_lt_add RamseyM.left RamseyN.left],
unfold Ramsey_prop,
split,
assumption,
intro,
rcases (nat.exists_eq_succ_of_ne_zero (ne.symm (ne_of_lt NMpos.lt))) with ⟨NM, NMprop⟩,
haveI finNMzero : has_zero (fin (M + N)),
rw NMprop,
apply fin.has_zero,
let g : fin 2 → ℚ := λ x, (finset.filter (λ y, f ⟦(0, y)⟧ = x) ((complete_graph (fin (M + N))).neighbor_finset 0)).card,
let h : fin 2 → ℚ := ![↑M - rat.mk 1 2, ↑N - rat.mk 1 2],
have hgsum : finset.univ.sum h = finset.univ.sum g,
have univexpand : finset.univ = (insert (fin.mk 1 _) (insert (fin.mk 0 _) (∅:(finset (fin 2))))); try { simp },
symmetry,
rw finset.eq_univ_iff_forall,
intros,
fin_cases x; simp,
rw univexpand,
simp [h, g],
have temp1:  ↑N - rat.mk 1 2 + (↑M - rat.mk 1 2) = 
↑N + ↑M - (rat.mk 1 2 + rat.mk 1 2 ):= by linarith,
have temp2 : rat.mk 1 2 + rat.mk 1 2  = 1,
simp [rat.add_def],
change rat.mk 4 4 = 1,
simp [← rat.mk_one_one, rat.mk_eq]; simp,
simp [temp1, temp2],
rcases (nat.exists_eq_succ_of_ne_zero (ne_of_gt NMpos.lt)) with ⟨O, Oprop⟩,
have filterdisj : disjoint (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1)
            ((complete_graph (fin (M + N))).neighbor_finset 0)) (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0)
            ((complete_graph (fin (M + N))).neighbor_finset 0)),
rw finset.disjoint_iff_ne,
intros _ ainS _ binT,
simp at ainS binT,
intro aeqb,
rw aeqb at ainS,
cases eq.trans (eq.symm binT.right) ainS.right,
rw [rat.coe_nat_eq_mk (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1)
            ((complete_graph (fin (M + N))).neighbor_finset 0)).card, rat.coe_nat_eq_mk (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0)
            ((complete_graph (fin (M + N))).neighbor_finset 0)).card],
simp,
rw ← int.coe_nat_add,
rw ← finset.card_union_eq filterdisj,
have seteq : (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1)
              ((complete_graph (fin (M + N))).neighbor_finset 0) ∪
            finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0)
              ((complete_graph (fin (M + N))).neighbor_finset 0))=((complete_graph (fin (M + N))).neighbor_finset 0),
apply subset_antisymm; unfold has_subset.subset,
intros _ ainset,
simp at ainset ⊢,
cases ainset with aprop aprop; exact aprop.left,
intros _ ainset,
simp at ainset ⊢,
let fa := f ⟦(0, a)⟧,
fin_cases fa; simp [← fa, this, ainset],
rw [seteq, simple_graph.neighbor_finset_eq_filter],
simp [complete_graph, finset.filter_ne, rat.coe_nat_eq_mk N, rat.coe_nat_eq_mk M],
rw [← int.coe_nat_add N M,  nat.add_comm N M, ← rat.mk_one_one, rat.sub_def (ne_of_gt int.zero_lt_one) (ne_of_gt int.zero_lt_one)],
simp [Oprop],
have mp := missing_pigeonhole (exists.intro (0 : fin 2) _) (le_of_eq hgsum); simp,
rcases mp with ⟨a, ainuniv, gha⟩,
fin_cases a,
simp [g, h] at gha,
have MtoZ : (↑M:ℚ) = (↑M:ℤ) := by simp,
rw MtoZ at gha,
rw ← rat.le_floor at gha,
have halflt1 : rat.mk_pnat 1 2 < 1 :=
by simp [rat.lt_one_iff_num_lt_denom, rat.mk_pnat_num,
rat.mk_pnat_denom];
linarith,
have MleqNeighbor0 := floormagic M ((finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0)
             ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (rat.mk_nat 1 2) halflt1 gha,
have RamseySub := Ramsey_monotone RamseyM MleqNeighbor0,
have cardeq : (finset.card (@finset.univ (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) _)) = (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card := by simp,
have ftrans := bijection_of_eq_card cardeq,
simp at ftrans,
cases ftrans,
have absurd := (finset.card_eq_zero.mpr ftrans.right),
simp [absurd] at MleqNeighbor0,
unfold Ramsey_prop at RamseyM,
simp [MleqNeighbor0] at RamseyM,
cases RamseyM,
rcases ftrans with ⟨ftrans, ftransbij⟩,
have ftransembinj : function.injective ((λ x, ↑(ftrans ⟨x, finset.mem_univ x⟩)):(fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card → fin (M + N))),
intros _ _ fa₁a₂,
simp at fa₁a₂,
have a₁a₂eq := ftransbij.left (subtype.ext fa₁a₂),
simp at a₁a₂eq,
exact a₁a₂eq,
let ftransemb : function.embedding (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (fin (M + N)) := ⟨λ x, ↑(ftrans ⟨x, finset.mem_univ x⟩), ftransembinj⟩,
unfold Ramsey_prop at RamseySub,
cases RamseySub.right (λ e, f ⟦(ftrans ⟨e.out.1, _⟩, ftrans ⟨e.out.2, _⟩)⟧) with clique clique; continue { clear RamseySub, simp },

rcases clique with ⟨S, Sclique⟩,
left,
use (insert 0 (S.map ftransemb)),
constructor,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color],
split,
intros _ ainS ftransa,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
exact ftransaprop,
intros _ ainS,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
split,
rw [sym2.eq_swap],
intros ftransa,
simp [ftransa, ftransaprop.right],
intros b binS ftransneq,
simp [ftransneq],
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Sclique,
cases (fin.decidable_eq _ a b) with aneqb aeqb,
have abedge := Sclique.clique ainS binS aneqb,
simp at abedge,
cases' quotient.mk_out (a, b),
rw ← cases_eq at abedge,
simp at abedge,
exact abedge.right,
rw ← cases_eq at abedge,
simp at abedge,
rw [sym2.eq_swap],
exact abedge.right,
rw ← @subtype.mk_eq_mk (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (λ x, x ∈ finset.univ) a (finset.mem_univ a) b (finset.mem_univ b) at aeqb,
have ftranseq := congr_arg ftrans aeqb,
rw subtype.ext_iff at ftranseq,
cases ftransneq ftranseq,
have znotinSmap : finNMzero.zero ∉ (S.map ftransemb),
simp [ftransemb],
intros a aprop ftransa,
have ftransat := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp [ftransa] at ftransat,
exact ftransat,
rw finset.card_insert_of_not_mem znotinSmap,
simp [Sclique.card_eq],

rcases clique with ⟨T, Tclique⟩,
right,
use (T.map ftransemb),
constructor,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color],
intros _ ainT b binT ftransneq,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
simp [ftransneq],
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Tclique,
cases (fin.decidable_eq _ a b) with aneqb aeqb,
have abedge := Tclique.clique ainT binT aneqb,
simp at abedge,
cases' quotient.mk_out (a, b),
rw ← cases_eq at abedge,
simp at abedge,
exact abedge.right,
rw ← cases_eq at abedge,
simp at abedge,
rw [sym2.eq_swap],
exact abedge.right,
rw ← @subtype.mk_eq_mk (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 0) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (λ x, x ∈ finset.univ) a (finset.mem_univ a) b (finset.mem_univ b) at aeqb,
have ftranseq := congr_arg ftrans aeqb,
rw subtype.ext_iff at ftranseq,
cases ftransneq ftranseq,
simp [Tclique.card_eq],

simp [g, h] at gha,
have NtoZ : (↑N:ℚ) = (↑N:ℤ) := by simp,
rw NtoZ at gha,
rw ← rat.le_floor at gha,
have halflt1 : rat.mk_pnat 1 2 < 1 :=
by simp [rat.lt_one_iff_num_lt_denom, rat.mk_pnat_num,
rat.mk_pnat_denom];
linarith,
have NleqNeighbor0 := floormagic N ((finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1)
             ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (rat.mk_nat 1 2) halflt1 gha,
have RamseySub := Ramsey_monotone RamseyN NleqNeighbor0,
have cardeq : (finset.card (@finset.univ (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) _)) = (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card := by simp,
have ftrans := bijection_of_eq_card cardeq,
simp at ftrans,
cases ftrans,
have absurd := (finset.card_eq_zero.mpr ftrans.right),
simp [absurd] at NleqNeighbor0,
unfold Ramsey_prop at RamseyN,
simp [NleqNeighbor0] at RamseyN,
cases RamseyN,
rcases ftrans with ⟨ftrans, ftransbij⟩,
have ftransembinj : function.injective ((λ x, ↑(ftrans ⟨x, finset.mem_univ x⟩)):(fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card → fin (M + N))),
intros _ _ fa₁a₂,
simp at fa₁a₂,
have a₁a₂eq := ftransbij.left (subtype.ext fa₁a₂),
simp at a₁a₂eq,
exact a₁a₂eq,
let ftransemb : function.embedding (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (fin (M + N)) := ⟨λ x, ↑(ftrans ⟨x, finset.mem_univ x⟩), ftransembinj⟩,
unfold Ramsey_prop at RamseySub,
cases RamseySub.right (λ e, f ⟦(ftrans ⟨e.out.1, _⟩, ftrans ⟨e.out.2, _⟩)⟧) with clique clique; continue { clear RamseySub, simp },

rcases clique with ⟨S, Sclique⟩,
left,
use (S.map ftransemb),
constructor,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color],
intros _ ainS b binS ftransneq,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
simp [ftransneq],
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Sclique,
cases (fin.decidable_eq _ a b) with aneqb aeqb,
have abedge := Sclique.clique ainS binS aneqb,
simp at abedge,
cases' quotient.mk_out (a, b),
rw ← cases_eq at abedge,
simp at abedge,
exact abedge.right,
rw ← cases_eq at abedge,
simp at abedge,
rw [sym2.eq_swap],
exact abedge.right,
rw ← @subtype.mk_eq_mk (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (λ x, x ∈ finset.univ) a (finset.mem_univ a) b (finset.mem_univ b) at aeqb,
have ftranseq := congr_arg ftrans aeqb,
rw subtype.ext_iff at ftranseq,
cases ftransneq ftranseq,
simp [Sclique.card_eq],

rcases clique with ⟨T, Tclique⟩,
right,
use (insert 0 (T.map ftransemb)),
constructor,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color],
split,
intros _ ainT ftransa,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
exact ftransaprop,
intros _ ainT,
have ftransaprop := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp at ftransaprop,
split,
rw [sym2.eq_swap],
intros ftransa,
simp [ftransa, ftransaprop.right],
intros b binT ftransneq,
simp [ftransneq],
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at Tclique,
cases (fin.decidable_eq _ a b) with aneqb aeqb,
have abedge := Tclique.clique ainT binT aneqb,
simp at abedge,
cases' quotient.mk_out (a, b),
rw ← cases_eq at abedge,
simp at abedge,
exact abedge.right,
rw ← cases_eq at abedge,
simp at abedge,
rw [sym2.eq_swap],
exact abedge.right,
rw ← @subtype.mk_eq_mk (fin (finset.filter (λ (y : fin (M + N)), f ⟦(0, y)⟧ = 1) ((complete_graph (fin (M + N))).neighbor_finset 0)).card) (λ x, x ∈ finset.univ) a (finset.mem_univ a) b (finset.mem_univ b) at aeqb,
have ftranseq := congr_arg ftrans aeqb,
rw subtype.ext_iff at ftranseq,
cases ftransneq ftranseq,
have znotinTmap : finNMzero.zero ∉ (T.map ftransemb),
simp [ftransemb],
intros a aprop ftransa,
have ftransat := (ftrans ⟨a, finset.mem_univ a⟩).prop,
simp [ftransa] at ftransat,
exact ftransat,
rw finset.card_insert_of_not_mem znotinTmap,
simp [Tclique.card_eq],

end

theorem Ramsey_finite : ∀ s t : ℕ, { N : ℕ | Ramsey_prop N s.succ t.succ }.nonempty :=
begin
suffices Ramsey_finite_additive : ∀ m : ℕ, ∀ s t, m = s + t → { N : ℕ | Ramsey_prop N s.succ t.succ }.nonempty,
intros,
apply (Ramsey_finite_additive (s + t) s t),
simp,
intro,
induction m with st ih,
intros _ _ h,
have h' := eq.symm h,
simp at h',
cases h' with s0 t0,
simp [s0, t0],
use 1,
simp,
unfold Ramsey_prop,
simp,
intro,
use {0},
constructor; simp [simple_graph.is_clique_iff, set.pairwise],
intros _ _ h,
cases s; cases t,
use 1,
use 1,
simp,
apply Ramsey1_prop,
use 1,
simp,
rw Ramsey_prop_symm,
apply Ramsey1_prop,
have s1t : st = s + t.succ,
have stsuccpred := congr_arg nat.pred h,
simp at stsuccpred,
rw stsuccpred,
simp [nat.succ_add],
have st1 : st = s.succ + t,
have stsuccpred := congr_arg nat.pred h,
simp at stsuccpred,
rw stsuccpred,
simp [nat.add_succ],
have RamseyS := ih s t.succ s1t,
have RamseyT := ih s.succ t st1,
cases RamseyS with S Sprop,
cases RamseyT with T Tprop,
simp at Sprop Tprop,
use (S + T),
simp,
apply Ramsey_prop_ineq; assumption,
end

theorem Ramsey_ineq : ∀ s t : ℕ, Ramsey s.succ.succ t.succ.succ ≤ Ramsey s.succ t.succ.succ + Ramsey s.succ.succ t.succ :=
begin
intros,
have RamseyM := nat.Inf_mem (Ramsey_finite s t.succ),
have RamseyN := nat.Inf_mem (Ramsey_finite s.succ t),
simp at RamseyM RamseyN,
apply nat.Inf_le,
simp,
apply Ramsey_prop_ineq; assumption
end

theorem Ramsey_symm : ∀  s t: ℕ, Ramsey s.succ t.succ = Ramsey t.succ s.succ :=
begin
intros,
apply nat.le_antisymm,
have RamseyM := nat.Inf_mem (Ramsey_finite t s),
apply nat.Inf_le,
simp [Ramsey] at RamseyM ⊢,
rw Ramsey_prop_symm at RamseyM,
assumption,
have RamseyN := nat.Inf_mem (Ramsey_finite s t),
apply nat.Inf_le,
simp [Ramsey] at RamseyN ⊢,
rw Ramsey_prop_symm at RamseyN,
assumption
end

theorem friendship_upper_bound_alt : Ramsey 3 3 ≤ 6 :=
begin
have R33 := Ramsey_ineq 1 1,
rw [Ramsey_symm 2 1, Ramsey2] at R33,
exact R33
end

theorem friendship : Ramsey 3 3 = 6 := sorry

theorem Ramsey_binomial_coefficient_ineq : ∀ s t : ℕ, Ramsey s.succ t.succ 
≤ nat.choose (s.succ + t.succ - 2) (s.succ - 1) :=
begin
intros,

induction s with s' ihp₁ generalizing t,
simp,
rw Ramsey1 t,

induction t with t' ihp₂,
rw Ramsey_symm,
simp [Ramsey1 s'.succ],
transitivity Ramsey s'.succ t'.succ.succ + Ramsey s'.succ.succ t'.succ,
apply Ramsey_ineq s' t', 

have temp₁: Ramsey s'.succ t'.succ.succ + Ramsey s'.succ.succ t'.succ
≤ (s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ,
apply add_le_add,
exact ihp₁ t'.succ,
exact ihp₂,

have temp₂ :(s'.succ.succ + t'.succ.succ - 2).choose (s'.succ.succ - 1) = 
(s'.succ + t'.succ.succ - 2).choose s' + (s'.succ.succ + t'.succ - 2).choose s'.succ
:= by simp [nat.succ_add, nat.add_succ,nat.choose_succ_succ],
rw temp₂,
exact temp₁,
end

