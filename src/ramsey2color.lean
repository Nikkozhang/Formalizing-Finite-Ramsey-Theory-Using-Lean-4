import combinatorics.pigeonhole
import combinatorics.simple_graph.clique
import tactic.fin_cases
import data.finset

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

def Ramsey_prop (N s t : ℕ) : Prop := ∀ f : sym2 (fin N) → fin 2, 
(∃ S, (graph_at_color (complete_graph (fin N)) f 0).is_n_clique s S) 
∨ (∃ T, (graph_at_color (complete_graph (fin N)) f 1).is_n_clique t T)

lemma Ramsey_monotone : ∀ {N s t}, Ramsey_prop N s t → ∀ {M}, N ≤ M 
→ Ramsey_prop M s t :=
begin
unfold Ramsey_prop,
intros _ _ _ R _ NleqM _,
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

def Ramsey_symm : ∀ N s t, Ramsey_prop N s t → Ramsey_prop N t s :=
begin
unfold Ramsey_prop,
intros _ _ _ R _,
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
end

theorem friendship_upper_bound : Ramsey_prop 6 3 3 := sorry

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
rw finset.card_insert_of_not_mem,
rw finset.card_insert_of_not_mem,
tauto,
tauto,
simp,
by_contra,
cases h,
tauto,
tauto,

unfold Ramsey_prop,
simp,
let f : sym2 (fin k) → fin 2 := λ e, 1,
use f,
by_contra,
cases h,
rcases h with ⟨ S, S_prop ⟩,

rw simple_graph.is_n_clique_iff at S_prop,
rcases S_prop with ⟨SisClique,S_card⟩,
unfold graph_at_color at SisClique,
simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at SisClique,
rw finset.card_eq_two at S_card,
rcases S_card with ⟨x,y,⟨xneqy,Sxy⟩ ⟩  ,
have xins : x ∈ S := by rw Sxy;simp,
have yins : y ∈ S := by rw Sxy;simp,
exact SisClique xins yins xneqy,
--pick 2 from (finset.filter (λx y: fin k, x ≠ y ∧ x ∈ S ∧ y ∈ S ) finset.univ) with x y,

rcases h with ⟨T,TisClique⟩ ,
have kcard : fintype.card (fin k) < k.succ := sorry,
have cliquefree : (graph_at_color (complete_graph (fin k)) f 1).clique_free k.succ := 
by apply simple_graph.clique_free_of_card_lt kcard,
unfold simple_graph.clique_free at cliquefree,
have Tcontra :=  cliquefree T,
contradiction,


--simp [simple_graph.is_clique_iff, set.pairwise, graph_at_color] at TisClique,

-- have S_exist_x : ∃x , x ∈ S,
-- have S_card_pos : 0 < S.card := by linarith only [S_card],
-- have S_non_empty: S.nonempty,
-- rw ← finset.card_pos,
-- exact S_card_pos,
-- apply finset.nonempty.bex S_non_empty,
--rcases S_exist_x with ⟨x,xprop⟩,
--simp [xprop, SisClique],

sorry
end

theorem friendship : Ramsey 3 3 = 6 := sorry
