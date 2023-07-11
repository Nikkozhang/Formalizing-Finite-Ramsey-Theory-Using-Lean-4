import combinatorics.pigeonhole
import combinatorics.simple_graph.clique
import tactic.fin_cases

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

lemma Ramsey_monotone : ∀ N s t, Ramsey_prop N s t → ∀ M, N ≤ M → Ramsey_prop M s t :=
begin
unfold Ramsey_prop,
intros _ _ _ R _ NleqM _,
let f' : sym2 (fin N) → fin 2 := λ e, f (sym2.map (fin.cast_le NleqM) e),
cases (R f'),
rcases h with ⟨S, Sprop⟩,
cases Sprop,
left,
use (finset.map (fin.cast_le NleqM).to_embedding S),
have cliqueproof : (graph_at_color (complete_graph (fin M)) f 0).is_clique (finset.map (fin.cast_le NleqM).to_embedding S),
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
have cliqueproof : (graph_at_color (complete_graph (fin M)) f 1).is_clique (finset.map (fin.cast_le NleqM).to_embedding T),
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

theorem friendship : Ramsey 3 3 = 6 := sorry
