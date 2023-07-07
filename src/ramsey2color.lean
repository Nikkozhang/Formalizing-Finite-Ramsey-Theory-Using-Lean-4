import combinatorics.pigeonhole
import combinatorics.simple_graph.clique

import .pick_tactic

def graph_at_color {N : ℕ} (G : simple_graph (fin N)) (ϕ : sym2 (fin N) → fin 2) (i : fin 2) : simple_graph (fin N) := { adj := λ u v, (G.adj u v) ∧ (ϕ ⟦(u, v)⟧ = i), symm := sorry, loopless := sorry }

def Ramsey_prop (N s t : ℕ) : Prop := ∀ f : sym2 (fin N) → fin 2, ∃ S, (graph_at_color (complete_graph (fin N)) f (fin.mk 0 sorry)).is_n_clique s S ∨ ∃ T, (graph_at_color (complete_graph (fin N)) f (fin.mk 1 sorry)).is_n_clique t T

theorem friendship_upper_bound : Ramsey_prop 6 3 3 := sorry

noncomputable def Ramsey (s t : ℕ) : ℕ := Inf { N : ℕ | Ramsey_prop N s t }

theorem frienship : Ramsey 3 3 = 6 := sorry
