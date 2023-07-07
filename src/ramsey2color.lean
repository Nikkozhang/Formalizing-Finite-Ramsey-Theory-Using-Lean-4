import combinatorics.pigeonhole
import combinatorics.simple_graph.clique
import tactic.fin_cases

import .pick_tactic

def graph_at_color {N : ℕ} (G : simple_graph (fin N)) (ϕ : sym2 (fin N) → fin 2) (i : fin 2) : simple_graph (fin N) := { adj := λ u v, (G.adj u v) ∧ (ϕ ⟦(u, v)⟧ = i), symm := sorry, loopless := sorry }

def Ramsey_prop (N s t : ℕ) : Prop := ∀ f : sym2 (fin N) → fin 2, (∃ S, (graph_at_color (complete_graph (fin N)) f 0).is_n_clique s S) ∨ (∃ T, (graph_at_color (complete_graph (fin N)) f (fin.last 1)).is_n_clique t T)

def Ramsey_monotone : ∀ N s t, Ramsey_prop N s t → ∀ M, N ≤ M → Ramsey_prop M s t := sorry

def Ramsey_symm : ∀ N s t, Ramsey_prop N s t → Ramsey_prop N t s := sorry

theorem friendship_upper_bound : Ramsey_prop 6 3 3 := sorry

noncomputable def Ramsey (s t : ℕ) : ℕ := Inf { N : ℕ | Ramsey_prop N s t }

theorem friendship : Ramsey 3 3 = 6 := sorry
