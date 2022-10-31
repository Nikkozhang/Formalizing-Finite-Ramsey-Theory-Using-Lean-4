import combinatorics.simple_graph.basic
import combinatorics.simple_graph.clique

def k6:=complete_graph(fin 6)

--#check (k6.neighbor_finset 0).card

#check k6.is_clique{1,2}

def arrowing {α: Type} (G: simple_graph α )(s t : ℕ ):Prop := 
  (∃ S: finset α , S.card = s ∧ G.is_clique S) ∨ (∃ T: finset α , T.card = s ∧ Gᶜ .is_clique T) 

theorem R33: ∀ G: simple_graph(fin 6), arrowing G 3 3 :=
begin

end
