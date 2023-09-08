import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Data.Rat.Floor 
import Mathlib.Algebra.Parity

namespace Finset

def sortedList {α : Type} [LinearOrder α] (s : Finset α) : List α :=
match s.decidableNonempty with
| isTrue p =>
  let m := s.min' p;
  have := Finset.card_erase_lt_of_mem (Finset.min'_mem s p);
  m :: (sortedList (s.erase m))
| isFalse _ => []
termination_by _ => s.card

-- TODO Maybe add a [simp] lemma that sortedList ∅ = [] because any
-- simp unfolding sortedList reaches maximum recursion depth.

lemma sortedList_mem_iff {α : Type} [LinearOrder α] : ∀ (s : Finset α) (a : α), a ∈ s ↔ a ∈ s.sortedList := by
  intros s
  induction s using Finset.induction_on_min with
  | h0 =>
    unfold sortedList
    split
    next p _ => simp at p
    next => simp
  | step a t aMin ih =>
    simp
    intro b
    unfold sortedList
    split
    next nonemp _ =>
      simp
      have minIns : min' (insert a t) nonemp = a := by
        cases t using Finset.induction with
        | empty => simp
        | @insert c t _ ih =>
          rw [Finset.min'_insert a (insert c t) (Finset.insert_nonempty c t)]
          apply min_eq_right
          apply le_of_lt
          apply aMin
          apply Finset.min'_mem
      have aNotInt : a ∉ t := by
        cases Finset.decidableMem a t
        next aNotInt => exact aNotInt
        next aInt =>
          have absurd := aMin a aInt
          simp at absurd
      apply Iff.intro
      · intro bVal
        rw [minIns]
        cases bVal
        next bEqa => left; exact bEqa
        next bInt =>
          simp
          rw [Finset.erase_eq_of_not_mem aNotInt]
          right
          rw [← ih b]
          exact bInt
      · intro bVal
        cases bVal
        next bMin =>
          have bMem := Finset.min'_mem (insert a t) nonemp
          simp [← bMin] at bMem
          exact bMem
        next bRest =>
          rw [minIns] at bRest
          simp at bRest
          rw [Finset.erase_eq_of_not_mem aNotInt] at bRest
          right
          rw [ih b]
          exact bRest
    next absurd _ => simp at absurd
        
lemma sortedList_is_sorted {α : Type} [LinearOrder α] : ∀ (s : Finset α), List.Chain' LT.lt s.sortedList := by
  intros s
  induction s using Finset.induction_on_min with
  | h0 =>
    unfold sortedList
    split
    next p _ => simp at p
    next => simp
  | step a t aMin ih =>
    simp
    unfold sortedList
    split
    next nonemp _ =>
      have minIns : min' (insert a t) nonemp = a := by
        cases t using Finset.induction with
        | empty => simp
        | @insert c t _ ih =>
          rw [Finset.min'_insert a (insert c t) (Finset.insert_nonempty c t)]
          apply min_eq_right
          apply le_of_lt
          apply aMin
          apply Finset.min'_mem
      have aNotInt : a ∉ t := by
        cases Finset.decidableMem a t
        next aNotInt => exact aNotInt
        next aInt =>
          have absurd := aMin a aInt
          simp at absurd
      simp [minIns, Finset.erase_eq_of_not_mem aNotInt]
      apply @List.Chain'.cons' α LT.lt a (sortedList t) ih
      intro b bHead
      have bInt := List.mem_of_mem_head? bHead
      rw [← sortedList_mem_iff] at bInt
      exact aMin b bInt
    next absurd _ => simp at absurd

end Finset

lemma bijection_of_eq_card {α β : Type} [DecidableEq α] [DecidableEq β] : ∀ {s : Finset α} {t : Finset β}, s.card = t.card → ((s = ∅ ∧ t = ∅) ∨ ∃ f : ↥s → ↥t, Function.Bijective f) := by
  
  intro s
  induction' s using Finset.induction with a s anotins ih
  simp
  intros t h
  left
  rw [← Finset.card_eq_zero]
  symm
  exact h

  intros t tcard
  right
  rw [(Finset.card_insert_of_not_mem anotins)] at tcard
  have tinsert := Eq.symm tcard
  rw [Finset.card_eq_succ] at tinsert
  rcases tinsert with ⟨b, t', bnotint', bins, tcards⟩
  rcases (ih (Eq.symm tcards)) with stempt | fbij 
  simp [stempt.right] at bins
  rw [stempt.left, ← bins]
  have bobv : b ∈ t
  rw [← bins]
  exact Finset.mem_singleton_self b
  lift b to t using bobv
  rw [bins]
  use (λ _ : {y // y ∈ insert a ∅} ↦ b)
  apply And.intro
  intros a₁ a₂ _
  apply Subtype.ext
  have a₁prop := a₁.prop
  have a₂prop := a₂.prop
  simp at a₁prop a₂prop
  simp [a₁prop, a₂prop]
  intros b'
  use ⟨a, Finset.mem_insert_self a ∅⟩
  have b'prop := b'.prop
  simp [← bins] at b'prop
  apply Subtype.ext
  simp [b'prop]
  have bint : b ∈ t := by rw [← bins] ; simp
  rcases fbij with ⟨f, fbij⟩
  have fhelper : ∀ x, ↑(f x) ∈ t
  intros
  simp [← bins]
  use (λ x ↦ match Finset.decidableMem ↑x s with
  | isTrue p => ⟨f ⟨↑x, p⟩, fhelper ⟨↑x, p⟩⟩
  | isFalse _ => ⟨b, bint⟩)
  apply And.intro
  intros a₁ a₂ fa₁a₂
  simp at fa₁a₂
  split at fa₁a₂ <;> split at fa₁a₂ <;> simp at fa₁a₂
  next a₁ins _ _ a₂ins _ =>
    have a₁eqa₂ := fbij.left (Subtype.ext fa₁a₂)
    simp at a₁eqa₂
    exact Subtype.ext a₁eqa₂
  next a₁ins _ _ a₂notins _ =>
    have fa₁prop := (f ⟨↑a₁, a₁ins⟩).prop
    rw [fa₁a₂] at fa₁prop
    contradiction
  next a₁notins _ _ a₂ins _ =>
    have bint' := (f { val := ↑a₂, property := a₂ins }).prop
    rw [← fa₁a₂] at bint'
    contradiction
  next a₁notins _ _ a₂notins _ =>
    have a₁a := a₁.prop
    have a₂a := a₂.prop
    simp [a₁notins, a₂notins] at a₁a a₂a
    apply Subtype.ext
    simp [a₁a, a₂a]
  
  intros b'
  have b'prop := b'.prop
  simp [← bins] at b'prop
  rcases b'prop with b'prop|b'prop
  use ⟨a, Finset.mem_insert_self a s⟩
  simp
  rcases ains : (Finset.decidableMem a s) with h|h
  simp [← b'prop]
  contradiction
  have boysc := fbij.right ⟨↑b', b'prop⟩
  rcases boysc with ⟨a', fa'⟩
  have a'ins : ↑a' ∈ insert a s
  simp
  use ⟨a',a'ins⟩ 
  rcases (Finset.decidableMem ↑a' s) with h|_
  cases h a'.prop
  simp_all
  split <;> simp_all;simp_all

lemma floormagic : ∀ (n m : ℕ) (q : ℚ), q < 1 → ↑n ≤ ⌊(↑m + q)⌋  → n ≤ m := by
  intros n m q smallqat nlemfloor
  rw  [Int.floor_nat_add] at nlemfloor
  have qflrle0 : ⌊q⌋ ≤ 0
  by_contra qflrpos
  simp at qflrpos
  rw [Int.floor_pos] at qflrpos
  cases (lt_irrefl 1 (lt_of_le_of_lt qflrpos smallqat))
  have mqlem := Int.add_le_add_left qflrle0 ↑m
  have nleqm := Int.le_trans nlemfloor mqlem
  simp at nleqm
  exact nleqm

 lemma xor_even_le_implies_lt : ∀ {m n : ℕ}, Xor' (Even m) (Even n) → m ≤ n → m < n := by
  intros m n xoreven mlen
  cases' xoreven with hp hq
  rw [le_iff_lt_or_eq] at mlen
  cases' mlen with mltn meqn
  exact mltn
  simp [meqn] at hp
  rw [le_iff_lt_or_eq] at mlen
  cases' mlen with mltn meqn
  exact mltn
  simp [meqn] at hq
  --NOTE: try using <;> to reduce redundancy 
  -- rcases xoreven with xoreven |xoreven <;>{
  -- rw [le_iff_lt_or_eq] at mlen
  -- rcases mlen with mlen | mlen
  -- exact mlen 
  -- simp [mlen] at xoreven
  -- --rw [le_iff_lt_or_eq] at mlen
  -- cases xoreven
  -- }
lemma notc : ∀ {c x y : Fin 2}, x ≠ c → y ≠ c → x = y := by

  intros c x y h₁ h₂
  fin_cases c 

  fin_cases x 
  contradiction
  fin_cases y 
  contradiction
  simp

  simp_all
  fin_cases x 
  simp_all
  fin_cases y 
  simp_all
  contradiction
  simp
  contradiction

lemma not0_eq1: ∀ {x: Fin 2}, x ≠ 0 ↔ x = 1 := by
  intro 
  apply Iff.intro 
  intro xneq0
  have _1_neq0 : (1 : Fin 2) ≠ 0 := by simp
  apply notc xneq0 _1_neq0
  intro
  simp_all
  done

lemma missing_pigeonhole {α β : Type} [DecidableEq α] [LinearOrderedSemiring β] : ∀ {s : Finset α}, Finset.Nonempty s → ∀ {f g : α → β}, s.sum f ≤ s.sum g → ∃ a : α, a ∈ s ∧ f a ≤ g a := by
  
  intros s sne f g fgsum
  induction' s using Finset.induction with a t anotint ih
  rcases sne with ⟨sne_w, sne_h⟩ 
  cases sne_h
  rcases Finset.eq_empty_or_nonempty t with h|h
  simp [h] at fgsum ⊢
  assumption
  simp_all
  cases (le_or_lt (f a) (g a)) with 
  |inl fleg => simp [fleg]
  |inr gltf =>
    cases (le_or_lt (t.sum f) (t.sum g)) with 
    |inl tfleg => simp_all
    |inr tgltf => cases (not_le_of_lt (add_lt_add gltf tgltf) fgsum)

  

-- NOTE: Proof by simp
/- lemma halflt1 : mkRat 1 2 < 1 := by
  simp -/


lemma dblcnt (M' N': ℕ) (f : Sym2 (Fin (M'+ N').succ) → Fin 2): ∀ c : Fin 2, 2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card = (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = c) Finset.univ).card := by

  let r: Sym2 (Fin (M' + N').succ) → (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart → Prop := λ x y ↦ x = ⟦y.toProd⟧ ∨ x = ⟦y.toProd.swap⟧
  intro c
  let s := Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = c) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset
  let t := Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = c) Finset.univ
  have hm : ∀ (a : Sym2 (Fin (M' + N').succ)), a ∈ s → (Finset.bipartiteAbove r t a).card = 2
  intros a ains
  rcases (Quotient.exists_rep a) with ⟨⟨fst,snd⟩, aprop⟩ 
  simp [SimpleGraph.mem_edgeSet, ← SimpleGraph.completeGraph_eq_top,completeGraph] at ains --NOTE: can be replace by simp_all
  simp [Finset.bipartiteAbove,Finset.card_eq_two]
  rcases ains with ⟨ains_left, ains_right⟩ 

  have aOutAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj fst snd := by
    simp [← aprop] at ains_left
    simp [ains_left] 
  use SimpleGraph.Dart.mk (fst,snd) aOutAdj
  
  have aOutSwapAdj : (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj snd fst := by 
    simp[aOutAdj]
    simp [Sym2.eq_swap, ←aprop] at ains_left
    intro ; simp_all
  use SimpleGraph.Dart.mk (snd,fst) aOutSwapAdj
  simp

  apply And.intro
  by_contra h
  simp[Prod.ext_iff] at h
  rcases h with ⟨h_left, _⟩ 
  simp[← aprop,h_left] at ains_left
  
  simp[Finset.Subset.antisymm_iff, Finset.subset_iff]
  apply And.intro
  intros x _ aeqx
  have swap : (snd, fst) = Prod.swap (fst, snd) := by simp
  simp [SimpleGraph.Dart.ext_iff]
  rw [swap, ← SimpleGraph.dart_edge_eq_mk'_iff]
  simp [aeqx, SimpleGraph.Dart.edge,aprop]

  simp_all
  have aeqswap : a = Quotient.mk (Sym2.Rel.setoid (Fin (Nat.succ (M' + N')))) (snd, fst) := by simp[← aprop]
  simp[aeqswap]
  simp[← aeqswap, ains_right] 
  
  have hn : ∀ (b : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart), b ∈ t → (Finset.bipartiteBelow r s b).card = 1
  intros b bint
  simp [Finset.bipartiteBelow, Finset.card_eq_one]
  simp[← SimpleGraph.completeGraph_eq_top, completeGraph] at bint
  use b.edge 
  simp[Finset.Subset.antisymm_iff, Finset.subset_iff, SimpleGraph.mem_edgeSet,←  SimpleGraph.completeGraph_eq_top, completeGraph]
  have toEdge : b.edge = ⟦b.toProd⟧ := by simp [SimpleGraph.dart_edge_eq_mk'_iff]
  apply And.intro
  intros x _ _ xeqb
  simp_all
  simp[Finset.filter] at bint
  simp[toEdge, bint]
  --NOTE: try avoid temp
  have temp := Finset.card_mul_eq_card_mul r hm hn
  simp[mul_one (t.card)] at temp
  simp[← temp,mul_comm]

-- NOTE: use Finset.univ_fin2
/- lemma univexpand : (@Finset.univ (Fin 2) _) = {0, 1} := by
  symm
  rw [Finset.eq_univ_iff_forall]
  intros
  fin_cases x; simp
 -/

lemma mkRat_one_den : ∀ (n : ℤ), (mkRat n 1).den = 1 := by intros; simp [mkRat, Rat.normalize]

lemma mkRat_one_num : ∀ (n : ℤ), (mkRat n 1).num = n := by intros; simp [mkRat, Rat.normalize]
