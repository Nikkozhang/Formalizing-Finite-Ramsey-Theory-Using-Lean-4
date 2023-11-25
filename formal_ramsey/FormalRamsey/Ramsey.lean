import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Rat.NNRat
import Mathlib.Data.Vector.Mem

import Mathlib.Tactic.PermuteGoals
import Lean.Parser.Tactic
import Mathlib.Tactic
import FormalRamsey.PickTactic
import FormalRamsey.Utils

import FormalRamsey.Ramsey2Color

open Ramsey

theorem RamseyPropSymm : ∀ {N k : ℕ} (s s' : Vector ℕ k.succ), RamseyProp N s → s.toList ~ s'.toList → RamseyProp N s' := by
  intros N k s s' RamseyN sPerm
  unfold RamseyProp at RamseyN ⊢
  simp [RamseyN.left]
  intro f
  cases s
  next s sLength =>
    cases s'
    next s' s'Length =>
      simp [Vector.toList] at sPerm
      rcases (bijection_of_List_perm sPerm.symm) with ⟨μ, ⟨μBij, μProp⟩⟩
      rcases (RamseyN.right (λ e ↦ Fin.cast sLength (μ (Fin.cast s'Length.symm (f e))))) with ⟨S, i, Sclique⟩
      simp [Vector.get] at Sclique
      haveI : Nonempty (Fin s'.length) := by simp [s'Length]; infer_instance
      use S, Fin.cast s'Length ((Function.invFun μ) (Fin.cast sLength.symm i))
      cases Sclique
      next Sclique Scard =>
        simp [Vector.get, List.nthLe] at Scard ⊢
        constructor
        · simp [graphAtColor, SimpleGraph.isClique_iff, Set.Pairwise] at Sclique ⊢
          intro u uIns v vIns uneqv
          apply And.intro
          · exact uneqv
          · have fuv := (Sclique uIns vIns uneqv).right
            have fuvcast := congr_arg (Fin.cast sLength.symm) fuv
            simp at fuvcast
            have fuvμ := congr_arg (Function.invFun μ) fuvcast
            have fuvcomp := congr_fun (Function.invFun_comp μBij.left) (Fin.cast s'Length.symm (f (Quotient.mk (Sym2.Rel.setoid (Fin N)) (u, v))))
            simp [Function.comp] at fuvcomp
            rw [fuvcomp] at fuvμ
            rw [← fuvμ]
            simp
        · rw [Scard]
          have si := μProp (Function.invFun μ (Fin.cast sLength.symm i))
          have μinv := Function.rightInverse_invFun μBij.right
          rw [Function.rightInverse_iff_comp] at μinv
          have μinvi := congr_fun μinv (Fin.cast sLength.symm i)
          unfold Function.comp at μinvi
          simp [μinvi] at si
          rw [si]
          simp [Fin.cast]
  done

noncomputable def Ramsey {k : ℕ} (s : Vector ℕ k.succ) : ℕ := sInf { N : ℕ | RamseyProp N s }

theorem Ramsey2 : ∀ {k : ℕ} (s : Vector ℕ k.succ), Ramsey (2 ::ᵥ s) = Ramsey s := sorry
  -- intros k
  -- unfold Ramsey₂

  -- have Ramsey₂2_monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ } → M₂ ∈ { N : ℕ | Ramsey₂Prop N 2 k.succ }
  -- intros M₁ M₂ M₁leM₂
  -- simp
  -- intro M₁Ramsey
  -- apply RamseyMonotone M₁Ramsey M₁leM₂

  -- rw [Nat.sInf_upward_closed_eq_succ_iff]
  -- simp
  -- apply And.intro
  -- simp [Ramsey₂Prop, RamseyProp]
  -- intros f
  -- rcases Finset.eq_empty_or_nonempty (Finset.filter 
  -- (λ (x : Sym2 (Fin k.succ))↦ ¬ x.IsDiag ∧ f x = 0) Finset.univ) with h|h
  -- rw [Finset.filter_eq_empty_iff] at h
  -- use Finset.univ,1
  -- constructor
  -- simp [graphAtColor, Vector.get, List.nthLe, SimpleGraph.isClique_iff, Set.Pairwise]
  -- intros x y xneqy
  -- let a: Sym2 (Fin (k + 1)) := ⟦(x, y)⟧
  -- rcases (Quotient.exists_rep a) with ⟨⟨fst,snd⟩,aprop⟩ 
  -- simp_all
  -- have nDiag : ¬Sym2.IsDiag a := by simp_all
  -- cases aprop <;> simp[← not0_eq1, (h a nDiag)] 
  -- simp [Vector.get, List.nthLe]
  -- rcases h with ⟨⟨fst,snd⟩ ,wprop⟩ 
  -- simp at wprop
  -- use {fst,snd},0
  -- constructor
  -- simp [SimpleGraph.isClique_iff, graphAtColor, Set.Pairwise]

  -- apply And.intro
  -- intro h ;simp[h] ;exact wprop.right
  -- intro h ;simp[h,Sym2.eq_swap] ;exact wprop.right
  -- simp [Vector.get,List.nthLe,Finset.card_eq_two]
  -- use fst,snd
  -- simp
  -- intro h
  -- rw [← Sym2.mk''_isDiag_iff] at h
  -- cases wprop.left h
  
  -- unfold Ramsey₂Prop
  -- unfold RamseyProp
  -- simp
  -- intro
  -- let f : Sym2 (Fin k) → Fin 2 := λ e ↦ 1
  -- use f
  -- by_contra h
  -- simp at h
  -- rcases h with ⟨ S, ⟨ i, SProp ⟩ ⟩ 
  -- fin_cases i

  -- rw [SimpleGraph.isNClique_iff] at SProp
  -- rcases SProp with ⟨SisClique,S_card⟩
  -- unfold graphAtColor at SisClique
  -- simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at SisClique
  -- simp [Vector.get, List.nthLe,Finset.card_eq_two] at S_card
  -- rcases S_card with ⟨x,y,⟨xneqy,Sxy⟩ ⟩ 
  -- have xins : x ∈ S := by rw [Sxy]; simp
  -- have yins : y ∈ S := by rw [Sxy]; simp
  -- exact SisClique xins yins xneqy

  -- have kcard : Fintype.card (Fin k) < k.succ := by simp
  -- have cliquefree : (graphAtColor (completeGraph (Fin k)) f 1).CliqueFree k.succ := by 
  --   apply SimpleGraph.cliqueFree_of_card_lt kcard
  -- unfold SimpleGraph.CliqueFree at cliquefree
  -- have Scontra :=  cliquefree S
  -- contradiction

  -- assumption
  -- done

theorem Ramsey1Prop : ∀ {k : ℕ} (N : ℕ) (s : Vector ℕ k.succ), RamseyProp N.succ (1 ::ᵥ s) := by
  simp [RamseyProp]
  intros
  use {0}, 0
  constructor
  · simp [SimpleGraph.isClique_iff, Set.Pairwise]
  · simp [Vector.get_zero]

theorem Ramsey1 : ∀ {k : ℕ} (s : Vector ℕ k.succ), Ramsey (1 ::ᵥ s) = 1 := by
  intro k s
  simp [Ramsey]
  have Ramsey1Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyProp N (1 ::ᵥ s)} → M₂ ∈ { N : ℕ | RamseyProp N (1 ::ᵥ s) }
  · intros M₁ M₂ M₁leM₂
    simp
    intro M₁Ramsey
    apply RamseyMonotone M₁Ramsey M₁leM₂
  · rw [Nat.sInf_upward_closed_eq_succ_iff]
    · simp
      apply And.intro
      · apply Ramsey1Prop
      · simp [RamseyProp]
    · assumption

-- TODO Note that these are multicolor theorems already, probably deserve to be in Utils.lean
-- def monochromaticVicinity {α : Type} [Fintype α] {c : ℕ} (g : SimpleGraph α) [DecidableRel g.Adj] (v : α) (f : Sym2 α → Fin c) (i : Fin c) : Finset α := Finset.filter (λ x ↦  f ⟦(v, x)⟧ = i) (g.neighborFinset v)

-- lemma monochromaticVicinity_Ramsey {N c : ℕ} : ∀ (v : Fin N) (f : Sym2 (Fin N) → Fin c.succ) (i : Fin c.succ) (s : Vector ℕ c.succ), RamseyProp (monochromaticVicinity (⊤:SimpleGraph (Fin N)) v f i).card s → (∃ S, (graphAtColor (completeGraph (Fin N)) f i).IsNClique (s.get i).succ S) ∨ (∃ i' S, i' ≠ i ∧ (graphAtColor (completeGraph (Fin N)) f i').IsNClique (s.get i') S) := by

def increaseVector {k : ℕ} (s : Vector ℕ k) : Vector ℕ k := Vector.ofFn (λ i ↦ (s.get i).succ)

#eval increaseVector (Vector.ofFn (λ (_ : Fin 3) ↦ 2))

def increaseVectorExcept {k : ℕ} (s : Vector ℕ k) (i : Fin k) : Vector ℕ k := Vector.ofFn (λ j ↦ if i = j then s.get i else (s.get j).succ)

#eval increaseVectorExcept (Vector.ofFn (λ (_ : Fin 3) ↦ 2)) 1

set_option maxHeartbeats 500000

theorem RamseyPropIneq : ∀ {k : ℕ} {M : Vector ℕ k.succ.succ} (MPos : 1 ≤ M.toList.sum) (s : Vector ℕ k.succ.succ), (∀ (i : Fin k.succ.succ), RamseyProp (M.get i) (increaseVectorExcept s i)) → RamseyProp M.toList.sum (increaseVector s) := by
  intros k M MPos s RamseyM
  have MSumPos : M.toList.sum > 0 := by
    have headPos := (RamseyM 0).left
    simp at headPos
    have allMNNeg : ∀ (m : ℕ), m ∈ M.toList → 0 ≤ m := by simp
    have sumLB := List.single_le_sum allMNNeg M.head M.head_mem
    use lt_of_lt_of_le headPos sumLB
  unfold RamseyProp
  apply And.intro
  · exact MSumPos
  · intro f
    haveI : NeZero M.toList.sum := by
      constructor
      intro h
      simp [h] at MSumPos
    have MSumNonzero : M.toList.sum ≠ 0 := by
      intro MSumZero
      simp [MSumZero] at MPos
    rcases (Nat.exists_eq_succ_of_ne_zero MSumNonzero) with ⟨M', M'Prop⟩
    let g : Fin k.succ.succ → ℚ := λ i ↦ ↑(M.get i) - mkRat 1 k.succ.succ
    let h : Fin k.succ.succ → ℚ := λ c ↦ (((⊤ : SimpleGraph (Fin M'.succ)).neighborFinset 0).filter (λ v : Fin M'.succ ↦ (λ e : Sym2 (Fin M'.succ) ↦ f (e.map (Fin.cast M'Prop.symm))) ⟦(0, v)⟧ = c)).card
    have hgsum : Finset.univ.sum h = Finset.univ.sum g := by
      simp [Rat.add_def]
      rw [Int.ofNat_add_one_out, Rat.normalize_eq_mkRat Nat.zero_ne_one.symm, Rat.mkRat_one_num, Rat.normalize_eq_mkRat]
      simp only [Rat.mkRat_one_den ↑(k.succ), Int.ofNat_add_out, ← Nat.succ_eq_add_one, Rat.mkRat_mul_mkRat, Nat.mul_comm, Rat.mkRat_mul_left k.succ.succ_ne_zero]
      simp [Rat.mkRat_one]
      trans ↑((⊤ : SimpleGraph (Fin M'.succ)).neighborFinset 0).card
      · trans ↑(Finset.sum Finset.univ (λ x ↦ (Finset.filter (λ v ↦ f ⟦(0, (Fin.cast M'Prop.symm v))⟧ = x) ((⊤ : SimpleGraph (Fin M'.succ)).neighborFinset 0)).card))
        · simp
        · rw [Nat.cast_inj]
          have partCard : ∀ {n m : ℕ} (f' : Sym2 (Fin n.succ) → Fin m.succ), Finset.univ.sum (λ x ↦ (((⊤ : SimpleGraph (Fin n.succ)).neighborFinset 0).filter (λ v ↦ f' ⟦(0, v)⟧ = x)).card) = ((⊤ : SimpleGraph (Fin n.succ)).neighborFinset 0).card := by
            intro n
            induction n with
            | zero => simp
            | succ n' ih =>
              simp
              intro m f'
              let partition : Finset (Finset (Fin n'.succ.succ)) := Finset.univ.image (λ x ↦ ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0).filter (λ v ↦ f' ⟦(0, v)⟧ = x))
              have partitionPwDisj : Set.PairwiseDisjoint ↑partition (@id (Finset (Fin n'.succ.succ))) := by
                unfold Set.PairwiseDisjoint Set.Pairwise Disjoint id
                intros x xinPart y yinPart xneqy
                simp only [List.coe_toFinset, List.mem_ofFn] at xinPart yinPart
                simp [Function.onFun_apply] at xinPart yinPart ⊢
                intros a ainx ainy
                rcases xinPart with ⟨x', xProp⟩
                rcases yinPart with ⟨y', yProp⟩
                rw [← xProp] at ainx
                rw [← yProp] at ainy
                rw [Finset.subset_iff] at ainx ainy ⊢
                intros b bina
                have binx := ainx bina
                have biny := ainy bina
                simp at binx biny
                have x'eqy' := Eq.trans binx.right.symm biny.right
                rw [x'eqy'] at xProp
                have xeqy := Eq.trans xProp.symm yProp
                contradiction
              have partitionSupParts : partition.sup id = ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0) := by
                apply subset_antisymm <;> rw [Finset.subset_iff]
                · intros v vinSup
                  simp only [Finset.mem_sup, id] at vinSup
                  rcases vinSup with ⟨a, ⟨aProp, vina⟩⟩
                  simp at aProp
                  rcases aProp with ⟨i, aProp⟩
                  simp [← aProp] at vina ⊢
                  exact vina.left
                · intros v vneq0
                  simp only [Finset.mem_sup, id]
                  use ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0).filter (λ u ↦ f' ⟦(0, u)⟧ = f' ⟦(0, v)⟧)
                  simp at vneq0 ⊢
                  exact vneq0
              let parted : Finset.FinpartitionWithEmpty ((⊤ : SimpleGraph (Fin n'.succ.succ)).neighborFinset 0) := ⟨partition, partitionPwDisj, partitionSupParts⟩
              have partedSum := parted.sum_card_parts_with_empty
              simp at partedSum
              rw [Finset.sum_image_vanishing] at partedSum
              · exact partedSum
              · simp
                intros x y filtereq filternonempty
                rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at filternonempty
                rcases filternonempty with ⟨u, uinxFilter⟩
                have uinyFilter := uinxFilter
                rw [filtereq] at uinyFilter
                simp at uinxFilter uinyFilter
                exact Eq.trans uinxFilter.right.symm uinyFilter.right
          have partRw := partCard (λ e : Sym2 (Fin (M'.succ)) ↦ f (e.map (Fin.cast M'Prop.symm)))
          simp at partRw ⊢
          exact partRw
      · simp
        rw [← M'.succ_sub_one, ← M'Prop, Nat.cast_sub MPos]
        simp
        apply vector_list_finset_sum
    -- NOTE: The hgsum lemma is backwards (should be ghsum) so here we need hgsum.symm
    have mp := missing_pigeonhole (Exists.intro (0 : Fin k.succ.succ) (Finset.mem_univ 0)) (le_of_eq hgsum.symm)
    rcases mp with ⟨a, _, gha⟩
    simp at gha
    rw [← Int.cast_ofNat, ← Rat.le_floor] at gha
    have invLt1 : mkRat 1 k.succ.succ < 1 := by
      rw [Rat.lt_def, Rat.mkRat_den_one, Rat.mkRat_num_one]
      simp
    -- TODO: Make arguments in floormagic implicit
    have MleqNeighbora := floormagic _ _ (mkRat 1 k.succ.succ) invLt1 gha
    have cliqueCases := monochromaticVicinity_Ramsey 0 (λ e : Sym2 (Fin M'.succ) ↦ f (e.map (Fin.cast M'Prop.symm))) a (increaseVectorExcept s a) (RamseyMonotone (RamseyM a) MleqNeighbora)
    cases cliqueCases with
    | inl cliqueCase =>
      rcases cliqueCase with ⟨S, Sclique⟩
      use S.map (Fin.castEmb M'Prop.symm), a
      rw [SimpleGraph.isNClique_iff] at Sclique
      rcases Sclique with ⟨Sclique, Scard⟩
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
        exact Sclique
      · simp [increaseVector, increaseVectorExcept] at Scard ⊢
        exact Scard
    | inr cliqueCase =>
      rcases cliqueCase with ⟨b, S, bneqa, Sclique⟩
      use S.map (Fin.castEmb M'Prop.symm), b
      rw [SimpleGraph.isNClique_iff] at Sclique
      rcases Sclique with ⟨Sclique, Scard⟩
      constructor
      · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
        exact Sclique
      · simp [increaseVector, increaseVectorExcept, bneqa.symm] at Scard ⊢
        exact Scard

-- TODO Figure out how to state this theorem
-- theorem Ramsey₂PropStrictIneq : ∀ M N s t : ℕ, Even M → Even N → Ramsey₂Prop M s.succ t.succ.succ → Ramsey₂Prop N s.succ.succ t.succ → Ramsey₂Prop (M + N).pred s.succ.succ t.succ.succ := by
--   intros M N s t evenM evenN RamseyM RamseyN
--   rcases (Nat.exists_eq_succ_of_ne_zero (Ne.symm (ne_of_lt RamseyM.left))) with ⟨M', rfl⟩
--   rcases (Nat.exists_eq_succ_of_ne_zero (Ne.symm (ne_of_lt RamseyN.left))) with ⟨N', rfl⟩
--   simp [Nat.succ_add, Nat.add_succ]
--   unfold Ramsey₂Prop RamseyProp
--   simp
--   intro f 
--   let g : Fin 2 → ℕ := (λ x ↦ 2 * (Finset.filter (λ e ↦ f e = x) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card)
--   let h : Fin 2 → ℕ := ![(M' + N').succ * M', (M' + N').succ * N']
--   have hgsum : Finset.univ.sum h = Finset.univ.sum g
--   simp [Finset.univ_fin2]
--   rw [← Nat.left_distrib, ← Nat.left_distrib]
--   have filterdisj : Disjoint (Finset.filter (λ e ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset) (Finset.filter (λ e ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset)
--   simp [Finset.disjoint_iff_ne]
--   intros a _ fa0 b _ fb1
--   by_contra h
--   simp [h,fb1] at fa0
--   rw [← Finset.card_union_eq filterdisj]
--   have seteq : (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset ∪ Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset) = (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset
--   simp[Finset.Subset.antisymm_iff,Finset.subset_iff]
--   apply And.intro
--   intros _ xprop ; cases xprop <;> simp_all  
--   intros x xprop 
--   by_contra h
--   simp [not_or,not0_eq1, xprop] at h

--   rw [seteq, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
--   simp
--   have mp := missing_pigeonhole (Exists.intro (0 : Fin 2) (Finset.mem_univ (0 : Fin 2))) (Nat.le_of_eq hgsum)
--   rcases mp with ⟨a, ainuniv, gha⟩

--   have cardodd : Odd (M' + N').succ := by
--     simp[← Nat.even_add_one]
--     rw[← Nat.succ_add, Nat.add_assoc, Nat.add_one]
--     simp[Nat.even_add, evenM, evenN]

--   fin_cases a <;> simp_all[-cardodd]
--   have evenrhs : Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card) := by simp
--   have xoreven : Xor' (Even ((M' + N').succ * M')) (Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ))↦ f e = 0) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card)) := by 
--     right
--     simp
--     rw [← Nat.add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenM
--     have oddlhs := Nat.odd_mul.mpr ⟨cardodd, evenM⟩
--     simp at oddlhs
--     exact oddlhs
--   swap
--   have evenrhs : Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card) := by simp
--   have xoreven : Xor' (Even ((M' + N').succ * N')) (Even (2 * (Finset.filter (λ (e : Sym2 (Fin (M' + N').succ)) ↦ f e = 1) (⊤ : SimpleGraph (Fin (M' + N').succ)).edgeFinset).card)) := by
--     right
--     simp
--     rw [← Nat.add_one, Nat.even_add_one, ← Nat.odd_iff_not_even] at evenN
--     have oddlhs := Nat.odd_mul.mpr ⟨cardodd, evenN⟩
--     simp at oddlhs
--     exact oddlhs
  
--   have ghalt := xor_even_le_implies_lt xoreven gha
--   rw [dblcnt M' N' f 1] at ghalt
--   have pghineq : (@Finset.univ (Fin (M' + N').succ) _).card • N' < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = 1) Finset.univ).card) := by simp [ghalt]
--   have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
--   rcases pgh with ⟨v, _, vprop⟩
--   have cardeq : (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ x.toProd.snd = v)
--         (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) ↦ f ⟦x.toProd⟧ = 1) Finset.univ)).card = (monochromaticVicinity (⊤ : SimpleGraph (Fin (M' + N').succ)) v f 1).card  

--   pick_goal -1
--   have ghalt := xor_even_le_implies_lt xoreven gha
--   rw [dblcnt M' N' f 0] at ghalt
--   have pghineq : (@Finset.univ (Fin (M' + N').succ) _).card • M' < ↑((Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ f ⟦x.toProd⟧ = 0) Finset.univ).card) := by simp [ghalt]
--   have pgh := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ (e : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ Finset.mem_univ e.snd) pghineq
--   rcases pgh with ⟨v, _, vprop⟩
--   simp at vprop
--   have cardeq : (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ x.toProd.snd = v)
--         (Finset.filter (λ (x : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart)↦ f ⟦x.toProd⟧ = 0) Finset.univ)).card = (monochromaticVicinity (⊤ : SimpleGraph (Fin (M' + N').succ)) v f 0).card
--   all_goals{
--     try{
--       apply Finset.card_congr (λ (a : (⊤ : SimpleGraph (Fin (M' + N').succ)).Dart) _ ↦ a.fst)
--       intro a
--       simp [monochromaticVicinity]
--       intros f0 asndv
--       have aprop := a.is_adj
--       simp[asndv] at aprop
--       simp[Ne.symm aprop]
--       simp [Sym2.eq_swap, ← asndv]
--       exact f0
--       intros _ _
--       simp
--       intros _ asndv _ bsndv abfst
--       rw [SimpleGraph.Dart.ext_iff, Prod.ext_iff]
--       simp [abfst, asndv, bsndv]
--       intro b
--       simp [monochromaticVicinity]
--       intros bnotv fvb0
--       have bvAdj: (⊤ : SimpleGraph (Fin (M' + N').succ)).Adj b v := by simp [Ne.symm, bnotv]
--       use SimpleGraph.Dart.mk (b,v) bvAdj 
--       simp [Sym2.eq_swap, fvb0]
--     }
--     try{
--       rw [cardeq] at vprop
--       have cliquecases := monochromaticVicinity_Ramsey v f 0 ⟨[s.succ, t.succ.succ], by simp⟩ (RamseyMonotone RamseyM vprop)
--       rcases cliquecases with ⟨S, Sclique⟩ | cliquecases
--       use S, 0
--       exact Sclique
--       rcases cliquecases with ⟨i, ⟨S, Sclique⟩⟩
--       use S, 1
--       have ieq1 := notc Sclique.left (Fin.succ_ne_zero 0)
--       simp [ieq1] at Sclique
--       exact Sclique
--     }
--     try{
--       rw [cardeq] at vprop
--       have cliquecases := monochromaticVicinity_Ramsey v f 1 ⟨[s.succ.succ, t.succ], by simp⟩ (RamseyMonotone RamseyN vprop)
--       rcases cliquecases with ⟨T, Tclique⟩ | cliquecases
--       use T, 1
--       exact Tclique
--       rcases cliquecases with ⟨i, ⟨T, Tclique⟩⟩
--       use T, 0
--       have ineq1 := notc Tclique.left Fin.zero_ne_one
--       simp [ineq1] at Tclique
--       exact Tclique
--     }
--   }
--   done

theorem RamseyFinite : ∀ {k : ℕ} (s : Vector ℕ k.succ), { N : ℕ | RamseyProp N s }.Nonempty := by
  intro k
  cases k with
  | zero =>
    intro s
    use s.head.succ
    simp [RamseyProp]
    intro f
    use (Finset.univ.map Fin.castSuccEmb.toEmbedding), 0
    constructor <;>  simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor]
  | succ k =>
    induction k with
    | zero =>
      intro s
      cases s
      next s sLength =>
        rw [List.length_eq_two] at sLength
        rcases sLength with ⟨a, b, sEq⟩
        rcases (Ramsey₂Finite a b) with ⟨R, RProp⟩
        simp [Ramsey₂Prop] at RProp
        use R
        simp [sEq]
        exact RProp
    | succ k' ih =>
      intro s
      rcases (ih s.tail) with ⟨R, RProp⟩
      rcases (Ramsey₂Finite s.head R) with ⟨R', R'Prop⟩
      simp at RProp R'Prop
      simp [Ramsey₂Prop, RamseyProp] at R'Prop
      use R'
      simp [RamseyProp]
      apply And.intro
      · exact R'Prop.left
      · intro f
        rcases (R'Prop.right (λ e ↦ if f e = 0 then 0 else 1)) with ⟨R'', i, R''Prop⟩
        fin_cases i
        · use R'', 0
          simp [graphAtColor] at R''Prop ⊢
          cases R''Prop
          next R''Clique R''Card =>
            constructor
            · simp [SimpleGraph.IsClique, Set.Pairwise] at R''Clique ⊢
              intros x xinR y yinR xneqy
              cases (R''Clique xinR yinR xneqy)
              next _ notnot =>
                simp [xneqy]
                rw [← @Decidable.not_not (f (Quotient.mk (Sym2.Rel.setoid (Fin R')) (x, y)) = 0)]
                exact notnot
            · exact R''Card
        · simp at R''Prop
          unfold RamseyProp at RProp
          rcases R''Prop with ⟨R''Clique, R''Card⟩
          have Rcard : (Finset.univ : Finset (Fin R)).card = R''.card := by
            simp [Vector.get, List.nthLe] at R''Card
            simp [R''Card]
          have FinRNonempty : (Finset.univ : Finset (Fin R)) ≠ ∅ := by
            haveI : Nonempty (Fin R) := by
              rw [← Fin.pos_iff_nonempty]
              exact RProp.left.lt
            rw [← Finset.nonempty_iff_ne_empty]
            apply Finset.univ_nonempty
          have vertexMapEx := bijection_of_eq_card Rcard
          simp [FinRNonempty] at vertexMapEx
          rcases vertexMapEx with ⟨vmap, vmapBij⟩
          have fneq0 : ∀ (e : Sym2 (Fin R)), f (e.map (λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v ))).val)) ≠ 0 := by
            intros e feq0
            simp [SimpleGraph.isClique_iff, Set.Pairwise] at R''Clique
            have eversion : ∃ x, f (x.map (λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v ))).val)) = 0 := ⟨e, feq0⟩
            rw [Sym2.exists] at eversion
            rcases eversion with ⟨u, v, uvProp⟩
            have vmapneq : ¬(vmap (Subtype.mk u (Finset.mem_univ u))).val = (vmap (Subtype.mk v (Finset.mem_univ v))).val := sorry
            have cliqueInfo := R''Clique (vmap (Subtype.mk u (Finset.mem_univ u))).property (vmap (Subtype.mk v (Finset.mem_univ v))).property vmapneq
            simp [graphAtColor] at cliqueInfo
            exact cliqueInfo.right uvProp
          have exClique := RProp.right (λ (e : Sym2 (Fin R)) ↦ (f (e.map (λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v))).val))).pred (fneq0 _))
          rcases exClique with ⟨S, i, Sclique⟩
          let vmap' := λ v ↦ (vmap (Subtype.mk v (Finset.mem_univ v))).val
          have vmapInj : Function.Injective vmap' := by
            simp [Function.Injective]
            intros a₁ a₂ vmapa₁a₂
            rw [← Subtype.ext_iff] at vmapa₁a₂
            exact Subtype.ext_iff.mp (vmapBij.left vmapa₁a₂)
          let vmapEmb : Function.Embedding (Fin R) (Fin R') := ⟨vmap', vmapInj⟩
          use S.map vmapEmb, i.succ
          rcases Sclique with ⟨Sclique, Scard⟩
          constructor
          · simp [SimpleGraph.isClique_iff, Set.Pairwise, graphAtColor] at Sclique ⊢
            intros x xinS y yinS xneqy
            apply And.intro
            · exact xneqy
            · have xneqy' : ¬(x = y) := sorry
               -- intro xeqy
               -- rw [← Subtype.ext_iff] at xneqy
              have lemmesee := Sclique xinS yinS xneqy'
              rw [Fin.pred_eq_iff_eq_succ] at lemmesee
              exact lemmesee.right
          · simp at Scard ⊢
            exact Scard

-- TODO Figure out how to state this theorem
-- theorem Ramsey₂Ineq : ∀ s t : ℕ, Ramsey₂ s.succ.succ t.succ.succ ≤ Ramsey₂ s.succ t.succ.succ + Ramsey₂ s.succ.succ t.succ := by 
--   intros s t
--   have RamseyM := Nat.sInf_mem (Ramsey₂Finite s t.succ)
--   have RamseyN := Nat.sInf_mem (Ramsey₂Finite s.succ t)
--   apply Nat.sInf_le
--   simp_all  
--   apply Ramsey₂PropIneq<;> assumption
--   done

-- TODO Figure out how to state this theorem
-- theorem Ramsey₂StrictIneq : ∀ s t : ℕ, Even (Ramsey₂ s.succ t.succ.succ) → Even (Ramsey₂ s.succ.succ t.succ) → Ramsey₂ s.succ.succ t.succ.succ < Ramsey₂ s.succ t.succ.succ + Ramsey₂ s.succ.succ t.succ := by
--   intros s t evenM evenN
--   have lt_or_eq := Decidable.lt_or_eq_of_le (Ramsey₂Ineq s t)
--   rcases lt_or_eq with lt | eq
--   exact lt 

--   have temp := Ramsey₂PropStrictIneq (Ramsey₂ s.succ t.succ.succ) (Ramsey₂ s.succ.succ t.succ) (s) (t) evenM evenN
--   unfold Ramsey₂ at temp
--   have RamseyM := Nat.sInf_mem (Ramsey₂Finite s t.succ)
--   have RamseyN := Nat.sInf_mem (Ramsey₂Finite s.succ t)
--   simp at RamseyM RamseyN
--   unfold Ramsey₂ at eq

--   have pos : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}) ≠ 0
--   simp[← eq]
--   by_contra h
--   rcases h with h | h
--   unfold Ramsey₂Prop RamseyProp at h
--   simp at h
--   have contra := Ramsey₂Finite s.succ t.succ
--   simp [h] at contra

--   have pred_lt : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}).pred < 
--   (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}) := by simp[ Nat.pred_lt pos]

--   have predInSet : (sInf {N : ℕ | Ramsey₂Prop N s.succ t.succ.succ} + 
--   sInf {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ}).pred ∈ 
--   {N : ℕ | Ramsey₂Prop N s.succ.succ t.succ.succ} := by simp[temp RamseyM RamseyN]

--   have le_pred :=  Nat.sInf_le predInSet
--   simp[eq] at le_pred
--   have absurd := lt_of_le_of_lt le_pred pred_lt
--   simp at absurd
--   done