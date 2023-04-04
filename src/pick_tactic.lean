import data.finset

open interactive (parse)
open interactive.types (texpr with_ident_list)
open lean.parser (val ident tk small_nat)
open tactic.interactive («have»)

lemma pick_one_eq {α : Type} {s : finset α} [decidable_eq α] : 0 < s.card → ∃ (a : α) (t : finset α), (t.card = s.card.pred) ∧ (a ∉ t) ∧ (insert a t = s) :=
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
tauto,
end

lemma pick_one_lo {α : Type} {s : finset α} [linear_order α] : 0 < s.card → ∃ (a : α) (t : finset α), (t.card = s.card.pred) ∧ (∀ a' ∈ t, a < a') ∧ (insert a t = s) :=
begin
intro sp,
rw finset.card_pos at sp,
let a := s.min' sp,
let t := s.erase a,
use [a,t],
have a_in_s := s.min'_mem sp,
repeat {split},
{simp [a,t],
apply finset.card_erase_of_mem,
apply a_in_s,},
{intro a1,
intro a1_in_t,
apply s.min'_lt_of_mem_erase_min' sp a1_in_t,},
apply finset.insert_erase a_in_s,
end

meta def pick_diff (a : expr) (anotint : expr) (info : name × expr) : tactic unit :=
do {
  b ← tactic.get_local info.fst,
  `(_ ∉ %%t) ← tactic.infer_type anotint,
  neqexpr ← tactic.to_expr ``(%%a ≠ %%b),
  neqproof ← tactic.to_expr ``(λ x, %%anotint (@eq.subst _ (λ y, y ∈ %%t) _ _ (eq.symm x) %%info.snd)),
  ineqprooft ← tactic.infer_type neqproof,
  neqname ← tactic.get_unused_name "neq",
  tactic.assertv neqname neqexpr neqproof,
  return()
}

meta def pick_wrapup (s : expr) (info : name × expr) : tactic unit :=
do {
  n ← tactic.get_unused_name "wr",
  a ← tactic.get_local info.fst,
  inexpr ← tactic.to_expr ``(%%a ∈ %%s),
  tactic.assertv n inexpr info.snd,
  return ()
}

meta def pick_upgrade (ainst : expr) (info : name × expr) : tactic (name × expr) :=
do {
  `(insert %%a %%t = %%s) ← tactic.infer_type ainst,
  b ← tactic.get_local info.fst,
  subseqeqexpr ← tactic.to_expr ``(((finset.ext_iff.mp %%ainst) %%b).mp (finset.subset_iff.mp (finset.subset_insert %%a %%t) %%info.snd)),
  return (info.fst, subseqeqexpr)
}

-- Invariant: every level returns a list of triples of names where each triple is:
-- fst: the name of a member obtained in a recursive call
-- snd: the name of the fact that that member belongs to the rest of the set of this level
-- It is the responsibility of each level to upgrade the recursive list for the calling level
meta def pick : ℕ → expr → tactic (list (name × expr))
| nat.zero bineq := do {
    tactic.trace "here",
    tactic.trace bineq,
    omg ← tactic.infer_type bineq,
    tactic.trace omg,
    `(%%b < (finset.card %%s)) ← tactic.infer_type bineq,
    `(finset %%α) ← tactic.infer_type s,
    tactic.trace b, tactic.trace s,
    elemname ← tactic.get_unused_name "a",
    subsetname ← tactic.get_unused_name "t",
    atcardname ← tactic.get_unused_name "atcard",
    anotintname ← tactic.get_unused_name "anotint",
    ainstname ← tactic.get_unused_name "ainst",
    match b.to_nat with
    | some b' := match b' with
        | nat.zero := do {
            tactic.rcases none ``(pick_one_eq %%bineq) (tactic.rcases_patt.tuple (list.map tactic.rcases_patt.one [elemname, subsetname, atcardname, anotintname, ainstname]))
          }
        | nat.succ b'' := do {
            tactic.rcases none ``(pick_one_eq (lt_of_le_of_lt (nat.zero_le %%b) %%bineq)) (tactic.rcases_patt.tuple (list.map tactic.rcases_patt.one [elemname, subsetname, atcardname, anotintname, ainstname]))
          }
      end
    | none := tactic.fail "Somehow the bound was not a nat"
    end,
    elem ← tactic.get_local elemname,
    subset ← tactic.get_local subsetname,
    ainst ← tactic.get_local ainstname,
    tactic.trace ainst,
    ainparent ← tactic.to_expr ``(@eq.subst _ (λ x, %%elem ∈ x) _ _ %%ainst (finset.mem_insert_self %%elem %%subset)),
    return [(elemname, ainparent)]
  }
| (nat.succ n) bineq := do {
    `(%%b < (finset.card %%s)) ← tactic.infer_type bineq,
    `(finset %%α) ← tactic.infer_type s,
    tactic.trace b, tactic.trace s,
    elemname ← tactic.get_unused_name "a",
    subsetname ← tactic.get_unused_name "t",
    atcardname ← tactic.get_unused_name "atcard",
    anotintname ← tactic.get_unused_name "anotint",
    ainstname ← tactic.get_unused_name "ainst",
    tactic.rcases none ``(pick_one_eq (lt_of_le_of_lt (nat.zero_le %%b) %%bineq)) (tactic.rcases_patt.tuple (list.map tactic.rcases_patt.one [elemname, subsetname, atcardname, anotintname, ainstname])),
    subset ← tactic.resolve_name subsetname,
    atcard ← tactic.resolve_name atcardname,
    match b.to_nat with
    | some b' := do {
        -- We have to trust bpred is b-1 here
        newineqexpr ← tactic.to_expr ``(%%(reflect b'.pred) < (finset.card %%subset)),
        newineqproof ← tactic.to_expr ``(@eq.subst nat (λ x, %%(reflect b'.pred) < x) _ _ (eq.symm %%atcard) (nat.pred_lt_pred (nat.succ_ne_zero %%(reflect b'.pred)) %%bineq)),
        newboundname ← tactic.get_unused_name "newb",
        tactic.assertv newboundname newineqexpr newineqproof,
        simpdefault ← simp_lemmas.mk_default,
        localbound ← tactic.get_local newboundname,
        tactic.simp_hyp simpdefault [] localbound,
        localbound ← tactic.get_local newboundname,
        rec ← pick n localbound,
        elem ← tactic.get_local elemname,
        atnotint ← tactic.get_local anotintname,
        list.mmap' (λ i, pick_diff elem atnotint i) rec,
        ainst ← tactic.get_local ainstname,
        rec ← list.mmap (λ i, pick_upgrade ainst i) rec,
        elem ← tactic.get_local elemname,
        subset ← tactic.get_local subsetname,
        ainst ← tactic.get_local ainstname,
        tactic.trace ainst,
        ainparent ← tactic.to_expr ``(@eq.subst _ (λ x, %%elem ∈ x) _ _ %%ainst (finset.mem_insert_self %%elem %%subset)),
        return ((elemname, ainparent) :: rec)
      }
    | none := tactic.fail "Somehow the bound was not a nat"
    end
  }

meta def tactic.interactive.pick (k : parse small_nat) (stexp : parse (tk "from" *> texpr)) : tactic unit :=
do
  ctx ← tactic.local_context, 
  sexp ← tactic.i_to_expr stexp,
  ineqexp ← tactic.to_expr ``(_ < (finset.card %%sexp)),
  exp ← tactic.find_assumption ineqexp,
  etype ← tactic.infer_type exp,
  `(%%b < (finset.card %%l)) ← tactic.infer_type exp,
  match b.to_nat with
  | some c := if c.succ < k then tactic.fail "Picking too many elements!" else
              match k with
              | nat.zero := tactic.fail "Pick at least one element!"
              | (nat.succ k') := do {
                  tactic.trace k',
                  newobjs ← pick k' exp,
                  list.mmap' tactic.trace newobjs,
                  list.mmap' (λ i, pick_wrapup l i) newobjs
                }
              end
  | none := tactic.fail ("Assumption " ++ (to_string exp) ++ " is not a good bound.")
  end
