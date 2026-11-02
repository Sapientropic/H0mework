import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Tensor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code} (cursor : Cursor seed driver)
  (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model)) (n : Nat)

def NoWorse (new previous : Term cursor) : Prop :=
  ∀ table ∈ tables cursor, accepts cursor (tensor cursor pricing new (opponent cursor table) n)
    (tensor cursor pricing previous (opponent cursor table) n)
instance (new previous : Term cursor) : Decidable (NoWorse cursor pricing n new previous) := by
  unfold NoWorse;infer_instance

def Benefit (new previous : Term cursor) : Prop :=
  ∀ table ∈ tables cursor, benefit cursor (tensor cursor pricing new (opponent cursor table) n)
    (tensor cursor pricing previous (opponent cursor table) n)
instance (new previous : Term cursor) : Decidable (Benefit cursor pricing n new previous) := by
  unfold Benefit;infer_instance

theorem noWorse_trans {first middle last : Term cursor}
    (left : NoWorse cursor pricing n first middle) (right : NoWorse cursor pricing n middle last) :
    NoWorse cursor pricing n first last := fun table inside =>
  accepts_trans cursor (left table inside) (right table inside)
theorem no_worse_bounds_real_benefit {new previous : Term cursor}
    (accepted : NoWorse cursor pricing n new previous) : Benefit cursor pricing n new previous :=
  fun table inside => acceptance_bounds_every_real_benefit cursor (accepted table inside)

abbrev Axis := Table cursor × Term cursor
def axes : List (Axis cursor) := (tables cursor).flatMap fun table => (terms cursor).map (table,·)
/-- Finite order embedding of the real-benefit preorder; archive admission is absent from its tests. -/
def cost (term : Term cursor) (axis : Axis cursor) : ℚ :=
  if benefit cursor (tensor cursor pricing term (opponent cursor axis.1) n)
    (tensor cursor pricing axis.2 (opponent cursor axis.1) n) then 0 else 1

theorem vector_iff (new previous : Term cursor) :
    Distributed.NoWorse (axes cursor) (cost cursor pricing n) new previous ↔ Benefit cursor pricing n new previous := by
  constructor
  · intro vector table inside
    have tested := vector (table,previous) (List.mem_flatMap.mpr ⟨table,inside,
      List.mem_map.mpr ⟨previous,List.mem_attach _ _,rfl⟩⟩)
    have self := benefit_refl cursor (tensor cursor pricing previous (opponent cursor table) n)
    by_contra failed
    simp only [cost,if_pos self,if_neg failed] at tested
    norm_num at tested
  · intro all axis inside
    obtain ⟨table,generated,mapped⟩ := List.mem_flatMap.mp inside
    obtain ⟨probe,_,same⟩ := List.mem_map.mp mapped
    cases same
    by_cases old : benefit cursor (tensor cursor pricing previous (opponent cursor table) n)
        (tensor cursor pricing probe (opponent cursor table) n)
    · have current := benefit_trans cursor (all table generated) old
      simp only [cost,if_pos old,if_pos current,le_refl]
    · simp only [cost,if_neg old]
      split <;> norm_num

def Better (previous new : Term cursor) : Prop :=
  NoWorse cursor pricing n new previous ∧ ¬ Benefit cursor pricing n previous new

structure Candidate (reference : Term cursor) where
  term : Term cursor
  no_regression : NoWorse cursor pricing n term reference

def check (reference term : Term cursor) : Option (Candidate cursor pricing n reference) :=
  if valid : NoWorse cursor pricing n term reference then some ⟨term,valid⟩ else none

def candidates (reference : Term cursor) := (terms cursor).filterMap (check cursor pricing n reference)

theorem every_accepted_term_is_generated (reference term : Term cursor)
    (valid : NoWorse cursor pricing n term reference) :
    ∃ candidate ∈ candidates cursor pricing n reference, candidate.term = term := by
  exact ⟨⟨term,valid⟩,List.mem_filterMap.mpr ⟨term,List.mem_attach _ _,by simp [check,valid]⟩,rfl⟩

abbrev Choice (reference : Term cursor) :=
  Selected (axes cursor) (fun candidate : Candidate cursor pricing n reference => cost cursor pricing n candidate.term)
    (candidates cursor pricing n reference)

def strictBenefit (previous new : Term cursor) : Prop :=
  Benefit cursor pricing n new previous ∧ ¬ Benefit cursor pricing n previous new
instance (previous new : Term cursor) : Decidable (strictBenefit cursor pricing n previous new) := by
  unfold strictBenefit;infer_instance

theorem strictBenefit_iff (previous new : Term cursor) : strictBenefit cursor pricing n previous new ↔
    Improves (axes cursor) (cost cursor pricing n) previous new := by
  simp only [strictBenefit,Improves,vector_iff]

private theorem strictBenefit_irrefl (term : Term cursor) : ¬ strictBenefit cursor pricing n term term :=
  fun both => both.2 both.1
private theorem strictBenefit_trans {first middle last : Term cursor}
    (a : strictBenefit cursor pricing n first middle) (b : strictBenefit cursor pricing n middle last) :
    strictBenefit cursor pricing n first last := by
  refine ⟨fun table member => benefit_trans cursor (b.1 table member) (a.1 table member),?_⟩
  intro reverse
  exact a.2 (fun table member => benefit_trans cursor (reverse table member) (b.1 table member))

variable {cursor pricing n}
private structure Scanned {reference : Term cursor} (seed : Candidate cursor pricing n reference)
    (remaining : List (Candidate cursor pricing n reference)) where
  policy : Candidate cursor pricing n reference
  original : policy = seed ∨ policy ∈ remaining
  advances : policy = seed ∨ strictBenefit cursor pricing n seed.term policy.term
  maximal : ∀ other ∈ remaining, ¬ strictBenefit cursor pricing n policy.term other.term

private theorem cannot_improve_seed {reference : Term cursor} {seed : Candidate cursor pricing n reference}
    {remaining : List (Candidate cursor pricing n reference)} (result : Scanned seed remaining) :
    ¬ strictBenefit cursor pricing n result.policy.term seed.term := by
  intro backward
  rcases result.advances with same | forward
  · apply strictBenefit_irrefl cursor pricing n seed.term
    simpa only [same] using backward
  · exact strictBenefit_irrefl cursor pricing n seed.term (strictBenefit_trans cursor pricing n forward backward)

private def scan {reference : Term cursor} (seed : Candidate cursor pricing n reference) :
    (remaining : List (Candidate cursor pricing n reference)) → Scanned seed remaining
  | [] => ⟨seed,.inl rfl,.inl rfl,by simp⟩
  | head :: tail =>
    if improves : strictBenefit cursor pricing n seed.term head.term then
      let result := scan head tail
      { policy := result.policy
        original := .inr (by
          rcases result.original with same | inside
          · simpa only [same] using (List.mem_cons_self : head ∈ head :: tail)
          · exact List.mem_cons_of_mem _ inside)
        advances := .inr (by
          rcases result.advances with same | further
          · exact same.symm ▸ improves
          · exact strictBenefit_trans cursor pricing n improves further)
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other;exact cannot_improve_seed result
          · exact result.maximal other later }
    else
      let result := scan seed tail
      { policy := result.policy
        original := result.original.imp_right (List.mem_cons_of_mem _)
        advances := result.advances
        maximal := by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other
            intro backward
            rcases result.advances with same | forward
            · apply improves
              simpa only [same] using backward
            · exact improves (strictBenefit_trans cursor pricing n forward backward)
          · exact result.maximal other later }

variable (cursor pricing n)
/-- Execute the proved preorder directly; the order embedding remains the public Choice contract. -/
def fastChoose (reference : Term cursor) (pool : List (Candidate cursor pricing n reference)) :
    Option (Selected (axes cursor)
      (fun candidate : Candidate cursor pricing n reference => cost cursor pricing n candidate.term) pool) :=
  match same : pool with
  | [] => none
  | head :: tail =>
    let result := scan head tail
    some ⟨result.policy,by
      rcases result.original with h | h
      · simpa only [h] using (List.mem_cons_self : head ∈ head :: tail)
      · exact List.mem_cons_of_mem _ h,by
      intro other inside improves
      have strict : strictBenefit cursor pricing n result.policy.term other.term :=
        (strictBenefit_iff cursor pricing n _ _).mpr improves
      rcases List.mem_cons.mp inside with h | later
      · subst other;exact cannot_improve_seed result strict
      · exact result.maximal other later strict⟩

theorem fastChoose_none_iff_empty (reference : Term cursor) (pool : List (Candidate cursor pricing n reference)) :
    fastChoose cursor pricing n reference pool = none ↔ pool = [] := by
  unfold fastChoose
  split <;> simp_all

inductive Row where
  | present (table : Table cursor)
  | future (table : Table cursor) (word : List (Future.Recovery.Action cursor.model))
  | funding (table : Table cursor) (word : List (Future.Recovery.Action cursor.model))

def rows : List (Row cursor) := (tables cursor).flatMap fun table =>
  [.present table] ++ (Future.Recovery.capabilities cursor.model cursor.depth).map (.future table) ++
    (Future.Recovery.capabilities cursor.model cursor.depth).map (.funding table)

def Holds (reference term : Term cursor) : Row cursor → Prop
  | .present table => Synthesis.accepts cursor.source.val.code (Window.axes cursor.model cursor.depth)
      (tensor cursor pricing term (opponent cursor table) n).present
      (tensor cursor pricing reference (opponent cursor table) n).present
  | .future table word => futureNoWorse cursor
      ((tensor cursor pricing term (opponent cursor table) n).future cursor word)
      ((tensor cursor pricing reference (opponent cursor table) n).future cursor word)
  | .funding table word =>
      ((tensor cursor pricing reference (opponent cursor table) n).funding cursor word).isNone = true →
      ((tensor cursor pricing term (opponent cursor table) n).funding cursor word).isNone = true
instance (reference term : Term cursor) (row : Row cursor) : Decidable (Holds cursor pricing n reference term row) := by
  cases row <;> unfold Holds <;> infer_instance

theorem rows_iff (reference term : Term cursor) :
    (∀ row ∈ rows cursor, Holds cursor pricing n reference term row) ↔ NoWorse cursor pricing n term reference := by
  constructor
  · intro all table inside
    refine ⟨all (.present table) (by simp [rows,inside]),?_,?_⟩
    · intro word member;exact all (.future table word) (by simp [rows,inside,member])
    · intro word member;exact all (.funding table word) (by simp [rows,inside,member])
  · intro all row inside
    obtain ⟨table,member,generated⟩ := List.mem_flatMap.mp inside
    have valid := all table member
    simp only [List.mem_append,List.mem_singleton,List.mem_map] at generated
    rcases generated with (same | ⟨word,registered,same⟩) | ⟨word,registered,same⟩
    · subst row;exact valid.1
    · subst row;exact valid.2.1 word registered
    · subst row;exact valid.2.2 word registered

structure Rejection (reference term : Term cursor) where
  row : Row cursor
  original : row ∈ rows cursor
  broken : ¬ Holds cursor pricing n reference term row
inductive Outcome (reference : Term cursor) where
  | selected (choice : Choice cursor pricing n reference)
  | blocked (rejected : ∀ term : Term cursor, Rejection cursor pricing n reference term)

def compile (reference : Term cursor) : Outcome cursor pricing n reference :=
  match result : fastChoose cursor pricing n reference (candidates cursor pricing n reference) with
  | some choice => .selected choice
  | none => .blocked (fun term => match inspect (Holds cursor pricing n reference term) (rows cursor) with
      | .rejected row original broken => ⟨row,original,broken⟩
      | .accepted all => False.elim (by
          have empty := (fastChoose_none_iff_empty cursor pricing n reference _).mp result
          obtain ⟨candidate,member,_⟩ := every_accepted_term_is_generated cursor pricing n reference term
            ((rows_iff cursor pricing n reference term).mp all)
          rw [empty] at member
          exact List.not_mem_nil member))

theorem selected_has_no_full_responsibility_dominator (reference : Term cursor)
    (choice : Choice cursor pricing n reference) (other : Term cursor) :
    ¬ Better cursor pricing n choice.policy.term other := by
  intro improves
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated cursor pricing n reference other
    (noWorse_trans cursor pricing n improves.1 choice.policy.no_regression)
  apply choice.maximal candidate member
  change Improves (axes cursor) (cost cursor pricing n) choice.policy.term candidate.term
  rw [same]
  exact ⟨(vector_iff cursor pricing n _ _).mpr (no_worse_bounds_real_benefit cursor pricing n improves.1),
    fun reverse => improves.2 ((vector_iff cursor pricing n _ _).mp reverse)⟩

theorem every_available_real_improvement_is_realized (reference : Term cursor)
    (choice : Choice cursor pricing n reference)
    (available : ∃ term : Term cursor, Better cursor pricing n reference term) :
    Better cursor pricing n reference choice.policy.term := by
  refine ⟨choice.policy.no_regression,?_⟩
  intro reverse
  obtain ⟨term,improves⟩ := available
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated cursor pricing n reference term improves.1
  apply choice.maximal candidate member
  change Improves (axes cursor) (cost cursor pricing n) choice.policy.term candidate.term
  rw [same]
  refine ⟨(vector_iff cursor pricing n _ _).mpr ?_,?_⟩
  · intro table inside
    exact benefit_trans cursor (no_worse_bounds_real_benefit cursor pricing n improves.1 table inside) (reverse table inside)
  · intro backward
    apply improves.2
    intro table inside
    exact benefit_trans cursor (reverse table inside) ((vector_iff cursor pricing n _ _).mp backward table inside)

/-- A replacement planner is checked by a separate scan of all generated terms. -/
def verify (reference term : Term cursor) : Bool := decide (
  NoWorse cursor pricing n term reference ∧
  ∀ other ∈ terms cursor, NoWorse cursor pricing n other reference →
    ¬ strictBenefit cursor pricing n term other)

theorem verify_iff (reference term : Term cursor) : verify cursor pricing n reference term = true ↔
    NoWorse cursor pricing n term reference ∧
    ∀ other : Term cursor, NoWorse cursor pricing n other reference →
      ¬ Improves (axes cursor) (cost cursor pricing n) term other := by
  simp only [verify,decide_eq_true_eq,strictBenefit_iff]
  constructor
  · rintro ⟨accepted,maximal⟩;exact ⟨accepted,fun other => maximal other (List.mem_attach _ _)⟩
  · rintro ⟨accepted,maximal⟩;exact ⟨accepted,fun other _ => maximal other⟩

def choiceOfVerified (reference term : Term cursor)
    (verified : verify cursor pricing n reference term = true) : Choice cursor pricing n reference := by
  let checked := (verify_iff cursor pricing n reference term).mp verified
  let candidate : Candidate cursor pricing n reference := ⟨term,checked.1⟩
  refine ⟨candidate,?_,?_⟩
  · exact List.mem_filterMap.mpr ⟨term,List.mem_attach _ _,by simp [check,checked.1,candidate]⟩
  · intro other _;exact checked.2 other.term other.no_regression

theorem independent_replay_accepts_selection (reference : Term cursor)
    (choice : Choice cursor pricing n reference) : verify cursor pricing n reference choice.policy.term = true := by
  apply (verify_iff cursor pricing n reference _).mpr
  refine ⟨choice.policy.no_regression,?_⟩
  intro other accepted
  obtain ⟨candidate,member,same⟩ := every_accepted_term_is_generated cursor pricing n reference other accepted
  have maximal := choice.maximal candidate member
  change ¬ Improves (axes cursor) (cost cursor pricing n) choice.policy.term candidate.term at maximal
  simpa only [same] using maximal

theorem selection_compares_every_same_future_adaptive_opponent (reference : Term cursor)
    (choice : Choice cursor pricing n reference) (bounded : n ≤ cursor.state.remaining) :
    (∀ rival : Opponent cursor.source.val.code, accepts cursor
      (tensor cursor pricing choice.policy.term rival n) (tensor cursor pricing reference rival n)) ∧
    ∀ other : Term cursor, ¬ ((∀ rival : Opponent cursor.source.val.code, accepts cursor
      (tensor cursor pricing other rival n) (tensor cursor pricing choice.policy.term rival n)) ∧
      ¬ (∀ rival : Opponent cursor.source.val.code, benefit cursor
        (tensor cursor pricing choice.policy.term rival n) (tensor cursor pricing other rival n))) := by
  refine ⟨(finite_comparison_iff_every_same_adaptive_opponent cursor pricing n _ _ _ bounded).mp choice.policy.no_regression,?_⟩
  intro other improves
  apply selected_has_no_full_responsibility_dominator cursor pricing n reference choice other
  exact ⟨(finite_comparison_iff_every_same_adaptive_opponent cursor pricing n _ _ _ bounded).mpr improves.1,
    fun reverse => improves.2 ((finite_comparison_iff_every_same_adaptive_opponent cursor pricing n _ _ _ bounded).mp reverse)⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection
