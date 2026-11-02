import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}


variable {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}

inductive Axis (all : Candidates source catalogue) where
  | original (axis : Automatic.Axis all)
  | work (index : Index prepared)
  | credit (index : Index prepared)

def axes (all : Candidates source catalogue) : List (Axis all) :=
  (Automatic.axes all).map Axis.original ++ (keys prepared).flatMap fun index => [.work index,.credit index]
def cost (candidate : Candidate all) : Axis all → ℚ
  | .original axis => Automatic.cost all candidate.policy.policy axis
  | .work index => candidate.work index
  | .credit index => -(candidate.credit index : ℚ)

def ResponsibilityLe (new previous : Candidate all) : Prop :=
  Automatic.Benefit all new.policy.policy previous.policy.policy ∧
    ∀ index : Index prepared,new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index

theorem vector_iff (new previous : Candidate all) :
    Distributed.NoWorse (axes all) cost new previous ↔ ResponsibilityLe new previous := by
  constructor
  · intro checked
    constructor
    · apply (Automatic.vector_iff all _ _).mp
      intro axis inside
      exact checked (.original axis) (List.mem_append_left _ (List.mem_map.mpr ⟨axis,inside,rfl⟩))
    · intro index
      have work := checked (.work index) (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,by simp⟩))
      have credit := checked (.credit index) (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨index,List.mem_finRange _,by simp⟩))
      constructor
      · change (new.work index : ℚ) ≤ (previous.work index : ℚ) at work
        exact_mod_cast work
      · change -(new.credit index : ℚ) ≤ -(previous.credit index : ℚ) at credit
        have order := neg_le_neg_iff.mp credit
        exact_mod_cast order
  · rintro ⟨original,construction⟩ axis inside
    cases axis with
    | original axis =>
      exact (Automatic.vector_iff all _ _).mpr original axis (by simpa [axes] using inside)
    | work index =>
      change (new.work index : ℚ) ≤ (previous.work index : ℚ)
      exact_mod_cast (construction index).1
    | credit index =>
      change -(new.credit index : ℚ) ≤ -(previous.credit index : ℚ)
      apply neg_le_neg
      exact_mod_cast (construction index).2

theorem responsibility_iff_every_same_adaptive_opponent (new previous : Candidate all) : ResponsibilityLe new previous ↔
    (∀ index : Index prepared,∀ opponent : Opponent (Policy.initial input prepared.saved[index].point).source.val.code,
      benefit (Policy.initial input prepared.saved[index].point) ((new.policy.policy.view index).tensor opponent)
        ((previous.policy.policy.view index).tensor opponent)) ∧
    (∀ index : Index prepared,new.work index ≤ previous.work index ∧ previous.credit index ≤ new.credit index) := by
  exact and_congr (Automatic.benefit_iff_every_same_adaptive_opponent all _ _) Iff.rfl

abbrev Selected (items : List (Report all)) := Distributed.Selected (axes all) cost (candidates items)
structure Refined (items : List (Report all)) (reference : Candidate all) where
  private mk ::
  selected : Selected items
  no_worse : Distributed.NoWorse (axes all) cost selected.policy reference

private def refineFrom (items : List (Report all)) (sourcePool : List (Candidate all)) (exact_source : sourcePool = candidates items)
    (reference : Candidate all) (listed : reference ∈ sourcePool) : Refined items reference :=
  let pool := sourcePool.filter (fun candidate => decide (Distributed.NoWorse (axes all) cost candidate reference))
  match found : Distributed.choose (axes all) cost pool with
  | none => False.elim (by
      have empty := (Distributed.choose_none_iff_empty _ _ _).mp found
      have self : reference ∈ pool := List.mem_filter.mpr ⟨listed,decide_eq_true (by intro axis _;exact le_refl _)⟩
      rw [empty] at self
      cases self)
  | some selected =>
      let accepted := List.mem_filter.mp selected.original
      let retained := of_decide_eq_true accepted.2
      ⟨⟨selected.policy,(by rw [←exact_source];exact accepted.1),by
          intro other original strict
          apply selected.maximal other (List.mem_filter.mpr ⟨(by rw [exact_source];exact original),decide_eq_true (Distributed.noWorse_trans strict.1 retained)⟩)
          exact strict⟩,retained⟩

def refine (items : List (Report all)) (reference : Candidate all) (listed : reference ∈ candidates items) : Refined items reference :=
  refineFrom items (candidates items) rfl reference listed

theorem every_available_strict_improvement_is_selected (items : List (Report all)) (reference : Candidate all)
    (listed : reference ∈ candidates items)
    (available : ∃ other ∈ candidates items,Distributed.Improves (axes all) cost reference other) :
    Distributed.Improves (axes all) cost reference (refine items reference listed).selected.policy := by
  refine ⟨(refine items reference listed).no_worse,?_⟩
  intro backwards
  obtain ⟨other,original,strict⟩ := available
  apply (refine items reference listed).selected.maximal other original
  exact ⟨Distributed.noWorse_trans strict.1 backwards,fun reverse =>
    strict.2 (Distributed.noWorse_trans backwards reverse)⟩

def verify (items : List (Report all)) (candidate : Candidate all) : Bool :=
  decide (∀ other ∈ candidates items,¬ Distributed.Improves (axes all) cost candidate other)
theorem independent_verification_accepts (items : List (Report all)) (chosen : Selected items) : verify items chosen.policy = true :=
  decide_eq_true chosen.maximal

def replaceByVerified (items : List (Report all)) (position : Fin (candidates items).length)
    (accepted : verify items (candidates items)[position] = true) : Selected items :=
  ⟨(candidates items)[position],List.getElem_mem position.isLt,of_decide_eq_true accepted⟩

def verifyRefinement (items : List (Report all)) (reference candidate : Candidate all) : Bool :=
  decide ((∀ other ∈ candidates items,¬ Distributed.Improves (axes all) cost candidate other) ∧
    Distributed.NoWorse (axes all) cost candidate reference)

theorem independent_refinement_verification_accepts (items : List (Report all)) (reference : Candidate all)
    (chosen : Refined items reference) : verifyRefinement items reference chosen.selected.policy = true :=
  decide_eq_true ⟨chosen.selected.maximal,chosen.no_worse⟩

def refinementOfVerified (items : List (Report all)) (reference : Candidate all) (position : Fin (candidates items).length)
    (accepted : verifyRefinement items reference (candidates items)[position] = true) : Refined items reference :=
  let checked : (∀ other ∈ candidates items,¬ Distributed.Improves (axes all) cost (candidates items)[position] other) ∧
      Distributed.NoWorse (axes all) cost (candidates items)[position] reference := of_decide_eq_true accepted
  ⟨replaceByVerified items position (decide_eq_true checked.1),checked.2⟩

inductive Verdict (items : List (Report all)) where
  | selected (choice : Selected items)
  | blocked (empty : candidates items = [])

structure Result (items : List (Report all)) where
  private mk ::
  book : Book items
  verdict : Verdict items

def compile (items : List (Report all)) : Result items :=
  let book := generateBook items
  match pool : book.pool with
  | [] => ⟨book,.blocked (by rw [←book.pool_exact];exact pool)⟩
  | reference::rest =>
      let listed : reference ∈ book.pool := by rw [pool];exact List.mem_cons_self
      ⟨book,.selected (refineFrom items book.pool book.pool_exact reference listed).selected⟩

theorem compile_keeps_the_exact_generated_directory (items : List (Report all)) :
    (compile items).book.entries = directory items := by
  unfold compile
  dsimp only
  split <;> rfl

theorem empty_pool_has_a_failure_for_every_report (items : List (Report all)) (empty : candidates items = [])
    (row : Row all) (original : row ∈ directory items) : row.2.accept? = none := by
  cases actual : row.2.accept? with
  | none => rfl
  | some candidate =>
    have accepted := every_ready_entry_is_in_the_pool items row original candidate actual
    rw [empty] at accepted
    cases accepted

theorem selected_preserves_full_original_responsibility_and_new_costs (items : List (Report all))
    (reference : Candidate all) (listed : reference ∈ candidates items) :
    ResponsibilityLe (refine items reference listed).selected.policy reference :=
  (vector_iff _ _).mp (refine items reference listed).no_worse

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting
