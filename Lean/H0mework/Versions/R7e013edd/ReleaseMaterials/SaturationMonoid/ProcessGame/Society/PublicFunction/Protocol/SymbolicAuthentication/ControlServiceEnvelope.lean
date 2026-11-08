import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeliveryControlTree

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceEnvelope
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

abbrev atCut := UnifiedRunPrefix.atCut model start vocabulary encoding law
abbrev Stages := JointResponse.Stages model

namespace Budget

def common (cases : List (Stages model)) (first : Nat) : Finset Party :=
  (Finset.univ.image model.source.code.siteParty).filter fun actor => cases.all fun past =>
    decide (actor ∈ ServiceActorEnvelope.candidates model start vocabulary encoding law past first)

def possible (cases : List (Stages model)) (first width : Nat) : Finset Party :=
  cases.foldr (fun past found => ServiceActorEnvelope.affected model start vocabulary encoding law past first width ∪ found) ∅

def communication (cases : List (Stages model)) (first width : Nat) : Bool :=
  cases.all fun past => (List.range width).all fun offset =>
    if JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (first+offset))
    then true else decide (UnifiedResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law past (first+offset)) ∧
      JointResponse.queueClear model start (atCut model start vocabulary encoding law past (first+offset)) = true)

def check (cases : List (Stages model)) (first width : Nat) : Bool :=
  decide ((possible model start vocabulary encoding law cases first width).card <
    (common model start vocabulary encoding law cases first).card) && communication model start vocabulary encoding law cases first width

theorem common_is_present_in_every_source_case (cases : List (Stages model)) (first : Nat) (past : Stages model)
    (inside : past ∈ cases) : common model start vocabulary encoding law cases first ⊆
      ServiceActorEnvelope.candidates model start vocabulary encoding law past first := by
  intro actor member
  exact of_decide_eq_true (List.all_eq_true.mp (Finset.mem_filter.mp member).2 past inside)

theorem each_actual_loss_is_within_the_possible_source_loss (cases : List (Stages model)) (first width : Nat)
    (past : Stages model) (inside : past ∈ cases) :
    ServiceActorEnvelope.affected model start vocabulary encoding law past first width ⊆
      possible model start vocabulary encoding law cases first width := by
  induction cases with
  | nil => cases inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst past
      exact Finset.subset_union_left
    · exact (ih later).trans Finset.subset_union_right

theorem possible_has_an_actual_admitted_case_origin (values : List (Stages model)) (first width : Nat) (actor : Party) :
    actor ∈ possible model start vocabulary encoding law values first width ↔
      ∃ branch ∈ values, actor ∈ ServiceActorEnvelope.affected model start vocabulary encoding law branch first width := by
  induction values with
  | nil => simp only [possible,List.foldr_nil,Finset.notMem_empty,List.not_mem_nil,false_and,exists_false]
  | cons head tail ih =>
    simp only [possible,List.foldr_cons,Finset.mem_union] at ih ⊢
    rw [ih]
    simp only [List.mem_cons,exists_eq_or_imp]

theorem a_checked_source_budget_generates_each_actual_surplus (cases : List (Stages model)) (first width : Nat)
    (checked : check model start vocabulary encoding law cases first width = true)
    (past : Stages model) (inside : past ∈ cases) :
    (ServiceActorEnvelope.affected model start vocabulary encoding law past first width).card <
      (ServiceActorEnvelope.candidates model start vocabulary encoding law past first).card := by
  have surplus := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  have lower := Finset.card_le_card (common_is_present_in_every_source_case model start vocabulary encoding law cases first past inside)
  have upper := Finset.card_le_card (each_actual_loss_is_within_the_possible_source_loss model start vocabulary encoding law cases first width past inside)
  omega

theorem a_checked_source_domain_generates_each_actual_communication_gate
    (cases : List (Stages model)) (first width : Nat)
    (checked : check model start vocabulary encoding law cases first width = true)
    (past : Stages model) (inside : past ∈ cases) (offset : Nat) (bounded : offset < width)
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (first+offset))) :
    UnifiedResponse.Clear model start vocabulary encoding law (atCut model start vocabulary encoding law past (first+offset)) ∧
      JointResponse.queueClear model start (atCut model start vocabulary encoding law past (first+offset)) = true := by
  have scanned := List.all_eq_true.mp (Bool.and_eq_true_iff.mp checked).2 past inside
  have here := List.all_eq_true.mp scanned offset (List.mem_range.mpr bounded)
  simp only [if_neg unfinished] at here
  exact of_decide_eq_true here
end Budget

-- Full profiles include completed cases too. The pending restriction is used
-- only by the original endpoint-conditional service obligation.
def cases (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) : List (Stages model) :=
  (DeliveryControlTree.branches controls past).filter fun branch =>
    !pendingOnly || decide (¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law branch (first+width)))

abbrev common (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) :=
  Budget.common model start vocabulary encoding law (cases model start vocabulary encoding law past controls first width pendingOnly) first
abbrev possible (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) :=
  Budget.possible model start vocabulary encoding law (cases model start vocabulary encoding law past controls first width pendingOnly) first width
abbrev check (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) :=
  Budget.check model start vocabulary encoding law (cases model start vocabulary encoding law past controls first width pendingOnly) first width

structure Covered (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) where
  private mk ::
  checked : check model start vocabulary encoding law past controls first width pendingOnly = true

inductive Obstruction where
  | noCommonIdentity | identityBudgetExhausted | communication
  deriving DecidableEq
inductive Result (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) where
  | covered (source : Covered model start vocabulary encoding law past controls first width pendingOnly)
  | blocked (reason : Obstruction)

def produce (past : Stages model) (controls first width : Nat) (pendingOnly : Bool) :
    Result model start vocabulary encoding law past controls first width pendingOnly :=
  if checked : check model start vocabulary encoding law past controls first width pendingOnly = true then .covered ⟨checked⟩ else
  if common model start vocabulary encoding law past controls first width pendingOnly = ∅ then .blocked .noCommonIdentity else
  if (possible model start vocabulary encoding law past controls first width pendingOnly).card ≥
      (common model start vocabulary encoding law past controls first width pendingOnly).card then .blocked .identityBudgetExhausted
  else .blocked .communication

theorem a_successful_source_check_returns_its_own_coverage
    (past : Stages model) (controls first width : Nat) (pendingOnly : Bool)
    (checked : check model start vocabulary encoding law past controls first width pendingOnly = true) :
    ∃ source, produce model start vocabulary encoding law past controls first width pendingOnly = .covered source := by
  unfold produce
  rw [dif_pos checked]
  exact ⟨_,rfl⟩

theorem an_actual_source_selector_belongs_to_its_covered_cases
    (past : Stages model) (controls first width : Nat) (pendingOnly : Bool)
    (choose : Nat → DeliveryControlTree.Stages model.source.code → DeliveryControlTree.Command model.source.code)
    (index : Nat)
    (openCut : pendingOnly = true → ¬ JointResponse.Clear model start vocabulary encoding law
      (atCut model start vocabulary encoding law (DeliveryControlTree.run choose controls index past) (first+width))) :
    DeliveryControlTree.run choose controls index past ∈ cases model start vocabulary encoding law past controls first width pendingOnly := by
  apply List.mem_filter.mpr
  refine ⟨DeliveryControlTree.every_adaptive_source_choice_is_in_the_generated_tree choose controls index past,?_⟩
  cases pendingOnly <;> simp_all

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceEnvelope
