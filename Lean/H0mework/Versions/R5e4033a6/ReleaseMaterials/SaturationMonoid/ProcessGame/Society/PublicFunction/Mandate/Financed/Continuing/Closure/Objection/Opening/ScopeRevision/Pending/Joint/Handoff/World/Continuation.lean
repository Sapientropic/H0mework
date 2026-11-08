import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Failure
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Effects

/-! The actual handoff and the new epoch's own paid/failed word are consumed
together. Every branch retains the complete generated next inventory. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

structure PaidReplacement where
  private mk ::
  fresh : Handoff.Ready epoch.bound (reviewed inventory).inputs
  chosen : Handoff.choose epoch.bound (reviewed inventory).inputs = some fresh
  payment : Handoff.Paid fresh (Handoff.start fresh)
  selected : Handoff.select fresh (Handoff.start fresh) = some payment
  opening : Handoff.PaidOpening fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted
  origin : (handoff (reviewed inventory) fresh).originOpening.paidOpening? fresh = some opening

def PaidReplacement.packet (replacement : PaidReplacement inventory) : Packet :=
  ⟨Epoch.ofFresh replacement.fresh,handoff (reviewed inventory) replacement.fresh⟩

theorem PaidReplacement.actual_service (replacement : PaidReplacement inventory) :
    (∀ item ∈ (Handoff.law replacement.fresh).rawItems (Handoff.actual replacement.fresh 1).before
      (Handoff.actual replacement.fresh 1).submitted, (Handoff.law replacement.fresh).Valid item.before item.request) ∧
    ServiceAdequate (Handoff.law replacement.fresh) (Handoff.actual replacement.fresh 1).before
      replacement.fresh.task (Handoff.actual replacement.fresh 1).submitted :=
  Handoff.selected_word_really_pays replacement.fresh replacement.payment replacement.selected

theorem PaidReplacement.original_task_service (replacement : PaidReplacement inventory) (index : epoch.source.Slot) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (Handoff.law replacement.fresh)
      (Handoff.actual replacement.fresh 1).before (Handoff.actual replacement.fresh 1).submitted
      (epoch.source.seed.slot index).bearer (epoch.source.seed.slot index).goods (epoch.source.seed.slot index).purpose := by
  have paid := (replacement.actual_service inventory).2.2.2
    ((Handoff.source replacement.fresh).seed.slot (Handoff.homologous replacement.fresh index))
    (List.getElem_mem (Handoff.homologous replacement.fresh index).isLt)
  rw [Handoff.original_slot_content_is_preserved replacement.fresh index] at paid
  exact paid

inductive ContinuationDecision where
  | private paid (replacement : PaidReplacement inventory)
  | private reviewBlocked (absent : Handoff.choose epoch.bound (reviewed inventory).inputs = none)
      (reason : Handoff.Blocked epoch.bound (reviewed inventory).inputs)
  | private replacementBlocked (fresh : Handoff.Ready epoch.bound (reviewed inventory).inputs)
      (chosen : Handoff.choose epoch.bound (reviewed inventory).inputs = some fresh)
      (absent : Handoff.select fresh (Handoff.start fresh) = none)
      (actual : Handoff.Failure fresh (Handoff.actual fresh 1).before (Handoff.actual fresh 1).submitted)
      (methods : (method : Handoff.Method) → method ∈ Handoff.methods →
        Handoff.Failure fresh (Handoff.start fresh) (Handoff.candidate fresh (Handoff.start fresh) method))

inductive ContinuationKind where
  | paid | reviewBlocked | replacementBlocked
  deriving DecidableEq

def ContinuationDecision.kind : ContinuationDecision inventory → ContinuationKind
  | .paid .. => .paid
  | .reviewBlocked .. => .reviewBlocked
  | .replacementBlocked .. => .replacementBlocked

def ContinuationDecision.packet : ContinuationDecision inventory → Packet
  | .paid replacement => replacement.packet inventory
  | .reviewBlocked .. => ⟨epoch,reviewed inventory⟩
  | .replacementBlocked fresh .. => ⟨Epoch.ofFresh fresh,handoff (reviewed inventory) fresh⟩

def continuationDecision : ContinuationDecision inventory := by
  cases cycleResult inventory
  next fresh chosen saved exact =>
    subst saved
    cases plan : (handoff (reviewed inventory) fresh).originOpening
    next payment selected opening =>
      exact .paid ⟨fresh,chosen,payment,selected,opening,by rw [plan]; rfl⟩
    next absent failed =>
      exact .replacementBlocked fresh chosen absent (Handoff.actualFailure fresh absent)
        (fun method listed => Handoff.failedMethod fresh absent method listed)
  next absent reason => exact .reviewBlocked absent reason

theorem ContinuationDecision.packet_is_the_actual_next (decision : ContinuationDecision inventory) :
    decision.packet inventory = next inventory := by
  cases decision
  next replacement =>
    exact (generated_packet_of_selected (reviewed inventory) replacement.fresh replacement.chosen).symm
  next absent reason =>
    change ⟨epoch,reviewed inventory⟩ = (generate (reviewed inventory)).packet _
    unfold generate
    split
    next fresh selected => cases absent.symm.trans selected
    next none => rfl
  next fresh chosen absent actual methods =>
    exact (generated_packet_of_selected (reviewed inventory) fresh chosen).symm

structure ContinuationDisposition where
  private mk ::
  review : ReviewOutcome inventory
  review_exact : review = reviewOutcome inventory
  decision : ContinuationDecision inventory
  decision_exact : decision = continuationDecision inventory

def produceContinuation : ContinuationDisposition inventory :=
  ⟨reviewOutcome inventory,rfl,continuationDecision inventory,rfl⟩

def ContinuationDisposition.packet (disposition : ContinuationDisposition inventory) := disposition.decision.packet inventory

theorem ContinuationDisposition.next_exact (disposition : ContinuationDisposition inventory) :
    disposition.packet inventory = next inventory := disposition.decision.packet_is_the_actual_next inventory

def ContinuationDisposition.financialRun (disposition : ContinuationDisposition inventory) :
    (Financial.Family.process sources).Run inventory.finance.current (disposition.packet inventory).2.finance.current := by
  rw [disposition.next_exact]
  exact nextFinancialRun inventory

theorem ContinuationDisposition.all_past_cohorts_continue (disposition : ContinuationDisposition inventory) :
    inventory.pastGrants.map GrantCohort.origin <+: (disposition.packet inventory).2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: (disposition.packet inventory).2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: (disposition.packet inventory).2.pastServices.map ServiceCohort.origin := by
  rw [disposition.next_exact]
  exact next_preserves_all_original_cohort_prefixes inventory

theorem ContinuationDisposition.complete_matrix (disposition : ContinuationDisposition inventory) :
    Financial.Family.ledgerClaims sources (disposition.packet inventory).2.finance.current =
      (current (disposition.packet inventory).1 (disposition.packet inventory).2.inputs).claims :=
  (disposition.packet inventory).2.matrix

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
