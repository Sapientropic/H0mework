import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Reserve
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.ExitCapacity.Continuation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme.Completion.Runtime

/-! The actual direct replacement is accepted as material-preserving only
with physical exit supplies after its service and debt response. Every other
outcome retains its complete actual packet and its independent obstruction. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)

abbrev completion := Programme.Completion.produce inventory
abbrev packet := (completion inventory).packet
abbrev after := current (packet inventory).1 (packet inventory).2.inputs

structure ReplacementWitness where
  private mk ::
  paid : (completion inventory).decision.kind = .paid
  healthy : ExitCapacity.Nonnegative (after inventory)
  available : ExitCapacity.Envelope (after inventory)

structure ObstructionDisposition where
  private mk ::
  healthy : ExitCapacity.Nonnegative (after inventory)
  cold : ¬ ExitCapacity.Envelope (after inventory)
  allContinuations : ∀ history : List (Epoch × List Action), ∀ future : Epoch, ∀ actor,
    ¬ (Mandate.law base future.scope).Valid (ExitCapacity.continuation (after inventory) history)
      (request future.scope (ExitCapacity.continuation (after inventory) history) actor .exit)

inductive Kind where
  | preserving | originalBlocked | materialBlocked | invalidStock
  deriving DecidableEq

inductive Result where
  | private preserving (witness : ReplacementWitness inventory)
  | private originalBlocked (reason : (completion inventory).decision.kind ≠ .paid)
  | private materialBlocked (paid : (completion inventory).decision.kind = .paid)
      (obstruction : ObstructionDisposition inventory)
  | private invalidStock (paid : (completion inventory).decision.kind = .paid)
      (reason : ¬ ExitCapacity.Nonnegative (after inventory))

theorem every_paid_completion_really_retains_exit_material
    (paid : (completion inventory).decision.kind = .paid) :
    ExitCapacity.Nonnegative (after inventory) ∧ ExitCapacity.Envelope (after inventory) := by
  dsimp only [after,packet,Programme.Completion.Disposition.packet]
  generalize actual : (completion inventory).decision = decision at paid ⊢
  cases decision
  next next =>
    exact Handoff.selected_actual_service_and_response_preserve_exit_material next.fresh next.payment next.selected
  next absent reason => cases paid
  next fresh chosen absent failure methods => cases paid

def generate : Result inventory :=
  if paid : (completion inventory).decision.kind = .paid then
    let material := every_paid_completion_really_retains_exit_material inventory paid
    .preserving ⟨paid,material.1,material.2⟩
  else .originalBlocked paid

def Result.kind : Result inventory → Kind
  | .preserving .. => .preserving
  | .originalBlocked .. => .originalBlocked
  | .materialBlocked .. => .materialBlocked
  | .invalidStock .. => .invalidStock

theorem every_paid_completion_generates_a_preserving_replacement
    (paid : (completion inventory).decision.kind = .paid) :
    (generate inventory).kind inventory = .preserving := by
  simp only [generate,dif_pos paid,Result.kind]

theorem ReplacementWitness.accepted_replacement_preserves_exit_material_capacity (witness : ReplacementWitness inventory) :
    ExitCapacity.Envelope (current epoch (Programme.produce inventory).finalInventory.inputs) →
      ExitCapacity.Envelope (after inventory) := fun _ => witness.available

theorem ReplacementWitness.every_actual_holder_can_generate_a_legal_paid_exit
    (witness : ReplacementWitness inventory) (actor : Bool)
    (holder : (after inventory).technology.holder = some actor) :
    (choose (packet inventory).1 .exit (after inventory)).isSome = true :=
  ExitCapacity.source_material_envelope_generates_a_real_exit _ _ actor holder
    (witness.healthy actor .service) witness.available

theorem ReplacementWitness.same_source_task_homology_and_actual_service
    (witness : ReplacementWitness inventory) :
    ∃ next : Programme.Completion.PaidNext (Programme.produce inventory),
      packet inventory = next.packet ∧
      ∀ index : epoch.source.Slot,
        (Handoff.source next.fresh).seed.slot (Handoff.homologous next.fresh index) = epoch.source.seed.slot index ∧
        Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (Handoff.law next.fresh)
          (Handoff.actual next.fresh 1).before (Handoff.actual next.fresh 1).submitted
          (epoch.source.seed.slot index).bearer (epoch.source.seed.slot index).goods (epoch.source.seed.slot index).purpose := by
  have paid := witness.paid
  dsimp only [packet,Programme.Completion.Disposition.packet]
  generalize actual : (completion inventory).decision = decision at paid ⊢
  cases decision
  next next =>
    refine ⟨next,rfl,fun index => ⟨?_,next.all_original_service_slots_are_paid index⟩⟩
    exact Handoff.original_slot_content_is_preserved next.fresh index
  next absent reason => cases paid
  next fresh chosen absent failure methods => cases paid

theorem Result.preserving_has_a_real_witness (result : Result inventory)
    (accepted : result.kind inventory = .preserving) : Nonempty (ReplacementWitness inventory) := by
  cases result
  next witness => exact ⟨witness⟩
  next reason => cases accepted
  next paid obstruction => cases accepted
  next paid reason => cases accepted

theorem Result.material_blocker_is_independent_of_the_finite_candidate_menu (result : Result inventory)
    (blocked : result.kind inventory = .materialBlocked) :
    ExitCapacity.total (after inventory) .service < 1 ∧
    ExitCapacity.total (after inventory) .feedstock < 1 ∧
    ∀ history : List (Epoch × List Action), ∀ future : Epoch, ∀ actor,
      ¬ (Mandate.law base future.scope).Valid (ExitCapacity.continuation (after inventory) history)
        (request future.scope (ExitCapacity.continuation (after inventory) history) actor .exit) := by
  cases result
  next witness => cases blocked
  next reason => cases blocked
  next paid obstruction =>
    have gap : ExitCapacity.total (after inventory) .service < 1 ∧
        ExitCapacity.total (after inventory) .feedstock < 1 := by
      simpa only [ExitCapacity.Envelope,not_or,not_le] using obstruction.cold
    exact ⟨gap.1,gap.2,obstruction.allContinuations⟩
  next paid reason => cases blocked

structure Disposition where
  private mk ::
  original : Programme.Completion.Disposition inventory
  original_exact : original = completion inventory
  replacement : Result inventory
  replacement_exact : replacement = generate inventory

def produce : Disposition inventory := ⟨completion inventory,rfl,generate inventory,rfl⟩

variable {inventory}

def Disposition.packet (result : Disposition inventory) := result.original.packet

def Disposition.financialRun (result : Disposition inventory) := result.original.financialRun

theorem Disposition.every_past_cohort_continues (result : Disposition inventory) :
    inventory.pastGrants.map GrantCohort.origin <+: result.packet.2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: result.packet.2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: result.packet.2.pastServices.map ServiceCohort.origin :=
  result.original.every_past_cohort_continues

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Replacement
