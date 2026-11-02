import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Source
import SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed
import SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable (fuel : ℚ) (inputs : List (List Action))

abbrev mandateCurrentAt := Mandate.History.Runtime.currentAt (bound fuel) inputs
abbrev mandateWordAt := Mandate.History.Runtime.wordAt (bound fuel) inputs

structure TracedGrant (birth last : Nat) where
  private mk ::
  admission : AdmittedGrant base scope (mandateCurrentAt fuel inputs birth) (mandateWordAt fuel inputs birth)
  continuation : Lifecycle.Observed.History base scope (mandateCurrentAt fuel inputs)
    (mandateWordAt fuel inputs) birth admission.grant
  exact : continuation = Lifecycle.Observed.through last

def traceGrant (birth last : Nat)
    (grant : Grant base scope (mandateCurrentAt fuel inputs birth) (mandateWordAt fuel inputs birth)) :
    TracedGrant fuel inputs birth last :=
  ⟨admitGrant base scope _ _ grant, Lifecycle.Observed.through last, rfl⟩

def recordsAt (last : Nat) : List (Sigma fun birth : Fin (last + 1) => TracedGrant fuel inputs birth.val last) :=
  (List.finRange (last + 1)).flatMap fun birth =>
    (grantsAt base scope (mandateCurrentAt fuel inputs birth.val) (mandateWordAt fuel inputs birth.val)).map fun grant =>
      ⟨birth, traceGrant fuel inputs birth.val last grant⟩

abbrev account (ordinal : Nat) := Financial.accountAt (input fuel inputs) ordinal

noncomputable section

abbrev previousRoot := ProgrammeLiving.livingRoot (input fuel inputs)

/-- Each component is generated from this input's own actual prefix.
The full mandate Run retains the guarded refusal, beyond the kind readout. -/
structure Disposition (depth : Nat) where
  private mk ::
  services : (index : (source fuel).Slot) →
    OutstandingSource.History.NativeService.Prefix (source fuel) inputs index (depth + 2)
  mandates : List (Sigma fun birth : Fin (depth + 2) => TracedGrant fuel inputs birth.val (depth + 1))
  mandates_exact : mandates = recordsAt fuel inputs (depth + 1)
  decision : (source fuel).Decision (currentAt fuel inputs (depth + 2))
    (trailAt fuel inputs (depth + 2)).frame.payments
  decision_exact : decision = (source fuel).decideAt (currentAt fuel inputs (depth + 2))
    (trailAt fuel inputs (depth + 2)).frame.payments
  actual_word : inputs.length ≤ depth → (actualExecution fuel inputs (depth + 1)).submitted = decision.word
  actual_input : (inside : depth < inputs.length) → (actualExecution fuel inputs (depth + 1)).submitted = inputs[depth]
  actual_report : inputs.length ≤ depth →
    (OutstandingSource.History.writtenReceipt (source fuel) inputs (depth + 1)).val = decision.report
  completion_response : Option (ActualCompletion fuel inputs depth)
  completion_response_exact : completion_response = actualCompletionAt fuel inputs depth
  account : (Financial.process (input fuel inputs)).GeneratedState
  account_exact : account = Runtime.account fuel inputs (depth + 3)
  actual_matrix : Financial.BalanceConservation.ledgerClaims (input fuel inputs) account.current =
    (currentAt fuel inputs (depth + 3)).claims
  actual_crossing : (Financial.process (input fuel inputs)).Run
    (Runtime.account fuel inputs (depth + 2)).current account.current
  original_claims : (Runtime.account fuel inputs (depth + 2)).current.slots.map (Financial.slotClaim (input fuel inputs)) <+:
    account.current.slots.map (Financial.slotClaim (input fuel inputs))

def generate (depth : Nat) : Disposition fuel inputs depth :=
  ⟨fun index => OutstandingSource.History.NativeService.historyAt (source fuel) inputs index (depth + 2),
    recordsAt fuel inputs (depth + 1), rfl,
    (source fuel).decideAt (currentAt fuel inputs (depth + 2)) (trailAt fuel inputs (depth + 2)).frame.payments,
    rfl, OutstandingSource.History.residual_is_actually_emitted _ _ depth,
    OutstandingSource.History.scheduled_input_is_actual _ _ depth,
    residual_report_is_the_actual_original_row fuel inputs depth,
    actualCompletionAt fuel inputs depth, rfl,
    account fuel inputs (depth + 3), rfl,
    Financial.BalanceConservation.generated_prefix_claims _ (zero_financial_genesis fuel inputs) _,
    Financial.BalanceConservation.fromActualCut _ (depth + 2) 1,
    Financial.BalanceConservation.cut_preserves_all_original_claims _ (depth + 2) 1⟩

theorem every_original_grant_is_retained (last : Nat) (birth : Fin (last + 1))
    (grant : Grant base scope (mandateCurrentAt fuel inputs birth.val) (mandateWordAt fuel inputs birth.val))
    (actual : grant ∈ grantsAt base scope (mandateCurrentAt fuel inputs birth.val) (mandateWordAt fuel inputs birth.val)) :
    (⟨birth, traceGrant fuel inputs birth.val last grant⟩ :
      Sigma fun birth : Fin (last + 1) => TracedGrant fuel inputs birth.val last) ∈ recordsAt fuel inputs last := by
  apply List.mem_flatMap.mpr
  exact ⟨birth, List.mem_finRange _, List.mem_map.mpr ⟨grant, actual, rfl⟩⟩

theorem every_mandate_retains_original_admission (last : Nat)
    (record : Sigma fun birth : Fin (last + 1) => TracedGrant fuel inputs birth.val last) :
    record.2.continuation.state.LiveAt 0 ∧
    HEq record.2.continuation.obligation.admission
      (Lifecycle.original base scope (mandateCurrentAt fuel inputs) (mandateWordAt fuel inputs)
        record.1.val record.2.admission.grant).admission :=
  ⟨record.2.continuation.responsibility_remains_live, record.2.continuation.original_admission⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input fuel inputs)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (depth : Nat) →
    current = (ProgrammeHistory.visitAt (input fuel inputs) (depth + 2)).current → Disposition fuel inputs depth
  project := fun _ {_} _ _ depth _own => generate fuel inputs depth

def root := (previousRoot fuel inputs).withProjectionCoface (projectionLaw fuel inputs)

theorem root_is_its_own_emitting_source : (root fuel inputs).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (input fuel inputs)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input fuel inputs)) :=
  ⟨ProgrammeSource.V (input fuel inputs), root fuel inputs, ProgrammeHistory.temporalVisit (input fuel inputs) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (input fuel inputs)) where
  State := Nat
  stateAt := stateAt fuel inputs
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input fuel inputs)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (input fuel inputs) first).current =
        (ProgrammeHistory.visitAt (input fuel inputs) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (input fuel inputs) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | joint

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input fuel inputs)) where
  process := process fuel inputs
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => ProgrammeLiving.projectionLaw (input fuel inputs)
    | .joint => projectionLaw fuel inputs
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (previousRoot fuel inputs).toAuthoritativeRoot.source (projectionLaw fuel inputs)
    | joint =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot fuel inputs).toAuthoritativeRoot.source (projectionLaw fuel inputs)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .joint => ()

def activated (ordinal : Nat) : LivingRuntimeState (process fuel inputs) := (facade fuel inputs).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated fuel inputs ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem payload_is_the_actual_joint_disposition (depth : Nat) :
    (projectionLaw fuel inputs).project ()
      (ProgrammeSource.emitted (input fuel inputs) (ProgrammeHistory.visitAt (input fuel inputs) (depth + 2)).current)
      () depth rfl = generate fuel inputs depth := rfl


end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Runtime
