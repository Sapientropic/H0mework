import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Grants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopePendingRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Objection.Followup Objection.Opening
variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : ScopeRevision.Ready inventory) (inputs : List (List Action))
noncomputable section

structure Disposition where
  private mk ::
  inherited : ScopeRevision.Ready inventory
  inherited_exact : inherited = ready
  oldJoint : JointRuntime.Disposition inventory (ScopeRevision.emit inventory)
  oldJoint_exact : oldJoint = JointRuntime.generate inventory (ScopeRevision.emit inventory)
  oldNative : Runtime.Disposition fuel (ScopeRevision.advance inventory).inputs inventory.cut.depth
  oldNative_exact : oldNative = ScopeRevision.legacy ready
  initial_exact : (ScopeRevision.Pending.sourceInput ready inputs).initial = (ScopeRevision.advance inventory).cut.past.frame.raw
  serviceBefore : (index : (ScopeRevision.epochSource ready).Slot) →
    OutstandingSource.History.NativeService.Prefix (ScopeRevision.epochSource ready) inputs index (inputs.length + 1)
  serviceBefore_exact : ∀ index, serviceBefore index =
    OutstandingSource.History.NativeService.historyAt (ScopeRevision.epochSource ready) inputs index (inputs.length + 1)
  serviceAfter : (index : (ScopeRevision.epochSource ready).Slot) →
    OutstandingSource.History.NativeService.Prefix (ScopeRevision.epochSource ready) (ScopeRevision.Pending.nextInputs ready inputs)
      index (inputs.length + 2)
  serviceAfter_exact : ∀ index, serviceAfter index =
    OutstandingSource.History.NativeService.historyAt (ScopeRevision.epochSource ready) (ScopeRevision.Pending.nextInputs ready inputs)
      index (inputs.length + 2)
  grants : List (Mandate.Challenge.Cross.GrantContinuation (ScopeRevision.epochBound ready) inputs (ScopeRevision.Pending.emit ready inputs))
  grants_exact : grants = Mandate.Challenge.Cross.grantContinuations (ScopeRevision.epochBound ready) inputs (ScopeRevision.Pending.emit ready inputs)
  objections : List (Mandate.Challenge.Cross.Resident (ScopeRevision.epochBound ready) (ScopeRevision.Pending.nextInputs ready inputs))
  objections_exact : objections = ScopeRevision.Pending.allResidents ready inputs
  financial_support : ScopeRevision.Pending.SilentPast inputs →
    Financial.BalanceConservation.ledgerClaims (I fuel (ScopeRevision.advance inventory).inputs) oldNative.account.current =
      (ScopeRevision.Pending.afterCurrent ready inputs).claims
  outcome : ScopeRevision.Pending.Outcome ready inputs
  outcome_exact : outcome = ScopeRevision.Pending.outcome ready inputs

def generate : Disposition ready inputs :=
  ⟨ready, rfl, JointRuntime.generate inventory (ScopeRevision.emit inventory), rfl, ScopeRevision.legacy ready, rfl,
    ScopeRevision.the_new_source_initial_is_the_actual_old_successor ready,
    fun index => OutstandingSource.History.NativeService.historyAt (ScopeRevision.epochSource ready) inputs index (inputs.length + 1),
    fun _ => rfl,
    fun index => OutstandingSource.History.NativeService.historyAt (ScopeRevision.epochSource ready)
      (ScopeRevision.Pending.nextInputs ready inputs) index (inputs.length + 2), fun _ => rfl,
    Mandate.Challenge.Cross.grantContinuations (ScopeRevision.epochBound ready) inputs (ScopeRevision.Pending.emit ready inputs), rfl,
    ScopeRevision.Pending.allResidents ready inputs, rfl,
    ScopeRevision.Pending.original_native_finance_supports_the_actual_response_matrix ready inputs,
    ScopeRevision.Pending.outcome ready inputs, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (ScopeRevision.Pending.sourceInput ready inputs)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => current = (ProgrammeHistory.visitAt (ScopeRevision.Pending.sourceInput ready inputs) (inputs.length + 2)).current → Disposition ready inputs
  project := fun _ {_} _ _ _own => generate ready inputs

def root := (ProgrammeLiving.livingRoot (ScopeRevision.Pending.sourceInput ready inputs)).withProjectionCoface (projectionLaw ready inputs)

theorem root_is_its_own_emitting_source : (root ready inputs).toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot (ScopeRevision.Pending.sourceInput ready inputs)).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (ScopeRevision.Pending.sourceInput ready inputs)) :=
  ⟨ProgrammeSource.V (ScopeRevision.Pending.sourceInput ready inputs), root ready inputs, ProgrammeHistory.temporalVisit (ScopeRevision.Pending.sourceInput ready inputs) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (ScopeRevision.Pending.sourceInput ready inputs)) where
  State := Nat
  stateAt := stateAt ready inputs
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (ScopeRevision.Pending.sourceInput ready inputs)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (ScopeRevision.Pending.sourceInput ready inputs) first).current =
        (ProgrammeHistory.visitAt (ScopeRevision.Pending.sourceInput ready inputs) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (ScopeRevision.Pending.sourceInput ready inputs) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | responsibilities

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (ScopeRevision.Pending.sourceInput ready inputs)) where
  process := process ready inputs
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (ScopeRevision.Pending.sourceInput ready inputs)
    | .responsibilities => projectionLaw ready inputs
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (ScopeRevision.Pending.sourceInput ready inputs)).toAuthoritativeRoot.source (projectionLaw ready inputs)
    | responsibilities =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (ScopeRevision.Pending.sourceInput ready inputs)).toAuthoritativeRoot.source (projectionLaw ready inputs)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .responsibilities => ()

def activated (ordinal : Nat) : LivingRuntimeState (process ready inputs) :=
  (facade ready inputs).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopePendingRuntime
