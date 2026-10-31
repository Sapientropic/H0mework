import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Effects
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup
variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)
noncomputable section

structure EpochDisposition where
  private mk ::
  oldJoint : JointRuntime.Disposition inventory (emit inventory)
  oldJoint_exact : oldJoint = JointRuntime.generate inventory (emit inventory)
  oldNative : Runtime.Disposition fuel (advance inventory).inputs inventory.cut.depth
  oldNative_exact : oldNative = legacy ready
  initial_exact : (epochInput ready).initial = (advance inventory).cut.past.frame.raw
  services : (index : (epochSource ready).Slot) →
    OutstandingSource.History.NativeService.Prefix (epochSource ready) (epochInputs ready) index 2
  services_exact : ∀ index, services index = epochServices ready index
  mandates : List (TracedGrant ready)
  mandates_exact : mandates = grantRecords ready
  objections : List (Sigma fun claim : Mandate.Challenge.Claim (Mandate.Challenge.fromHistory (epochBound ready)) (epochInputs ready) =>
    Mandate.Challenge.History (Mandate.Challenge.fromHistory (epochBound ready)) (epochInputs ready) claim)
  objections_exact : objections = Mandate.Challenge.recordsAt (Mandate.Challenge.fromHistory (epochBound ready)) (epochInputs ready) 3
  execution : EpochOutcome ready
  execution_exact : execution = epochOutcome ready
  financial_support : Financial.BalanceConservation.ledgerClaims (I fuel (advance inventory).inputs)
    oldNative.account.current = (epochCurrent ready 3).claims

def generateEpoch : EpochDisposition ready :=
  ⟨JointRuntime.generate inventory (emit inventory), rfl, legacy ready, rfl,
    the_new_source_initial_is_the_actual_old_successor ready,
    epochServices ready, fun _ => rfl, grantRecords ready, rfl,
    Mandate.Challenge.recordsAt (Mandate.Challenge.fromHistory (epochBound ready)) (epochInputs ready) 3, rfl, epochOutcome ready, rfl,
    original_financial_sources_support_the_new_actual_matrix ready⟩

inductive Handoff (inventory : Joint.Inventory fuel) where
  | private revised (ready : Ready inventory) (generated : choose inventory = some ready)
      (epoch : EpochDisposition ready) (exact : epoch = generateEpoch ready)
  | private blocked (absent : choose inventory = none) (reason : Blocked inventory)

def generateHandoff (inventory : Joint.Inventory fuel) : Handoff inventory :=
  match generated : choose inventory with
  | some ready => .revised ready generated (generateEpoch ready) rfl
  | none => .blocked generated (every_refused_scope_handoff_has_an_actual_reason inventory generated)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevisionRuntime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

open Objection.Followup Objection.Opening

variable {fuel : ℚ} (inventory : Joint.Inventory fuel)

noncomputable section

abbrev I := JointRuntime.I inventory (ScopeRevision.emit inventory)
abbrev previousRoot := JointRuntime.root inventory (ScopeRevision.emit inventory)
abbrev previousFacade := JointRuntime.facade inventory (ScopeRevision.emit inventory)

structure Disposition where
  private mk ::
  inherited : JointRuntime.Disposition inventory (ScopeRevision.emit inventory)
  inherited_exact : inherited = JointRuntime.generate inventory (ScopeRevision.emit inventory)
  handoff : ScopeRevision.Handoff inventory
  handoff_exact : handoff = ScopeRevision.generateHandoff inventory

def generate : Disposition inventory :=
  ⟨JointRuntime.generate inventory (ScopeRevision.emit inventory), rfl,
    ScopeRevision.generateHandoff inventory, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (I inventory)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt (I inventory) (inventory.cut.depth + 2)).current → Disposition inventory
  project := fun _ {_} _ _ _own => generate inventory

def root := (previousRoot inventory).withProjectionCoface (projectionLaw inventory)

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory)) :=
  ⟨ProgrammeSource.V (I inventory), root inventory, ProgrammeHistory.temporalVisit (I inventory) ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (I inventory)) where
  State := Nat
  stateAt := stateAt inventory
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (I inventory)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (I inventory) first).current =
        (ProgrammeHistory.visitAt (I inventory) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (I inventory) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : JointRuntime.Face)
  | revision

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (I inventory)) where
  process := process inventory
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).componentAt (previousFacade inventory).seed previous
    | .revision => projectionLaw inventory
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact ((previousFacade inventory).installationAt (previousFacade inventory).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory))
    | revision =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (previousRoot inventory).toAuthoritativeRoot.source (projectionLaw inventory)
  projectionAt := fun _ face => match face with
    | .previous previous => (previousFacade inventory).projectionAt (previousFacade inventory).seed previous
    | .revision => ()

def activated (ordinal : Nat) : LivingRuntimeState (process inventory) :=
  (facade inventory).seed.advance ordinal

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevisionRuntime
