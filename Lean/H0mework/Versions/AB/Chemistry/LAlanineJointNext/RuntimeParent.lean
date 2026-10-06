import H0mework.Versions.AB.Chemistry.LAlanineHeldForce.RuntimeHeldForceRuntimeRegression

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root HeldForce.Runtime Propagation.Interface
noncomputable section

def jointParentRuntime : LivingRuntimeState heldForceRuntimeProcess := heldForceRuntimeAfterFirst
def jointParentVisit : SourceNativeTemporalVisitAt heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  jointParentRuntime.current.visit
def jointParentGenerated :=
  heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit jointParentVisit
def jointParentEvent :
    ExactTemporalCausalRootEventAt heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot jointParentVisit :=
  heldForceLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt jointParentVisit
def jointParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? heldForceLivingRoot
    heldForceInitialEntry jointParentRuntime.state.history).get (by rfl)
def jointParentEntry := jointParentGeneratedAuthority.1
def jointParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt heldForceLivingRoot
    jointParentVisit jointParentEntry := jointParentGeneratedAuthority.2
def jointParentEntryRow : jointParentGenerated.GeneratedEntryRowAt jointParentEntry :=
  (jointParentGenerated.canonicalGeneratedEntryRow? jointParentEntry).get (by rfl)

def jointParentResult : HeldForceResult :=
  match heldForceRuntimeFacade.readoutAt jointParentRuntime .readiness with
  | .inl ⟨_, result, _⟩ => result
  | .inr impossible => nomatch impossible

def jointParentPhysical :
    Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger :=
  match heldForceRuntimeFacade.readoutAt jointParentRuntime .physical with
  | .inl ⟨_, physical⟩ => physical
  | .inr impossible => nomatch impossible

def jointParentHeld : Matrix Basis Basis ℂ :=
  match heldForceRuntimeFacade.readoutAt jointParentRuntime .held with
  | .inl ⟨_, current, _⟩ => current
  | .inr impossible => nomatch impossible

def jointParentRealization : Matrix Basis Basis ℂ × Matrix Basis Basis ℂ :=
  match heldForceRuntimeFacade.readoutAt jointParentRuntime .realization with
  | .inl ⟨_, realization⟩ => realization
  | .inr impossible => nomatch impossible

def jointParentTime : ℚ :=
  match heldForceRuntimeFacade.readoutAt jointParentRuntime .clock with
  | .inl ⟨_, current, _⟩ => current
  | .inr impossible => nomatch impossible

def jointParentHistory := jointParentPhysical.1
def jointParentFrame := jointParentPhysical.2.1
def jointParentEnergyLedger := jointParentPhysical.2.2
def jointParentMasses := jointParentHistory.masses

theorem jointParentEntry_exact : jointParentEntry = entryAt heldForceSupport := entryAt_unique _
theorem jointParent_generatedVisit : jointParentVisit = generatedHeldForceAction.target.targetVisit := rfl

theorem jointParent_actualInputs :
    jointParentResult = heldForceSourceResult ∧ jointParentHeld = HeldForce.Producer.exactHeld ∧
    jointParentRealization = (HeldForce.Source.realizedHeld, HeldForce.Producer.realizationResidual) ∧
    jointParentFrame = heldForceRefreshedFrame ∧ jointParentEnergyLedger = HeldForce.Source.energyLedger ∧
    jointParentMasses = Inertia.Source.stepReadout.masses := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem jointParent_installedFaces :
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .held) ∧
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .physical) ∧
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .realization) ∧
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .gradient) ∧
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .clock) ∧
    type_of% (heldForceRuntimeFace_factorizes jointParentRuntime .readiness) :=
  ⟨heldForceRuntimeFace_factorizes jointParentRuntime .held,
    heldForceRuntimeFace_factorizes jointParentRuntime .physical,
    heldForceRuntimeFace_factorizes jointParentRuntime .realization,
    heldForceRuntimeFace_factorizes jointParentRuntime .gradient,
    heldForceRuntimeFace_factorizes jointParentRuntime .clock,
    heldForceRuntimeFace_factorizes jointParentRuntime .readiness⟩

def jointParentFirstForceReceipt : HeldForceActionReceiptAt heldForceParentEvent jointParentResult :=
  generatedHeldForceAction_receipt

theorem jointParent_firstForce_trace :
    type_of% heldForceRuntime_sourceCertificate ∧ jointParentResult = generatedHeldForceAction.answer ∧
    type_of% generatedHeldForceAction_next :=
  ⟨heldForceRuntime_sourceCertificate, rfl, generatedHeldForceAction_next⟩

theorem jointParent_clock : jointParentTime = Propagation.Producer.nativeClockStep :=
  heldForceRuntime_clock jointParentRuntime

theorem jointParent_row_identity :
    jointParentEntry.1 = .bondDensityIncidenceAdjudication ∧
    jointParentEntry.claim = .registeredExperimentalGeometryModelBondTopology ∧
    jointParentEntry.progressBudget = 0 ∧ N.lineageAt heldForceSupport = LAlanine40K2025.Source.key :=
  ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.JointNext.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
