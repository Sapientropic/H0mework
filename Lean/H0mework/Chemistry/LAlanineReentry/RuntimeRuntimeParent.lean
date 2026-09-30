import H0mework.Chemistry.LAlanineReentry.RuntimeParent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root JointNext.Runtime
noncomputable section

def reentryParentVisit : SourceNativeTemporalVisitAt jointLivingRoot.toAuthoritativeRoot.toLedgerRoot :=
  reentryParentRuntime.current.visit
def reentryParentGenerated := jointLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit reentryParentVisit
def reentryParentEvent : ExactTemporalCausalRootEventAt jointLivingRoot.toAuthoritativeRoot.toLedgerRoot reentryParentVisit :=
  jointLivingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt reentryParentVisit
def reentryParentGeneratedAuthority :=
  (SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitial? jointLivingRoot
    jointInitialEntry reentryParentRuntime.state.history).get (by rfl)
def reentryParentEntry := reentryParentGeneratedAuthority.1
def reentryParentAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt jointLivingRoot
    reentryParentVisit reentryParentEntry := reentryParentGeneratedAuthority.2
def reentryParentEntryRow : reentryParentGenerated.GeneratedEntryRowAt reentryParentEntry :=
  (reentryParentGenerated.canonicalGeneratedEntryRow? reentryParentEntry).get (by rfl)

def reentryParentPacket := reentryParentPhysical.1
def reentryParentHistory : Inertia.Interface.InertialStepReadout × HeldForce.Runtime.HeldForceResult :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .history with
  | .inl ⟨_, history⟩ => history
  | .inr impossible => nomatch impossible

theorem reentryParentEntry_exact : reentryParentEntry = entryAt jointSupport := entryAt_unique _
theorem reentryParent_generatedVisit : reentryParentVisit = generatedJointAction.target.targetVisit := rfl
theorem reentryParent_packet : reentryParentPacket = JointNext.Source.stepReadout.nuclear := rfl
theorem reentryParent_history : reentryParentHistory = (jointParentHistory, jointParentResult) := rfl

theorem reentryParent_historicalFaces :
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .history) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .gradient) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .wholeLedger) :=
  ⟨jointRuntimeFace_factorizes reentryParentRuntime .history,
    jointRuntimeFace_factorizes reentryParentRuntime .gradient,
    jointRuntimeFace_factorizes reentryParentRuntime .wholeLedger⟩

def reentryParentFirstJointReceipt : JointActionReceiptAt jointParentEvent reentryParentResult :=
  generatedJointAction_receipt

theorem reentryParent_firstJoint_trace :
    type_of% jointRuntime_sourceCertificate ∧ reentryParentResult = generatedJointAction.answer ∧
    type_of% generatedJointAction_next := ⟨jointRuntime_sourceCertificate, rfl, generatedJointAction_next⟩

theorem reentryParent_row_identity :
    reentryParentEntry.1 = .bondDensityIncidenceAdjudication ∧
    reentryParentEntry.claim = .registeredExperimentalGeometryModelBondTopology ∧
    reentryParentEntry.progressBudget = 0 ∧ N.lineageAt jointSupport = LAlanine40K2025.Source.key :=
  ⟨rfl, rfl, rfl, rfl⟩

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
