import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open BasinRefinement.WholeBandBasin.Family.All
noncomputable section

theorem actual_material : readMaterial afterFirst first_ready=materialOf ReceiverBody.Runtime.sourceOutput := by
  rw [(material_read afterFirst first_ready).2]
  rfl

theorem actual_parent_material : (readMaterial afterFirst first_ready).joint=parentMaterial := by
  rw [actual_material]
  exact parent_generated.symm

theorem actual_coulomb_account : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    CoulombAccount (readMaterial afterFirst first_ready) :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.account⟩

theorem actual_original_hartree : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    d3Energy (readMaterial afterFirst first_ready).weight=
      UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.d3HartreeEnergy :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.hartree⟩

theorem actual_report_residual : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    (readMaterial afterFirst first_ready).weight.reportPotentialResidual=sourceMaterial.reportPotentialResidual :=
  ⟨(certificate_read afterFirst first_ready).1,
    congrArg (fun weight => weight.reportPotentialResidual) (certificate_read afterFirst first_ready).2.weight⟩

theorem actual_original_ledger : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    (readMaterial afterFirst first_ready).ledger=originalLedger :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.ledger⟩

theorem actual_spatial_closure : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    Spatial.Closure (readMaterial afterFirst first_ready).joint :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.joint⟩

theorem actual_shared_history (face : PreciseAtomicIQA.Runtime.Face) :
    type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    type_of% (historical_shared_face face) :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.sharedFaces face⟩

theorem actual_body_potential : type_of% (face_factorizes afterFirst (.component .certificate)) ∧
    (readMaterial afterFirst first_ready).joint.body.frame.potential=
      Reentry.Source.stepReadout.nuclear.target.potential :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.potential⟩

theorem actual_clocks : type_of% (face_factorizes afterFirst (.component .material)) ∧
    (readMaterial afterFirst first_ready).joint.body.resource.quantum.localClock=19*Propagation.Producer.nativeClockStep ∧
    (readMaterial afterFirst first_ready).joint.body.bodyClock=4*Propagation.Producer.nativeClockStep := by
  refine ⟨(material_read afterFirst first_ready).1,?_⟩
  rw [actual_parent_material]
  exact Spatial.Runtime.actual_clocks.2

theorem actual_resource_energy : type_of% (face_factorizes afterFirst (.component .material)) ∧
    Thermal.Collision.energy Thermal.Recovery.Reservoir.Pointer.baselineHamiltonian
      (readMaterial afterFirst first_ready).joint.body.resource.quantum.joint+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic
        (readMaterial afterFirst first_ready).joint.body.resource.momentum+
      ((readMaterial afterFirst first_ready).joint.body.frame.total : ℝ)=
    Thermal.Recovery.Reservoir.Pointer.Live.baselineEnergy resourceBefore.quantum+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic receiverInitial+
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  refine ⟨(material_read afterFirst first_ready).1,?_⟩
  rw [actual_parent_material]
  exact Spatial.Runtime.actual_resource_energy.2

theorem wholeLedger_same_occurrence (runtime : LivingRuntimeState process) :
    runtime.tick.generated.wholeLedgerWriteBack=
      Spatial.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem parent_joint_visit : afterFirst.current.visit=Spatial.Runtime.afterFirst.current.visit := rfl

theorem original_joint_visit : afterFirst.current.visit=ReceiverBody.Runtime.generatedAction.target.targetVisit :=
  parent_joint_visit.trans Spatial.Runtime.original_joint_visit

theorem seed_coulomb_inactive (face : Projection) :
    ∃ inactive, facade.readoutAt seed (.component face)=.inr inactive := by
  have no : ¬Ready seed.current.visit.current := False.elim
  refine ⟨⟨no⟩,?_⟩
  simp only [SourceNativeLivingRuntimeFacade.readoutAt,facade,
    SourceNativeProjectionLaw.outcomeAt,projectionLaw,dif_neg no]

structure InstalledJointCoulomb : Prop where
  material : type_of% actual_material
  parent : type_of% actual_parent_material
  account : type_of% actual_coulomb_account
  hartree : type_of% actual_original_hartree
  reportResidual : type_of% actual_report_residual
  originalLedger : type_of% actual_original_ledger
  spatial : type_of% actual_spatial_closure
  history : type_of% actual_shared_history
  potential : type_of% actual_body_potential
  clocks : type_of% actual_clocks
  energy : type_of% actual_resource_energy
  sourceLaw : type_of% source_and_law_unchanged
  compiler : type_of% rootCompiler_unchanged
  wholeLedger : type_of% wholeLedger_same_occurrence
  inherited : type_of% all_parent_faces
  occurrence : type_of% seed_same_occurrence
  parentVisit : type_of% parent_joint_visit
  jointVisit : type_of% original_joint_visit
  next : type_of% generated_same_next
  admission : type_of% seed_coulomb_inactive
  allFaces : Nonempty (Face ≃ Fin 271)

theorem sourceGeneratedJointCoulomb : InstalledJointCoulomb :=
  ⟨actual_material,actual_parent_material,actual_coulomb_account,actual_original_hartree,
    actual_report_residual,actual_original_ledger,actual_spatial_closure,actual_shared_history,
    actual_body_potential,actual_clocks,actual_resource_energy,source_and_law_unchanged,
    rootCompiler_unchanged,wholeLedger_same_occurrence,all_parent_faces,seed_same_occurrence,
    parent_joint_visit,original_joint_visit,generated_same_next,seed_coulomb_inactive,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Coulomb.Runtime
