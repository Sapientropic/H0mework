import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime.Facade

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open BasinRefinement.WholeBandBasin.Family.All
open Propagation.Interface
open UnifiedOrbitals.Frame
noncomputable section

theorem actual_material : readMaterial afterFirst first_ready=materialOf Spatial.current := by
  rw [(material_read afterFirst first_ready).2,Spatial.current_generated]
  rfl

theorem original_spatial_faces (runtime : LivingRuntimeState process)
    (ready : Ready runtime.state.current) (face : PreciseAtomicIQA.Runtime.Face) :
    type_of% (face_factorizes runtime (.component (.inherited face))) ∧
    ∃ active, facade.readoutAt runtime (.component (.inherited face))=
      .inl ⟨active,(originalFace face,⟨original_face_factorizes face⟩)⟩ := by
  have active : Ready runtime.current.visit.current := ready
  refine ⟨face_factorizes runtime _,⟨⟨active⟩,?_⟩⟩
  simp only [SourceNativeLivingRuntimeFacade.readoutAt,facade,
    SourceNativeProjectionLaw.outcomeAt,projectionLaw,dif_pos active]

theorem wholeLedger_same_occurrence (runtime : LivingRuntimeState process) :
    runtime.tick.generated.wholeLedgerWriteBack=
      ReceiverBody.Runtime.authoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem original_joint_visit :
    afterFirst.current.visit=ReceiverBody.Runtime.generatedAction.target.targetVisit := rfl

theorem actual_static :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    StaticClosure (readMaterial afterFirst first_ready).body :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.static⟩

theorem actual_iqa_original_ao :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    iqaTotal (readMaterial afterFirst first_ready).original :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.total⟩

theorem actual_iqa_current_coordinates :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    jointTotal (readMaterial afterFirst first_ready) :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.jointTotal⟩

theorem actual_iqa_independent :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    iqaIndependent (readMaterial afterFirst first_ready).original :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.independent⟩

theorem actual_gamma :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    complexFrame*registeredState (readMaterial afterFirst first_ready).body.realized*star complexFrame=
      registeredAOState (readMaterial afterFirst first_ready).body.realized :=
  ⟨actual_static.1,actual_static.2.complexFrame⟩

theorem actual_clocks :
    type_of% (face_factorizes afterFirst (.component (.component .material))) ∧
    (readMaterial afterFirst first_ready).body.resource.quantum.localClock=19*Propagation.Producer.nativeClockStep ∧
    (readMaterial afterFirst first_ready).body.bodyClock=4*Propagation.Producer.nativeClockStep := by
  refine ⟨(material_read afterFirst first_ready).1,?_⟩
  rw [actual_material,Spatial.current_generated]
  exact ⟨ReceiverBody.Runtime.source_output_resource_clock,ReceiverBody.Runtime.source_output_body_clock⟩

theorem actual_resource_energy :
    type_of% (face_factorizes afterFirst (.component (.component .material))) ∧
    Thermal.Collision.energy Thermal.Recovery.Reservoir.Pointer.baselineHamiltonian
      (readMaterial afterFirst first_ready).body.resource.quantum.joint+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic
        (readMaterial afterFirst first_ready).body.resource.momentum+
      ((readMaterial afterFirst first_ready).body.frame.total : ℝ)=
    Thermal.Recovery.Reservoir.Pointer.Live.baselineEnergy resourceBefore.quantum+
      Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Extract.Port.kinetic receiverInitial+
      (Reentry.Producer.targetMomentumKinetic : ℝ)+sourcePotential := by
  refine ⟨(material_read afterFirst first_ready).1,?_⟩
  rw [actual_material]
  exact ReceiverBody.Runtime.actual_resource_energy.2

theorem full_joint_account_retained :
    type_of% (all_joint_faces afterFirst .history) ∧
    type_of% (all_joint_faces afterFirst .energy) ∧
    ReceiverBody.Runtime.InstalledJointActuation :=
  ⟨all_joint_faces afterFirst .history,all_joint_faces afterFirst .energy,
    ReceiverBody.Runtime.sourceGeneratedJointActuation⟩

theorem historical_physical_clock :
    type_of% (face_factorizes afterFirst (.component (.component .certificate))) ∧
    type_of% (PreciseAtomicIQA.Runtime.clock_preserved PreciseAtomicIQA.Runtime.afterFirst) :=
  ⟨(certificate_read afterFirst first_ready).1,(certificate_read afterFirst first_ready).2.oldClock⟩

theorem original_body_not_relabelled :
    (readMaterial afterFirst first_ready).body.frame.momentum ≠
      ReceiverBody.Runtime.sourceInput.frame.momentum := by
  rw [actual_material,Spatial.current_generated]
  exact ReceiverBody.Runtime.source_output_changes_body

theorem seed_spatial_inactive (face : Projection) :
    ∃ inactive, facade.readoutAt seed (.component face)=.inr inactive := by
  have no : ¬Ready seed.current.visit.current := False.elim
  refine ⟨⟨no⟩,?_⟩
  simp only [SourceNativeLivingRuntimeFacade.readoutAt,facade,
    SourceNativeProjectionLaw.outcomeAt,projectionLaw,dif_neg no]

structure InstalledJointSpatial : Prop where
  sourceLaw : type_of% source_and_law_unchanged
  compiler : type_of% rootCompiler_unchanged
  occurrence : type_of% seed_same_occurrence
  generatedNext : type_of% generated_same_next
  jointVisit : type_of% original_joint_visit
  material : type_of% actual_material
  static : type_of% actual_static
  total : type_of% actual_iqa_original_ao
  currentCoordinates : type_of% actual_iqa_current_coordinates
  independent : type_of% actual_iqa_independent
  gamma : type_of% actual_gamma
  clocks : type_of% actual_clocks
  energy : type_of% actual_resource_energy
  fullAccount : type_of% full_joint_account_retained
  historicalClock : type_of% historical_physical_clock
  distinctBody : type_of% original_body_not_relabelled
  whole : type_of% wholeLedger_same_occurrence
  jointFaces : type_of% all_joint_faces
  spatialFaces : type_of% original_spatial_faces
  admission : type_of% seed_spatial_inactive
  allFaces : Nonempty (Face ≃ Fin 269)

theorem sourceGeneratedJointSpatial : InstalledJointSpatial :=
  ⟨source_and_law_unchanged,rootCompiler_unchanged,seed_same_occurrence,generated_same_next,
    original_joint_visit,actual_material,actual_static,actual_iqa_original_ao,actual_iqa_current_coordinates,actual_iqa_independent,
    actual_gamma,actual_clocks,actual_resource_energy,full_joint_account_retained,historical_physical_clock,original_body_not_relabelled,
    wholeLedger_same_occurrence,all_joint_faces,original_spatial_faces,seed_spatial_inactive,⟨faceEquiv⟩⟩

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.Spatial.Runtime
