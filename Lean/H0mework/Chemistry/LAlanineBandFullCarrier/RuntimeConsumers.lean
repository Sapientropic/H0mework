import H0mework.Chemistry.LAlanineBandFullCarrier.RuntimeParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceFiniteData SourceSignedEvaluator WholeBandSource WholeBandGenerated
open WholeBandAtlas IntervalParameterMap Set MeasureTheory
noncomputable section

theorem actual_calculations (runtime : LivingRuntimeState process) (t : HighJet.Tile) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    TileEvaluationSound t ((readMaterial runtime).calculation.evaluations t) :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.material_evaluations_sound t⟩

theorem actual_fields (runtime : LivingRuntimeState process) (f : FullBandCall) (x : Point)
    (inside : InRectangle ((readMaterial runtime).calculation.boxes f) x) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    FieldHolds ((readMaterial runtime).calculation.reported f) x :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.material_actual_fields f x inside⟩

theorem actual_carrier (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    (readMaterial runtime).calculation.parameterMap '' (readMaterial runtime).calculation.parameterCarrier =
      (readMaterial runtime).calculation.physicalCarrier ∧
    ContinuousOn (readMaterial runtime).calculation.parameterMap (readMaterial runtime).calculation.parameterCarrier ∧
    InjOn (readMaterial runtime).calculation.parameterMap (readMaterial runtime).calculation.parameterCarrier ∧
    0 < volume (readMaterial runtime).calculation.physicalCarrier ∧
    volume (readMaterial runtime).calculation.physicalCarrier < ⊤ :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.same_physical_carrier,(certificate_read runtime).2.whole_carrier_continuous,
    (certificate_read runtime).2.whole_carrier_no_fold,(certificate_read runtime).2.positive_finite_volume⟩

theorem actual_conservation (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    (∫ x in (readMaterial runtime).calculation.physicalCarrier,laplacian sourceTerms (readMaterial runtime).calculation.density x) =
      ∑ c : FullBandCell,∫ p in Faces.domain c 2,Faces.flux c (2,true) p + Faces.flux c (2,false) p :=
  ⟨face_factorizes runtime (.component .certificate),(certificate_read runtime).2.whole_spatial_conservation⟩

theorem actual_whole_space_flow (runtime : LivingRuntimeState process) (initial : Point) (t : ℝ) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    HasDerivAt ((readMaterial runtime).calculation.globalFlow initial)
      (ContinuousGradient.sourceGradient ((readMaterial runtime).calculation.globalFlow initial t)) t ∧
    (readMaterial runtime).calculation.globalFlow
      ((readMaterial runtime).calculation.globalFlow initial t) (-t) = initial :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.actual_global_flow initial t,
    (certificate_read runtime).2.actual_global_inverse initial t⟩

theorem actual_local_attractor (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    ContinuousGradient.sourceGradient (readMaterial runtime).calculation.criticalPoint = 0 ∧
    0 < volume (readMaterial runtime).calculation.attractingRegion ∧
    ∀ x ∈ (readMaterial runtime).calculation.attractingRegion,
      Filter.Tendsto ((readMaterial runtime).calculation.globalFlow x) Filter.atTop
        (nhds (readMaterial runtime).calculation.criticalPoint) :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.actual_critical_point,(certificate_read runtime).2.actual_attracting_volume,
    (certificate_read runtime).2.actual_attracting_limit⟩

structure PhysicalFullBandClosure : Prop where
  source : Source.FullBandClosure
  parent : type_of% complete_parent_preserved
  actualMaterial : type_of% actual_calculations
  fields : type_of% actual_fields
  carrier : type_of% actual_carrier
  conservation : type_of% actual_conservation
  globalFlow : type_of% actual_whole_space_flow
  attractor : type_of% actual_local_attractor
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit

theorem sourceGeneratedPhysicalFullBandNext : PhysicalFullBandClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_calculations,actual_fields,actual_carrier,
    actual_conservation,actual_whole_space_flow,actual_local_attractor,read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,row_identity,
    clock_preserved,all_original_faces,face_factorizes,generated_same_next,rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
