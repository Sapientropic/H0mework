import H0mework.Chemistry.LAlanineWholeBandCell0.RuntimeParentConsumers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource WholeBandReplay
open WholeBandActual WholeBandCell0Continuation ContinuousGradient Matrix Set
open scoped Matrix
noncomputable section

theorem wholeBandCell0Runtime_actual_flow :
    type_of% (wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate)) ∧
    (∀ d i role x,
      InRectangle (generatedWholeBandCell0Material.parent.parent.callBoxes (callAt 0 d i role)) x →
      FieldHolds (generatedWholeBandCell0Material.parent.parent.callReports (callAt 0 d i role)) x) ∧
    (∀ p, generatedWholeBandCell0Material.fullFlows p 0 =
      generatedWholeBandCell0Material.parent.parent.cellSeeds 0 p.val) ∧
    (∀ p, IsIntegralCurveOn (generatedWholeBandCell0Material.fullFlows p)
      (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2))) ∧
    (∀ p t, t ∈ Icc (-(1/2 : ℝ)) (1/2) →
      generatedWholeBandCell0Material.fullFlows p t ∈ sourceCube) ∧
    type_of% cell0_full_tubes ∧ type_of% cell0_full_fields ∧ type_of% cell0_full_field_cover :=
  ⟨wholeBandCell0Runtime_sourceCertificate.1, wholeBandCell0Runtime_sourceCertificate.2.fields64,
    wholeBandCell0Runtime_sourceCertificate.2.starts, wholeBandCell0Runtime_sourceCertificate.2.original,
    wholeBandCell0Runtime_sourceCertificate.2.residence, wholeBandCell0Runtime_sourceCertificate.2.tubes,
    wholeBandCell0Runtime_sourceCertificate.2.fieldsAlong, wholeBandCell0Runtime_sourceCertificate.2.coverage⟩

theorem wholeBandCell0Runtime_actual_targets :
    type_of% (wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate)) ∧
    (∀ p d i, InRectangle (generatedWholeBandCell0Material.parent.parent.endpointBoxes 0 d i)
      (generatedWholeBandCell0Material.fullFlows p (elapsedStop 0 d i))) ∧
    (∀ p d (i : Fin 15), InRectangle (generatedWholeBandCell0Material.parent.parent.initialBoxes 0 d i.succ)
      (generatedWholeBandCell0Material.fullFlows p (elapsedStop 0 d i.castSucc))) ∧
    (∀ p, InRectangle (generatedWholeBandCell0Material.parent.parent.endpointBoxes 0 0 15)
        (generatedWholeBandCell0Material.fullFlows p (-(1/2 : ℝ))) ∧
      InRectangle (generatedWholeBandCell0Material.parent.parent.endpointBoxes 0 1 15)
        (generatedWholeBandCell0Material.fullFlows p (1/2 : ℝ))) ∧
    (∀ p, EqOn (generatedWholeBandCell0Material.parent.fullFirstFlows p)
      (generatedWholeBandCell0Material.fullFlows p) firstWindow) :=
  ⟨wholeBandCell0Runtime_sourceCertificate.1, wholeBandCell0Runtime_sourceCertificate.2.endpoints,
    wholeBandCell0Runtime_sourceCertificate.2.nextInitial, wholeBandCell0Runtime_sourceCertificate.2.caps,
    wholeBandCell0Runtime_sourceCertificate.2.firstRestriction⟩

/- The all-cell statement is a same-time classification of the original clamped kernel. -/
theorem wholeBandCell0Runtime_source_kernel :
    type_of% (wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate)) ∧
    type_of% TrueFlowGeometry.rawFlow_meeting_nonneg ∧ type_of% TrueFlowGeometry.rawFlow_meeting_nonpos ∧
    (∀ t : Time, Function.Injective (fun p => generatedWholeBandCell0Material.parent.originalFlowKernel p t)) ∧
    type_of% WholeBandGeometry.cell_seed_plane_zero ∧ type_of% WholeBandGeometry.source_timeSlice_classification :=
  ⟨wholeBandCell0Runtime_sourceCertificate.1, wholeBandCell0Runtime_sourceCertificate.2.sourceMeetingNonneg,
    wholeBandCell0Runtime_sourceCertificate.2.sourceMeetingNonpos, wholeBandCell0Runtime_sourceCertificate.2.timeSliceInjective,
    wholeBandCell0Runtime_sourceCertificate.2.seedPlane, wholeBandCell0Runtime_sourceCertificate.2.seedTimeSlice⟩

theorem wholeBandCell0Runtime_nofold :
    type_of% (wholeBandCell0RuntimeFace_factorizes wholeBandCell0RuntimeSeed (.component .certificate)) ∧
    (∀ d i, 1/20 < generatedWholeBandCell0Material.normalLower (callAt 0 d i .initial) ∧
      1/20 < generatedWholeBandCell0Material.normalLower (callAt 0 d i .tube)) ∧
    (∀ p t, t ∈ Icc (-(1/2 : ℝ)) (1/2) → (1/20 : ℝ) <
      generatedWholeBandCell0Material.normal ⬝ᵥ sourceGradient (generatedWholeBandCell0Material.fullFlows p t)) ∧
    (∀ p, StrictMonoOn (fun t => generatedWholeBandCell0Material.plane (generatedWholeBandCell0Material.fullFlows p t))
      (Icc (-(1/2 : ℝ)) (1/2))) ∧
    type_of% WholeBandCell0Geometry.cell0_parameter_meeting_classification ∧
    Function.Injective (fun p : Cell0Point => generatedWholeBandCell0Material.parameterMap p.val) ∧
    InjOn generatedWholeBandCell0Material.parameterMap (generatedWholeBandCell0Material.parent.parent.cellDomains 0) :=
  ⟨wholeBandCell0Runtime_sourceCertificate.1, wholeBandCell0Runtime_sourceCertificate.2.normalBounds,
    wholeBandCell0Runtime_sourceCertificate.2.actualTransverse, wholeBandCell0Runtime_sourceCertificate.2.planeMonotone,
    wholeBandCell0Runtime_sourceCertificate.2.meetingClassification, wholeBandCell0Runtime_sourceCertificate.2.parameterInjective,
    wholeBandCell0Runtime_sourceCertificate.2.parameterInjOn⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
