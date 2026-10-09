import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Flux.Runtime.ParentConsumers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource MeasureTheory
open _root_.LAlanineTrueFlowDifferential
noncomputable section

theorem actual_transport (runtime : LivingRuntimeState process) (t : ℝ) (x : Point) :
    (readMaterial runtime).calculation.transport t x =
      (readMaterial runtime).parent.calculation.flow x t := (certificate_read runtime).2.original_transport t x

theorem actual_initial_derivative (runtime : LivingRuntimeState process) (x : Point) (t : Time) :
    HasStrictFDerivAt (fun y => (readMaterial runtime).parent.calculation.flow y
      ((readMaterial runtime).calculation.spatialStep*(t : ℝ))) ((readMaterial runtime).calculation.jacobian x t) x :=
  (certificate_read runtime).2.initial_derivative x t

theorem actual_jacobian_positive (runtime : LivingRuntimeState process) (x : Point) (t : Time) :
    0 < ((readMaterial runtime).calculation.jacobian x t).det := (certificate_read runtime).2.positive_jacobian x t

theorem actual_zero_flux (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime (.component .material)) ∧
    type_of% (face_factorizes runtime (.component .certificate)) ∧
    (readMaterial runtime).calculation.laplacianIntegral = 0 ∧
    (∫ x in (readMaterial runtime).parent.calculation.basin, laplacian sourceTerms densityMatrix x) = 0 :=
  ⟨face_factorizes runtime (.component .material),face_factorizes runtime (.component .certificate),
    (certificate_read runtime).2.actual_zero_flux,(certificate_read runtime).2.actual_zero_flux⟩

theorem actual_weak_flux (runtime : LivingRuntimeState process) (test : Weak.Test) :
    (∫ x in (readMaterial runtime).parent.calculation.basin, laplacian sourceTerms densityMatrix x*test.value x+
      test.derivative x (sourceGradient x)) = 0 := (certificate_read runtime).2.actual_weak_divergence test

structure PhysicalZeroFluxClosure : Prop where
  source : FluxClosure
  parent : type_of% complete_parent_preserved
  transport : type_of% actual_transport
  derivative : type_of% actual_initial_derivative
  positive : type_of% actual_jacobian_positive
  zero_flux : type_of% actual_zero_flux
  weak_flux : type_of% actual_weak_flux
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit

theorem sourceGeneratedPhysicalZeroFluxNext : PhysicalZeroFluxClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_transport,actual_initial_derivative,
    actual_jacobian_positive,actual_zero_flux,actual_weak_flux,read_commutes_with_physicalOccurrence,
    wholeLedger_same_occurrence,row_identity,clock_preserved,all_original_faces,face_factorizes,generated_same_next,rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Flux.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
