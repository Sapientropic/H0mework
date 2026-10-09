import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Runtime.ParentConsumers

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open BasinRefinement SourceFiniteData SourceGaussianModel MeasureTheory
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource UnifiedAction YangMills.FullPairing
open scoped Matrix ComplexOrder
noncomputable section

theorem actual_gamma (runtime : LivingRuntimeState process) :
    (readMaterial runtime).gamma = (readMaterial runtime).parent.calculation.registeredState :=
  (certificate_read runtime).2.source_gamma

theorem actual_projector (runtime : LivingRuntimeState process) :
    (readMaterial runtime).projector.PosSemidef ∧
    (readMaterial runtime).projector * (readMaterial runtime).projector =
      (readMaterial runtime).projector ∧
    (readMaterial runtime).projector.trace = ((readMaterial runtime).occupiedCount : ℂ) :=
  ⟨(certificate_read runtime).2.projector_positive,
    (certificate_read runtime).2.projector_idempotent,
    (certificate_read runtime).2.trace⟩

theorem actual_gamma_residual (runtime : LivingRuntimeState process) :
    (readMaterial runtime).gamma =
      (2 : ℂ) • (readMaterial runtime).projector + (readMaterial runtime).residual :=
  (certificate_read runtime).2.residual

theorem actual_U_wave (runtime : LivingRuntimeState process) (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ ((readMaterial runtime).wave i time x)
      ((readMaterial runtime).wave j time x)) = if i=j then 1 else 0 :=
  (certificate_read runtime).2.wave_orthonormal i j time

theorem actual_U_gamma_response (runtime : LivingRuntimeState process) (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ ((readMaterial runtime).wave i time x)
      (sourceWave ((readMaterial runtime).gamma *ᵥ Occupation.naturalCoefficient j) time x)) =
        Occupation.gamma_hermitian.eigenvalues j • (if i=j then (1 : ℂ) else 0) :=
  (certificate_read runtime).2.gamma_response i j time

theorem actual_U_projector_response (runtime : LivingRuntimeState process) (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ ((readMaterial runtime).wave i time x)
      (sourceWave ((readMaterial runtime).projector *ᵥ Occupation.naturalCoefficient j) time x)) =
        Occupation.mask j * (if i=j then (1 : ℂ) else 0) :=
  (certificate_read runtime).2.projector_response i j time

theorem actual_U_residual_response (runtime : LivingRuntimeState process) (i j : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ ((readMaterial runtime).wave i time x)
      (sourceWave ((readMaterial runtime).residual *ᵥ Occupation.naturalCoefficient j) time x)) =
        Occupation.gamma_hermitian.eigenvalues j • (if i=j then (1 : ℂ) else 0) -
          (2 : ℂ) * Occupation.mask j * (if i=j then (1 : ℂ) else 0) :=
  (certificate_read runtime).2.residual_response i j time

structure PhysicalOccupationClosure : Prop where
  source : Occupation.Closure
  parent : type_of% complete_parent_preserved
  gamma : type_of% actual_gamma
  projector : type_of% actual_projector
  residual : type_of% actual_gamma_residual
  wave : type_of% actual_U_wave
  gamma_response : type_of% actual_U_gamma_response
  projector_response : type_of% actual_U_projector_response
  residual_response : type_of% actual_U_residual_response
  physicalOccurrence : type_of% read_commutes_with_physicalOccurrence
  wholeLedger : type_of% wholeLedger_same_occurrence
  identity : type_of% row_identity
  clock : type_of% clock_preserved
  inherited : type_of% all_original_faces
  factorization : type_of% face_factorizes
  generatedNext : type_of% generated_same_next
  originalVisit : afterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit
  allFaces : Nonempty (Face ≃ Fin 76)

theorem sourceGeneratedPhysicalOccupationNext : PhysicalOccupationClosure :=
  ⟨(certificate_read afterFirst).2,complete_parent_preserved,actual_gamma,actual_projector,
    actual_gamma_residual,actual_U_wave,actual_U_gamma_response,actual_U_projector_response,
    actual_U_residual_response,read_commutes_with_physicalOccurrence,wholeLedger_same_occurrence,
    row_identity,clock_preserved,all_original_faces,face_factorizes,generated_same_next,rfl,⟨faceEquiv⟩⟩

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
