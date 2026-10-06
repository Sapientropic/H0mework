import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionSlice
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionIntegrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource Stage9DEF
open BasinRefinement SourceGaussianModel SourceFiniteData MeasureTheory
open YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

def preparedSection (preparation : Mother) (b : Basis) (scale : ℝ) (p : BasePoint) : Hilbert :=
  orbitalWeight b scale p • operator preparation (prepared p)

theorem full_preparation_pair (uTime : ℝ) (first second : Mother) (b c : Basis) (x : Point) :
    inner ℂ (preparedSection first b 1 (spatialSlice uTime x))
      (preparedSection second c 1 (spatialSlice uTime x)) =
      (UnifiedOrbitals.ao b x * UnifiedOrbitals.ao c x : ℝ) *
        inner ℂ (operator first (prepared (spatialSlice uTime 0)))
          (operator second (prepared (spatialSlice uTime 0))) := by
  simp [preparedSection,orbitalWeight,slice_coordinates,original_prepared_slice,
    UnifiedOrbitals.ao,mul_left_comm,mul_assoc]

theorem full_preparation_integrable (uTime : ℝ) (first second : Mother) (b c : Basis) :
    Integrable (fun x : Point => inner ℂ (preparedSection first b 1 (spatialSlice uTime x))
      (preparedSection second c 1 (spatialSlice uTime x))) := by
  simp_rw [full_preparation_pair]
  exact (UnifiedOrbitals.source_product_integrable b c ContinuousGradient.zeroJet ContinuousGradient.zeroJet).ofReal.mul_const _

/-- Every full mother preparation retains the original spatial metric and original independent quantum response. -/
theorem full_preparation_metric (uTime : ℝ) (first second : Mother) (b c : Basis) :
    (∫ x : Point, inner ℂ (preparedSection first b 1 (spatialSlice uTime x))
      (preparedSection second c 1 (spatialSlice uTime x))) =
      (UnifiedOrbitals.overlap b c : ℂ) *
        State.vectorEvaluation (Stage10.Runtime.tick.answer (spatialSlice uTime 0))
          (Compatibility.responseMatrix (pairedMother first second)) := by
  simp_rw [full_preparation_pair]
  rw [integral_mul_const,integral_complex_ofReal,source_gram]
  rfl

end
end LAlanine40K2025.UnifiedAction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
