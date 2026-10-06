import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Orbitals
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.SectionPreparations

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource Stage9DEF
open BasinRefinement SourceGaussianModel SourceFiniteData MeasureTheory UnifiedAction YangMills.FullPairing
open scoped InnerProductSpace
noncomputable section

def normalizedSection (b : Basis) (time : ℝ) (x : Point) : Hilbert :=
  (normalizedOrbital b x : ℂ) • prepared (spatialSlice time x)

def normalizedPreparedSection (A : Mother) (b : Basis) (time : ℝ) (x : Point) : Hilbert :=
  (normalizedOrbital b x : ℂ) • operator A (prepared (spatialSlice time x))

theorem normalizedSection_pair (b c : Basis) (time : ℝ) (x : Point) :
    inner ℂ (normalizedSection b time x) (normalizedSection c time x) =
      (normalizedOrbital b x*normalizedOrbital c x : ℝ) := by
  simp [normalizedSection,inner_self_eq_norm_sq_to_K,prepared_norm,mul_comm]

theorem normalized_U_section_integral (positive : actualGram.PosDef) (b c : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (normalizedSection b time x) (normalizedSection c time x)) =
      if b=c then 1 else 0 := by
  simp_rw [normalizedSection_pair]
  rw [integral_complex_ofReal,normalized_pair positive]
  split_ifs <;> norm_num

theorem normalized_preparation_pair (A B : Mother) (b c : Basis) (time : ℝ) (x : Point) :
    inner ℂ (normalizedPreparedSection A b time x) (normalizedPreparedSection B c time x) =
      (normalizedOrbital b x*normalizedOrbital c x : ℝ) *
        inner ℂ (operator A (prepared (spatialSlice time 0)))
          (operator B (prepared (spatialSlice time 0))) := by
  simp [normalizedPreparedSection,original_prepared_slice,mul_left_comm,mul_assoc]

theorem normalized_preparation_integrable (A B : Mother) (b c : Basis) (time : ℝ) :
    Integrable (fun x : Point => inner ℂ (normalizedPreparedSection A b time x)
      (normalizedPreparedSection B c time x)) := by
  simp_rw [normalized_preparation_pair]
  exact (normalized_pair_integrable b c).ofReal.mul_const _

/-- Full 252-dimensional preparation and the independent quantum response share the exact orbital Gram. -/
theorem normalized_full_U_preparation (positive : actualGram.PosDef)
    (A B : Mother) (b c : Basis) (time : ℝ) :
    (∫ x : Point, inner ℂ (normalizedPreparedSection A b time x)
      (normalizedPreparedSection B c time x)) =
      (if b=c then 1 else 0) * State.vectorEvaluation (Stage10.Runtime.tick.answer (spatialSlice time 0))
        (Compatibility.responseMatrix (pairedMother A B)) := by
  simp_rw [normalized_preparation_pair]
  rw [integral_mul_const,integral_complex_ofReal,normalized_pair positive,source_gram]
  split_ifs <;> norm_num

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
