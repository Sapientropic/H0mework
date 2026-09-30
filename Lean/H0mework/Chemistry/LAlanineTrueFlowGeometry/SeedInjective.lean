import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedAlgebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel ContinuousGradient ContinuousSeed TrueTubeWholeActual
open TrueTubeActual WholeCellPartition Matrix Set
open scoped Matrix
noncomputable section

theorem actual_seed_width_positive (p : BandPoint) :
    0 < bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) := by
  have epsilon : (0 : ℝ) < (Geometry.Source.epsilon 0 : ℝ) := by
    exact_mod_cast (show 0 < Geometry.Source.epsilon 0 from by decide +kernel)
  have source_interval : knotCoordinate (firstKnot 4) ≤ fullLowerQ 1 ∧
      fullUpperQ 1 ≤ knotCoordinate (lastKnot 4) := by decide +kernel
  apply bandWidth_positive 4 _ _ epsilon
  exact ⟨(Rat.cast_le.mpr source_interval.1).trans (p.property.1 1),
    (p.property.2 1).trans (Rat.cast_le.mpr source_interval.2)⟩

def seedFlowDerivative (p : BandPoint) : Point →L[ℝ] Point :=
  bandSeedDerivative 4 (Geometry.Source.epsilon 0) p.val +
    (ContinuousLinearMap.proj 2).smulRight
      (sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val))

theorem seedFlowDerivative_injective (p : BandPoint) : Function.Injective (seedFlowDerivative p) := by
  apply (injective_iff_map_eq_zero (seedFlowDerivative p)).mpr
  intro h zero
  have expansion :
      bandUDerivative 4 (Geometry.Source.epsilon 0) p.val h • basisVector 0 +
        h 1 • basisVector 1 + h 2 •
          sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val) = 0 := zero
  have transverse := original_gradient_transverse (ContinuousParameterMap.initialMap 0 4 p.val)
    ((TrueTubeChecks.initial_field_eq 0).symm ▸ actual_seed_initial 0 p.val p.property)
  have normal := congrArg (fun v : Point => seedNormal ⬝ᵥ v) expansion
  have timeProduct : h 2 * (seedNormal ⬝ᵥ
      sourceGradient (ContinuousParameterMap.initialMap 0 4 p.val)) = 0 := by
    simpa only [dotProduct_add, dotProduct_smul, seedNormal_dot_basis, smul_zero,
      zero_add, dotProduct_zero, smul_eq_mul, mul_zero] using normal
  have timeZero : h 2 = 0 := (mul_eq_zero.mp timeProduct).resolve_right transverse.ne'
  rw [timeZero, zero_smul, add_zero] at expansion
  have coefficients := seed_basis_coefficients _ _ expansion
  have alphaProduct : bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) * h 0 = 0 := by
    simpa [bandUDerivative, coefficients.2] using coefficients.1
  have alphaZero : h 0 = 0 :=
    (mul_eq_zero.mp alphaProduct).resolve_left (actual_seed_width_positive p).ne'
  funext i
  fin_cases i
  · exact alphaZero
  · exact coefficients.2
  · exact timeZero

theorem seed_coordinates_of_eq (p q : BandPoint)
    (same : ContinuousParameterMap.initialMap 0 4 p.val =
      ContinuousParameterMap.initialMap 0 4 q.val) :
    p.val 0 = q.val 0 ∧ p.val 1 = q.val 1 := by
  have difference :
      (bandU 4 (Geometry.Source.epsilon 0) p.val - bandU 4 (Geometry.Source.epsilon 0) q.val) •
          basisVector 0 + (p.val 1 - q.val 1) • basisVector 1 =
        ContinuousParameterMap.initialMap 0 4 p.val - ContinuousParameterMap.initialMap 0 4 q.val := by
    ext i
    simp only [ContinuousParameterMap.initialMap, bandSeed, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [same, sub_self] at difference
  have coefficients := seed_basis_coefficients _ _ difference
  have vEqual : p.val 1 = q.val 1 := sub_eq_zero.mp coefficients.2
  have uEqual := sub_eq_zero.mp coefficients.1
  have alphaProduct : (p.val 0 - q.val 0) *
      bandWidth 4 (Geometry.Source.epsilon 0) (p.val 1) = 0 := by
    rw [bandU, bandU, ← vEqual] at uEqual
    linear_combination uEqual
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp alphaProduct).resolve_right
    (actual_seed_width_positive p).ne'), vEqual⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
