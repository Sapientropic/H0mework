import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Projector
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransportError

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
attribute [local irreducible] factor normalizedFactor projector24 gram rawGamma candidateGamma
open Propagation.Interface
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

private theorem factor_from_isometry :
    normalizedFactor * CFC.sqrt gram = factor := by
  have rootUnit : IsUnit (CFC.sqrt gram) :=
    (CFC.isUnit_sqrt_iff gram gram_positive.posSemidef.nonneg).mpr gram_positive.isUnit
  let := rootUnit.invertible
  simp [normalizedFactor, correction, Matrix.mul_assoc]

theorem isometry_norm : ‖normalizedFactor‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self normalizedFactor
  rw [normalized_isometry, norm_one] at h
  nlinarith [norm_nonneg normalizedFactor]

theorem normalization_error :
    ‖normalizedFactor - factor‖ ≤ ‖gram - 1‖ := by
  have identity : normalizedFactor - factor =
      normalizedFactor * (1 - CFC.sqrt gram) := by
    rw [Matrix.mul_sub, Matrix.mul_one, factor_from_isometry]
  rw [identity]
  calc
    _ ≤ ‖normalizedFactor‖ * ‖1 - CFC.sqrt gram‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖CFC.sqrt gram - 1‖ := by rw [isometry_norm, one_mul, norm_sub_rev]
    _ ≤ ‖gram - 1‖ :=
      ElectronicFrame.Polar.sqrt_residual_norm gram gram_positive.posSemidef.nonneg

theorem factor_norm : ‖factor‖ ≤ 1 + ‖gram - 1‖ := by
  calc
    ‖factor‖ = ‖normalizedFactor * CFC.sqrt gram‖ := by rw [factor_from_isometry]
    _ ≤ ‖normalizedFactor‖ * ‖CFC.sqrt gram‖ := Matrix.l2_opNorm_mul _ _
    _ = ‖CFC.sqrt gram‖ := by rw [isometry_norm, one_mul]
    _ ≤ ‖(1 : Matrix OccupiedSlot OccupiedSlot ℂ)‖ + ‖CFC.sqrt gram - 1‖ := by
      convert norm_add_le (1 : Matrix OccupiedSlot OccupiedSlot ℂ) (CFC.sqrt gram - 1) using 1
      abel
    _ ≤ 1 + ‖gram - 1‖ := by
      rw [norm_one]
      exact add_le_add_right
        (ElectronicFrame.Polar.sqrt_residual_norm gram gram_positive.posSemidef.nonneg) 1

theorem projector_error :
    ‖candidateGamma - (2 : ℂ) • projector24‖ ≤
      2 * ‖gram - 1‖ * (2 + ‖gram - 1‖) := by
  have matrix_identity :
      projector24 - factor * factor.conjTranspose =
        (normalizedFactor - factor) * normalizedFactor.conjTranspose +
          factor * (normalizedFactor - factor).conjTranspose := by
    simp only [projector24, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have base : ‖projector24 - factor * factor.conjTranspose‖ ≤
      ‖normalizedFactor - factor‖ * (1 + ‖factor‖) := by
    rw [matrix_identity]
    calc
      _ ≤ ‖(normalizedFactor - factor) * normalizedFactor.conjTranspose‖ +
          ‖factor * (normalizedFactor - factor).conjTranspose‖ := norm_add_le _ _
      _ ≤ ‖normalizedFactor - factor‖ * ‖normalizedFactor.conjTranspose‖ +
          ‖factor‖ * ‖(normalizedFactor - factor).conjTranspose‖ := by
            exact add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
      _ = ‖normalizedFactor - factor‖ * (1 + ‖factor‖) := by
            rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose,
              isometry_norm]
            ring
  have δnonneg : 0 ≤ ‖gram - 1‖ := norm_nonneg _
  have fnonneg : 0 ≤ ‖factor‖ := norm_nonneg _
  have projection_bound :
      ‖projector24 - factor * factor.conjTranspose‖ ≤
        ‖gram - 1‖ * (2 + ‖gram - 1‖) :=
    base.trans (mul_le_mul normalization_error (by linarith [factor_norm])
      (by linarith) δnonneg)
  unfold candidateGamma
  rw [← smul_sub, norm_smul]
  have two_norm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [two_norm]
  have reverse : ‖factor * factor.conjTranspose - projector24‖ =
      ‖projector24 - factor * factor.conjTranspose‖ := norm_sub_rev _ _
  rw [reverse]
  calc
    2 * ‖projector24 - factor * factor.conjTranspose‖ ≤
        2 * (‖gram - 1‖ * (2 + ‖gram - 1‖)) := by
          exact mul_le_mul_of_nonneg_left projection_bound (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by ring

theorem source_projection_error :
    ‖rawGamma - (2 : ℂ) • projector24‖ ≤
      98 * ((gammaEntryBound : ℝ) / ((gammaScale : ℝ) * (factorScale : ℝ)^2)) +
        2 * (24 * ((gramEntryBound : ℝ) / (factorScale : ℝ)^2)) *
          (2 + 24 * ((gramEntryBound : ℝ) / (factorScale : ℝ)^2)) := by
  let γ : ℝ := 98 * ((gammaEntryBound : ℝ) /
    ((gammaScale : ℝ) * (factorScale : ℝ)^2))
  let δ : ℝ := 24 * ((gramEntryBound : ℝ) / (factorScale : ℝ)^2)
  have γbound : ‖rawGamma - candidateGamma‖ ≤ γ := gamma_norm_bound
  have δbound : ‖gram - 1‖ ≤ δ := gram_norm_bound
  have δpositive : 0 ≤ ‖gram - 1‖ := norm_nonneg _
  have δnonnegative : 0 ≤ δ := by norm_num [δ,gramEntryBound,factorScale]
  have projection := projector_error
  have triangle : ‖rawGamma - (2 : ℂ) • projector24‖ ≤
      ‖rawGamma - candidateGamma‖ +
        ‖candidateGamma - (2 : ℂ) • projector24‖ := by
    convert norm_add_le (rawGamma - candidateGamma)
      (candidateGamma - (2 : ℂ) • projector24) using 1
    abel
  have product : ‖gram - 1‖ * (2 + ‖gram - 1‖) ≤ δ * (2 + δ) := by
    exact mul_le_mul δbound (by linarith) (by positivity) δnonnegative
  change ‖rawGamma - (2 : ℂ) • projector24‖ ≤ γ + 2 * δ * (2 + δ)
  nlinarith

theorem source_projection_error_small :
    ‖rawGamma - (2 : ℂ) • projector24‖ < (1 / 10^9 : ℝ) := by
  have h := source_projection_error
  exact h.trans_lt (by norm_num [gammaEntryBound,gammaScale,gramEntryBound,factorScale])

theorem raw_gamma_norm_lt_three : ‖rawGamma‖ < 3 := by
  have δ : ‖gram - 1‖ < (1 / 1000 : ℝ) :=
    gram_norm_bound.trans_lt (by norm_num [gramEntryBound,factorScale])
  have γ : ‖rawGamma - candidateGamma‖ < (1 / 1000 : ℝ) :=
    gamma_norm_bound.trans_lt (by norm_num [gammaEntryBound,gammaScale,factorScale])
  have v : ‖factor‖ ≤ (1001 / 1000 : ℝ) := by linarith [factor_norm]
  have vSquared : ‖factor‖^2 ≤ (1001 / 1000 : ℝ)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) v 2
  have candidate : ‖candidateGamma‖ ≤ 2 * ‖factor‖^2 := by
    rw [candidateGamma,norm_smul]
    have twoNorm : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [twoNorm]
    have mulBound := Matrix.l2_opNorm_mul factor factor.conjTranspose
    rw [Matrix.l2_opNorm_conjTranspose] at mulBound
    nlinarith
  have triangle : ‖rawGamma‖ ≤ ‖rawGamma - candidateGamma‖ + ‖candidateGamma‖ := by
    calc
      ‖rawGamma‖ = ‖(rawGamma - candidateGamma) + candidateGamma‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
