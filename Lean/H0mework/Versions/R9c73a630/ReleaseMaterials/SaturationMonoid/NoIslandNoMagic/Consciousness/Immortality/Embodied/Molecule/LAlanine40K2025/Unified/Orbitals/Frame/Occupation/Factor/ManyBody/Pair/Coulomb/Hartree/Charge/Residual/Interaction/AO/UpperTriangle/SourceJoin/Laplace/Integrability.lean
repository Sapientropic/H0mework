import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace.Continuity

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.GaussianPair
open BasinRefinement.SourceGaussianModel BasinRefinement.SourceCoulomb
open BasinRefinement.ContinuousGradient BasinRefinement.GlobalSource MeasureTheory Set
noncomputable section

theorem heat_section_integrable
    (left right nextLeft nextRight : Term) (z : Point × Point)
    (offDiagonal : z.1 ≠ z.2) :
    Integrable (heatIntegrand left right nextLeft nextRight z)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hsub : z.2 - z.1 ≠ 0 := sub_ne_zero.mpr offDiagonal.symm
  have hd : 0 < distance (z.2 - z.1) :=
    (norm_pos_iff.mpr hsub).trans_le (pi_norm_le_distance _)
  have hgaussian : IntegrableOn
      (fun t : ℝ => Real.exp (-(distance (z.2 - z.1))^2 * t^2))
      (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (sq_pos_of_pos hd)
  convert hgaussian.const_mul
    (primitiveAmplitude left right nextLeft nextRight z *
      (2 / Real.sqrt Real.pi)) using 1
  funext t
  rfl

theorem heat_norm_integral
    (left right nextLeft nextRight : Term) (z : Point × Point) :
    (∫ t in Ioi (0 : ℝ),
      ‖heatIntegrand left right nextLeft nextRight z t‖) =
      ‖primitiveAmplitude left right nextLeft nextRight z *
        kernel (z.2 - z.1)‖ := by
  have pointwise (t : ℝ) :
      ‖heatIntegrand left right nextLeft nextRight z t‖ =
        |primitiveAmplitude left right nextLeft nextRight z| *
          (2 / Real.sqrt Real.pi) *
            Real.exp (-(distance (z.2-z.1))^2 * t^2) := by
    unfold heatIntegrand
    simp [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg Real.pi)]
  calc
    (∫ t in Ioi (0 : ℝ), ‖heatIntegrand left right nextLeft nextRight z t‖) =
        ∫ t in Ioi (0 : ℝ),
          |primitiveAmplitude left right nextLeft nextRight z| *
            (2 / Real.sqrt Real.pi) *
              Real.exp (-(distance (z.2-z.1))^2 * t^2) := by
      congr 1
      funext t
      exact pointwise t
    _ = |primitiveAmplitude left right nextLeft nextRight z| *
          ((2 / Real.sqrt Real.pi) *
            ∫ t in Ioi (0 : ℝ),
              Real.exp (-(distance (z.2-z.1))^2 * t^2)) := by
      rw [integral_const_mul]
      ring
    _ = |primitiveAmplitude left right nextLeft nextRight z| *
          kernel (z.2-z.1) := by rw [← kernel_laplace]
    _ = _ := by
      simp [Real.norm_eq_abs,abs_of_nonneg (kernel_nonnegative _)]

theorem primitive_heat_integrable
    (left right nextLeft nextRight : Term)
    (leftPositive : 0 < left.exponent) (rightPositive : 0 < right.exponent)
    (nextLeftPositive : 0 < nextLeft.exponent)
    (nextRightPositive : 0 < nextRight.exponent) :
    Integrable
      (fun w : (Point × Point) × ℝ =>
        heatIntegrand left right nextLeft nextRight w.1 w.2)
      ((volume : Measure (Point × Point)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  apply (integrable_prod_iff
    (heat_continuous left right nextLeft nextRight).aestronglyMeasurable).2
  constructor
  · filter_upwards [off_diagonal_ae] with z hz
    exact heat_section_integrable left right nextLeft nextRight z hz
  · have hCoulomb :=
      (pair_kernel_integrable left right nextLeft nextRight
        leftPositive rightPositive nextLeftPositive nextRightPositive).norm
    simpa only [heat_norm_integral,primitiveAmplitude] using hCoulomb


end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
