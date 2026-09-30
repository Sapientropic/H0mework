import H0mework.Versions.X.NavierStokes.MaterialJets.Coefficients

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeBalancedGaugeEnergy

open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction
open NativeCartanConstitutive NativeBalancedColorControl NativeBalancedJetCoefficients

noncomputable section

theorem source_vector_eq (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity)
      (NativeSourceColorAction.increment velocity
        (coefficients (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative))) =
      gaugeVector velocity (NativeMaterialJetAction.target velocity derivative) := by
  rw [NativeSourceColorAction.vector_eq, gaugeVector_eq_principal, wholeAction_eq, wholeAction_eq,
    response_eq_original]
  rfl

def energy (block : Block) : ℝ := ∑ row : Fin 2, ∑ column : Fin 2, Complex.normSq (block row column)

def colorBlock (velocity coefficients : Vector) : Block :=
  ∑ color, (coefficients color : ℂ) • colorAction (hermitianBlock velocity) color

theorem colorBlock_energy (velocity coefficients : Vector) :
    energy (colorBlock velocity coefficients) = NativePauliJet.density velocity * squared coefficients := by
  simp [energy, colorBlock, colorAction, hermitianBlock, pauli, squared, NativePauliJet.density,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem energy_smul (scale : ℝ) (block : Block) : energy ((scale : ℂ) • block) = scale ^ 2 * energy block := by
  simp [energy, Complex.normSq_mul, Complex.normSq_ofReal, pow_two]
  ring

def spatialBlock (velocity : Vector) (derivative : Fin 4 → Vector) (direction : Fin 3) : Block :=
  (((NativePauliJet.density velocity)⁻¹ : ℝ) : ℂ) • colorBlock velocity (coefficients velocity derivative direction.succ)

theorem spatialBlock_energy (velocity : Vector) (derivative : Fin 4 → Vector) (direction : Fin 3) :
    energy (spatialBlock velocity derivative direction) =
      squared (coefficients velocity derivative direction.succ) / NativePauliJet.density velocity := by
  rw [spatialBlock, energy_smul, colorBlock_energy]
  field_simp [(NativePauliJet.density_pos velocity).ne']

theorem spatial_energy_bound (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ direction, energy (spatialBlock velocity derivative direction)) ≤
      3 / 4 * squared (derivative 0) + 5 / 2 * squared (curl derivative) := by
  simp only [spatialBlock_energy, squared, ← Finset.sum_div]
  apply (div_le_iff₀ (NativePauliJet.density_pos velocity)).2
  have bound := spatial_bound velocity derivative
  have velocityNonnegative : 0 ≤ squared velocity := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have derivativeNonnegative : 0 ≤ squared (derivative 0) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have curlNonnegative : 0 ≤ squared (curl derivative) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  change _ ≤ (3 / 4 * squared (derivative 0) + 5 / 2 * squared (curl derivative)) *
    (2 * (1 + squared velocity))
  nlinarith [mul_nonneg velocityNonnegative derivativeNonnegative]

theorem source_increment (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    NativeSourceColorAction.increment velocity
      (coefficients (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative)) direction.succ =
        lowerMatter (spatialBlock (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative) direction) := by
  rw [NativeSourceColorAction.increment_block, spatialBlock, map_smul]
  have factor : compensation velocity direction.succ = (NativePauliJet.density (normalizedVelocity velocity))⁻¹ := by
    rw [← NativeMaterialJetAction.source_density]
    fin_cases direction <;> rfl
  rw [factor]
  rfl

abbrev HilbertBlock := EuclideanSpace ℂ (Fin 2 × Fin 2)

def hilbertBlock (block : Block) : HilbertBlock := WithLp.toLp 2 (fun index => block index.1 index.2)

theorem hilbertBlock_norm_sq (block : Block) : ‖hilbertBlock block‖ ^ 2 = energy block := by
  simp [hilbertBlock, EuclideanSpace.norm_sq_eq, energy, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

private def blockLinear : HilbertBlock →ₗ[ℂ] Block where
  toFun value := fun row column => value (row, column)
  map_add' := by intro first second; rfl
  map_smul' := by intro scalar block; rfl

def materialEmbedding : HilbertBlock →L[ℂ] MatterCoordinateCarrier :=
  (matterCoordinateEquiv.toLinearMap.comp (lowerMatter.comp blockLinear)).toContinuousLinearMap

theorem materialEmbedding_apply (block : Block) :
    materialEmbedding (hilbertBlock block) = matterCoordinateEquiv (lowerMatter block) := rfl

theorem full_material_energy (block : Block) :
    ‖matterCoordinateEquiv (lowerMatter block)‖ ^ 2 ≤ ‖materialEmbedding‖ ^ 2 * energy block := by
  rw [← materialEmbedding_apply]
  have bound := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (materialEmbedding.le_opNorm (hilbertBlock block))
  simpa only [mul_pow, hilbertBlock_norm_sq] using bound

/-- Complete mother-matter coordinates, not a finite Fourier observation, consume the same jet energy. -/
theorem source_material_energy (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) :
    (∑ direction : Fin 3, ‖matterCoordinateEquiv (NativeSourceColorAction.increment velocity
      (coefficients (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative)) direction.succ)‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 *
        (3 / 4 * squared (NativeMaterialJetAction.normalizedJet derivative 0) +
          5 / 2 * squared (curl (NativeMaterialJetAction.normalizedJet derivative))) := by
  simp only [source_increment]
  calc
    _ ≤ ∑ direction : Fin 3, ‖materialEmbedding‖ ^ 2 * energy
        (spatialBlock (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative) direction) :=
      Finset.sum_le_sum fun _ _ => full_material_energy _
    _ = _ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (spatial_energy_bound _ _) (sq_nonneg _)

end
end SaturationMonoid.NavierStokes.NativeBalancedGaugeEnergy
