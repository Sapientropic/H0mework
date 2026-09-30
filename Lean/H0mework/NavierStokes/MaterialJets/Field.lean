import H0mework.NavierStokes.MaterialJets.Energy

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise ENNReal

namespace SaturationMonoid.NavierStokes.NativeBalancedMaterialField

open MeasureTheory PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePhysicalFourier NativePhysicalTimeAction NativePauliCoframeAction NativeMaterialJetAction
open NativePauliControl NativePauliMotherAction NativeCartanConstitutive NativeBalancedColorControl NativeBalancedJetCoefficients NativeBalancedGaugeEnergy

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def evaluation (data : PhysicalSpace × (Fin 4 → PhysicalSpace)) (direction : Fin 3) : MatterCoordinateCarrier :=
  materialEmbedding (hilbertBlock (spatialBlock (normalizedVelocity data.1) (normalizedJet data.2) direction))

theorem evaluation_eq (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    evaluation (velocity, derivative) direction = matterCoordinateEquiv (NativeSourceColorAction.increment velocity
      (coefficients (normalizedVelocity velocity) (normalizedJet derivative)) direction.succ) := by
  rw [NativeBalancedGaugeEnergy.source_increment]
  exact materialEmbedding_apply _

private theorem coefficient_measurable (direction : Fin 4) (color : Fin 3) :
    Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) =>
      NativeBalancedJetCoefficients.coefficients (normalizedVelocity data.1) (normalizedJet data.2) direction color) := by
  fin_cases direction <;> fin_cases color <;>
    simp [NativeBalancedJetCoefficients.coefficients, normalizedJet, normalizedVelocity,
      temporalProjection, helicityCoefficient, pairing, weight, squared, denominator,
      curl, Fin.sum_univ_three]
  all_goals fun_prop

private theorem density_measurable :
    Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) => NativePauliJet.density (normalizedVelocity data.1)) := by
  simp only [NativePauliJet.density, normalizedVelocity, Fin.sum_univ_three]
  fun_prop

private theorem color_measurable (color : Fin 3) (row column : Fin 2) :
    Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) =>
      colorAction (hermitianBlock (normalizedVelocity data.1)) color row column) := by
  simp only [colorAction, hermitianBlock, normalizedVelocity, Fin.sum_univ_two, Fin.sum_univ_three,
    Matrix.add_apply, Matrix.smul_apply]
  fun_prop

theorem evaluation_measurable (direction : Fin 3) : Measurable (fun data => evaluation data direction) := by
  unfold evaluation
  apply materialEmbedding.continuous.measurable.comp
  change Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) =>
    WithLp.toLp 2 (fun index : Fin 2 × Fin 2 =>
      spatialBlock (normalizedVelocity data.1) (normalizedJet data.2) direction index.1 index.2))
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply measurable_pi_lambda
  intro index
  have coef (color : Fin 3) := coefficient_measurable direction.succ color
  have matrix (color : Fin 3) := color_measurable color index.1 index.2
  have rho := density_measurable
  change Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) =>
    (((NativePauliJet.density (normalizedVelocity data.1))⁻¹ : ℝ) : ℂ) *
      ∑ color : Fin 3, (NativeBalancedJetCoefficients.coefficients (normalizedVelocity data.1)
        (normalizedJet data.2) direction.succ color : ℂ) *
          colorAction (hermitianBlock (normalizedVelocity data.1)) color index.1 index.2)
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_sum
    intro color _
    fun_prop

def response (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) (point : Torus) :
    MatterCoordinateCarrier := evaluation (velocity point, fun index => derivative index point) direction

theorem response_measurable (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    AEStronglyMeasurable (response velocity derivative direction) volume := by
  have whole : MemLp (fun point : Torus => fun index => derivative index point) 2 volume :=
    memLp_pi_iff.mpr (fun index => Lp.memLp (derivative index))
  exact ((evaluation_measurable direction).comp_aemeasurable
    ((Lp.memLp velocity).1.aemeasurable.prodMk whole.1.aemeasurable)).aestronglyMeasurable

private theorem normalized_memLp (derivative : Fin 4 → PhysicalField) (direction : Fin 4) (index : Fin 3) :
    MemLp (fun point : Torus => normalizedJet (fun coordinate => derivative coordinate point) direction index) 2 volume := by
  simpa only [normalizedJet, normalizedVelocity, div_eq_mul_inv] using
    (memLp_piLp_iff.mp (Lp.memLp (derivative direction)) index).mul_const (4 : ℝ)⁻¹

private theorem curl_memLp (derivative : Fin 4 → PhysicalField) (index : Fin 3) :
    MemLp (fun point : Torus => curl (normalizedJet (fun coordinate => derivative coordinate point)) index) 2 volume := by
  fin_cases index
  · exact (normalized_memLp derivative 2 2).sub (normalized_memLp derivative 3 1)
  · exact (normalized_memLp derivative 3 0).sub (normalized_memLp derivative 1 2)
  · exact (normalized_memLp derivative 1 1).sub (normalized_memLp derivative 2 0)

theorem response_memLp (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    MemLp (response velocity derivative direction) 2 volume := by
  have timeIntegrable : Integrable (fun point : Torus => squared
      (normalizedJet (fun coordinate => derivative coordinate point) 0)) volume := by
    exact integrable_finsetSum _ (fun index _ => (normalized_memLp derivative 0 index).integrable_sq)
  have curlIntegrable : Integrable (fun point : Torus => squared
      (curl (normalizedJet (fun coordinate => derivative coordinate point)))) volume := by
    exact integrable_finsetSum _ (fun index _ => (curl_memLp derivative index).integrable_sq)
  apply (memLp_two_iff_integrable_sq_norm (response_measurable velocity derivative direction)).2
  apply (((timeIntegrable.const_mul (3 / 4)).add (curlIntegrable.const_mul (5 / 2))).const_mul
    (‖materialEmbedding‖ ^ 2)).mono'
    ((response_measurable velocity derivative direction).norm.pow 2)
  filter_upwards [] with point
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have whole := source_material_energy (velocity point) (fun coordinate => derivative coordinate point)
  have one := Finset.single_le_sum (f := fun index : Fin 3 => ‖response velocity derivative index point‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ direction)
  simp only [response, evaluation_eq] at one ⊢
  exact one.trans whole

def materialField (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    Lp MatterCoordinateCarrier 2 (volume : Measure Torus) :=
  (response_memLp velocity derivative direction).toLp (response velocity derivative direction)

theorem materialField_apply (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    materialField velocity derivative direction =ᵐ[volume] fun point =>
      matterCoordinateEquiv (NativeSourceColorAction.increment (velocity point)
        (coefficients (normalizedVelocity (velocity point))
          (normalizedJet (fun coordinate => derivative coordinate point))) direction.succ) := by
  exact (response_memLp velocity derivative direction).coeFn_toLp.trans
    (Filter.Eventually.of_forall fun point => evaluation_eq _ _ _)

end
end SaturationMonoid.NavierStokes.NativeBalancedMaterialField
