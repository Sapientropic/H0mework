import H0mework.Versions.X.NavierStokes.MaterialJets.CovariantEnergy

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise ENNReal

namespace SaturationMonoid.NavierStokes.NativeCovariantMaterialField

open MeasureTheory PhysicsCore StageNineHolonomicField
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePhysicalFourier NativePhysicalTimeAction NativePauliCoframeAction NativeMaterialJetAction
open NativePauliControl NativePauliMotherAction NativeCartanConstitutive NativeBalancedGaugeEnergy
open NativeCovariantMaterialEnergy

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : MeasurableSpace Block := inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → ℂ))
local instance : BorelSpace Block := inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℂ))
local instance : OpensMeasurableSpace (MatterCoordinateCarrier × MatterCoordinateCarrier) := Prod.opensMeasurableSpace
local instance : MeasurableAdd₂ MatterCoordinateCarrier := ⟨continuous_add.measurable⟩

private def lowerCoordinates : Block →L[ℂ] MatterCoordinateCarrier :=
  (matterCoordinateEquiv.toLinearMap.comp lowerMatter).toContinuousLinearMap

def evaluation (data : PhysicalSpace × (Fin 4 → PhysicalSpace)) (direction : Fin 3) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (lowerMatter (covariantBlock data.1 data.2 direction))

theorem evaluation_eq (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    evaluation (velocity, derivative) direction =
      matterCoordinateEquiv (NativeBalancedMaterialJet.derivative velocity derivative direction.succ) := by
  rw [source_derivative]
  rfl

private theorem raw_measurable (direction : Fin 3) :
    Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) => NativePauliJet.tangent (normalizedJet data.2 direction.succ)) := by
  apply measurable_pi_lambda
  intro row
  apply measurable_pi_lambda
  intro column
  simp only [NativePauliJet.tangent, normalizedJet, normalizedVelocity, Fin.sum_univ_three,
    Matrix.add_apply, Matrix.smul_apply]
  fun_prop

private theorem geometric_measurable (direction : Fin 3) :
    Measurable (fun data : PhysicalSpace × (Fin 4 → PhysicalSpace) =>
      NativeGeometricMaterial.spatialBlock (normalizedVelocity data.1) (normalizedJet data.2) direction) := by
  apply measurable_pi_lambda
  intro row
  apply measurable_pi_lambda
  intro column
  fin_cases direction <;>
    simp only [NativeGeometricMaterial.spatialBlock, NativeGeometricMaterial.spinBlock, NativeGeometricMaterial.rotation,
      NativePauliJet.logDerivative, NativePauliJet.density, NativePauliJet.tangent,
      NativeCartanClifford.blockAction, spinAction, hermitianBlock, normalizedJet, normalizedVelocity,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply]
  all_goals fun_prop

private theorem constitutive_measurable (direction : Fin 3) :
    Measurable (fun velocity : PhysicalSpace => NativeConstitutiveMaterialEnergy.materialBlock velocity direction) := by
  apply measurable_pi_lambda
  intro row
  apply measurable_pi_lambda
  intro column
  fin_cases direction <;>
    simp only [NativeConstitutiveMaterialEnergy.materialBlock, colorBlock, NativeConstitutiveColor.radial,
      NativeCanonicalFluidCoframe.scale, NativeCanonicalFluidCoframe.density, NativeCartanStressLaw.fluxFactor,
      squared, denominator, normalizedVelocity, colorAction, hermitianBlock,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply]
  all_goals fun_prop

theorem evaluation_measurable (direction : Fin 3) : Measurable (fun data => evaluation data direction) := by
  have split : (fun data => evaluation data direction) = fun data =>
      lowerCoordinates (NativePauliJet.tangent (normalizedJet data.2 direction.succ)) +
      lowerCoordinates (NativeGeometricMaterial.spatialBlock (normalizedVelocity data.1) (normalizedJet data.2) direction) +
      NativeBalancedMaterialField.evaluation data direction +
      lowerCoordinates (NativeConstitutiveMaterialEnergy.materialBlock data.1 direction) := by
    funext data
    simp only [evaluation, covariantBlock, map_add, NativeBalancedMaterialField.evaluation, materialEmbedding_apply]
    rfl
  rw [split]
  exact (((lowerCoordinates.continuous.measurable.comp (raw_measurable direction)).add
    (lowerCoordinates.continuous.measurable.comp (geometric_measurable direction))).add
      (NativeBalancedMaterialField.evaluation_measurable direction)).add
    (lowerCoordinates.continuous.measurable.comp ((constitutive_measurable direction).comp measurable_fst))

def response (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) (point : Torus) :
    MatterCoordinateCarrier := evaluation (velocity point, fun index => derivative index point) direction

theorem response_measurable (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    AEStronglyMeasurable (response velocity derivative direction) volume := by
  have whole : MemLp (fun point : Torus => fun index => derivative index point) 2 volume :=
    memLp_pi_iff.mpr (fun index => Lp.memLp (derivative index))
  exact ((evaluation_measurable direction).comp_aemeasurable
    ((Lp.memLp velocity).1.aemeasurable.prodMk whole.1.aemeasurable)).aestronglyMeasurable

theorem response_memLp (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    MemLp (response velocity derivative direction) 2 volume := by
  have spatial : Integrable (fun point : Torus => ∑ index : Fin 3, ‖derivative index.succ point‖ ^ 2) volume :=
    integrable_finsetSum _ (fun index _ => (Lp.memLp (derivative index.succ)).norm.integrable_sq)
  have value := (Lp.memLp velocity).norm.integrable_sq
  have temporal := (Lp.memLp (derivative 0)).norm.integrable_sq
  apply (memLp_two_iff_integrable_sq_norm (response_measurable velocity derivative direction)).2
  apply ((((value.const_mul 32).add (temporal.const_mul (7 / 16))).add (spatial.const_mul 2)).const_mul
    (‖materialEmbedding‖ ^ 2)).mono' ((response_measurable velocity derivative direction).norm.pow 2)
  filter_upwards [] with point
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have whole := full_material_bound (velocity point) (fun coordinate => derivative coordinate point)
  have one := Finset.single_le_sum (f := fun index : Fin 3 => ‖response velocity derivative index point‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ direction)
  simp only [response, evaluation_eq] at one ⊢
  exact one.trans whole

def materialField (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    Lp MatterCoordinateCarrier 2 (volume : Measure Torus) :=
  (response_memLp velocity derivative direction).toLp (response velocity derivative direction)

theorem materialField_apply (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) (direction : Fin 3) :
    materialField velocity derivative direction =ᵐ[volume] fun point =>
      matterCoordinateEquiv (NativeBalancedMaterialJet.derivative (velocity point)
        (fun coordinate => derivative coordinate point) direction.succ) :=
  (response_memLp velocity derivative direction).coeFn_toLp.trans
    (Filter.Eventually.of_forall fun _ => evaluation_eq _ _ _)

private theorem l2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (field : Lp E 2 (volume : Measure Torus)) : ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem field_energy_bound (velocity : PhysicalField) (derivative : Fin 4 → PhysicalField) :
    (∑ direction : Fin 3, ‖materialField velocity derivative direction‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 *
        (32 * ‖velocity‖ ^ 2 + 7 / 16 * ‖derivative 0‖ ^ 2 + 2 * ∑ direction : Fin 3, ‖derivative direction.succ‖ ^ 2) := by
  have each (direction : Fin 3) := (Lp.memLp (materialField velocity derivative direction)).norm.integrable_sq
  have value := (Lp.memLp velocity).norm.integrable_sq
  have time := (Lp.memLp (derivative 0)).norm.integrable_sq
  have spatial (direction : Fin 3) := (Lp.memLp (derivative direction.succ)).norm.integrable_sq
  have all := ae_all_iff.mpr (fun direction => materialField_apply velocity derivative direction)
  have pointwise : ∀ᵐ point : Torus, (∑ direction : Fin 3, ‖materialField velocity derivative direction point‖ ^ 2) ≤
      ‖materialEmbedding‖ ^ 2 * (32 * ‖velocity point‖ ^ 2 + 7 / 16 * ‖derivative 0 point‖ ^ 2 +
        2 * ∑ direction : Fin 3, ‖derivative direction.succ point‖ ^ 2) := by
    filter_upwards [all] with point actual
    simp only [actual]
    exact full_material_bound _ _
  calc
    _ = ∫ point : Torus, ∑ direction : Fin 3, ‖materialField velocity derivative direction point‖ ^ 2 := by
      simp only [l2_norm_sq]
      exact (integral_finsetSum _ (fun direction _ => each direction)).symm
    _ ≤ ∫ point : Torus, ‖materialEmbedding‖ ^ 2 * (32 * ‖velocity point‖ ^ 2 + 7 / 16 * ‖derivative 0 point‖ ^ 2 +
        2 * ∑ direction : Fin 3, ‖derivative direction.succ point‖ ^ 2) :=
      integral_mono_ae (integrable_finsetSum _ (fun direction _ => each direction))
        ((((value.const_mul _).add (time.const_mul _)).add
          ((integrable_finsetSum _ (fun direction _ => spatial direction)).const_mul _)).const_mul _) pointwise
    _ = _ := by
      have split := integral_add ((value.const_mul 32).add (time.const_mul (7 / 16)))
        ((integrable_finsetSum Finset.univ (fun direction _ => spatial direction)).const_mul 2)
      simp only [Pi.add_apply] at split
      rw [integral_const_mul, split,
        integral_add (value.const_mul 32) (time.const_mul (7 / 16)),
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_finsetSum Finset.univ (fun direction _ => spatial direction)]
      simp only [← l2_norm_sq]

end
end SaturationMonoid.NavierStokes.NativeCovariantMaterialField
