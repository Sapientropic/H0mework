import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.AllSlots

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticPrimitiveKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedQuarticTime NativeUnheatedQuarticAllSlots NativeCompleteStressCarrier
open NativeUnheatedSourceGradient NativeWholeH1Mixed
noncomputable section
variable {nu : Viscosity}

def scale (nu : Viscosity) : ℝ := nu.coeff * (2*Real.pi)^2 / 4

theorem scale_positive (nu : Viscosity) : 0 < scale nu := by unfold scale; positivity [nu.coeff_pos]

theorem rate_floor (a b c d : Slot) (nonzero : a.1 ≠ 0 ∨ b.1 ≠ 0 ∨ c.1 ≠ 0 ∨ d.1 ≠ 0) :
    nu.coeff*(2*Real.pi)^2 ≤ sumRate nu a b c d := by
  have lower : 1 ≤ integerWaveNormSq a.1+integerWaveNormSq b.1+integerWaveNormSq c.1+integerWaveNormSq d.1 := by
    rcases nonzero with first | second | third | last
    all_goals linarith [one_le_integerWaveNormSq _ (by assumption), integerWaveNormSq_nonneg a.1,
      integerWaveNormSq_nonneg b.1, integerWaveNormSq_nonneg c.1, integerWaveNormSq_nonneg d.1]
  have paid := mul_le_mul_of_nonneg_left lower (mul_nonneg nu.coeff_pos.le (sq_nonneg (2*Real.pi)))
  simpa only [mul_one, sumRate, integerWaveViscousMultiplier, mul_add, mul_assoc] using paid

theorem inverse_bound (a b c d : Slot) :
    (sumRate nu a b c d)⁻¹ ≤ (scale nu)⁻¹ * weight (a.1+b.1+c.1+d.1) := by
  by_cases nonzero : a.1 ≠ 0 ∨ b.1 ≠ 0 ∨ c.1 ≠ 0 ∨ d.1 ≠ 0
  · have lower : scale nu * (weight (a.1+b.1+c.1+d.1))⁻¹ ≤ sumRate nu a b c d := by
      by_cases zero : a.1+b.1+c.1+d.1 = 0
      · simp only [weight, if_pos zero, inv_one, mul_one]
        have paid := rate_floor (nu := nu) a b c d nonzero
        have positive := scale_positive nu
        unfold scale at positive ⊢
        linarith
      · simp only [weight, if_neg zero, inv_inv]
        have paid := NativeUnheatedQuarticKernel.decay_coercivity (nu := nu) a b c d
        unfold integerWaveViscousMultiplier at paid
        unfold scale
        nlinarith
    have positive : 0 < scale nu * (weight (a.1+b.1+c.1+d.1))⁻¹ := mul_pos (scale_positive nu) (inv_pos.mpr (weight_pos _))
    simpa only [one_div, mul_inv_rev, inv_inv, mul_comm] using one_div_le_one_div_of_le positive lower
  · push Not at nonzero
    obtain ⟨first,second,third,last⟩ := nonzero
    have zero : sumRate nu a b c d = 0 := by
      simp [sumRate, first, second, third, last, integerWaveViscousMultiplier, integerWaveNormSq]
    rw [zero, inv_zero]
    exact mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (weight_pos _).le

theorem frequency (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    (slots slot wave i j outside l m index 0).1+(slots slot wave i j outside l m index 1).1+
      (slots slot wave i j outside l m index 2).1+(slots slot wave i j outside l m index 3).1 = wave := by
  fin_cases slot
  · exact NativeUnheatedQuarticRows.frequency wave index.1 index.2
  · exact NativeUnheatedQuarticMiddle.frequency wave index.1 index.2
  · exact NativeUnheatedQuarticOuterRows.frequency wave index.1 index.2

def rate (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) : ℝ :=
  sumRate nu (slots slot wave i j outside l m index 0) (slots slot wave i j outside l m index 1)
    (slots slot wave i j outside l m index 2) (slots slot wave i j outside l m index 3)

theorem rate_nonnegative (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    0 ≤ rate nu slot wave i j outside l m index := NativeUnheatedQuarticKernel.rate_nonnegative _ _ _ _

theorem rate_inverse_bound (nu : Viscosity) (slot : Fin 3) (wave : IntegerWavevector) (i j outside l m : Coordinate) (index : Index) :
    (rate nu slot wave i j outside l m index)⁻¹ ≤ (scale nu)⁻¹*weight wave := by
  simpa only [rate, frequency] using inverse_bound (nu := nu) (slots slot wave i j outside l m index 0)
    (slots slot wave i j outside l m index 1) (slots slot wave i j outside l m index 2) (slots slot wave i j outside l m index 3)

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (wave : IntegerWavevector)
    (i j response outside l m : Coordinate) (index : Index) (time : ℝ) :
    primitiveTerm seed slot wave i j response outside l m index time =
      (rate nu slot wave i j outside l m index)⁻¹ • term seed slot wave i j response outside l m index time := by
  rw [term_original]
  simp only [primitiveTerm, NativeUnheatedQuarticNormalForm.primitive, NativeUnheatedQuarticKernel.normalizer, smul_mul_assoc]
  rfl

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (slot : Fin 3) (wave : IntegerWavevector) (i j response outside l m : Coordinate) :
    Summable (fun index => ‖primitiveTerm seed slot wave i j response outside l m index time‖) := by
  apply ((NativeUnheatedQuarticAllSlots.absolute_summable seed time nonnegative regular slot wave i j response outside l m).mul_left
    ((scale nu)⁻¹*weight wave)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro index
  rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot wave i j outside l m index))]
  exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot wave i j outside l m index) (norm_nonneg _)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ := (scale nu)⁻¹ * NativeUnheatedQuarticSource.bound seed

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed :=
  mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (NativeUnheatedQuarticSource.bound_nonnegative seed)

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) (slot : Fin 3) (wave : IntegerWavevector) (i j response outside l m : Coordinate) :
    (∑' index, ‖primitiveTerm seed slot wave i j response outside l m index time‖) ≤ bound seed*mass seed time*weight wave := by
  have compare := (absolute_summable seed time nonnegative regular slot wave i j response outside l m).tsum_le_tsum
    (fun index => by
      rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot wave i j outside l m index))]
      exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot wave i j outside l m index) (norm_nonneg _))
    ((NativeUnheatedQuarticAllSlots.absolute_summable seed time nonnegative regular slot wave i j response outside l m).mul_left ((scale nu)⁻¹*weight wave))
  rw [tsum_mul_left] at compare
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedQuarticAllSlots.absolute_bound seed time nonnegative regular slot wave i j response outside l m)
    (mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (weight_pos wave).le)
  exact compare.trans (paid.trans_eq (by unfold bound; ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticPrimitiveKernel
