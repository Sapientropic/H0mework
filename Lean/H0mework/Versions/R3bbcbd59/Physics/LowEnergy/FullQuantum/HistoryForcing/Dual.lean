import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Kernel

/-! The original independent dual reads the actual forcing of its conserved C0 pairing. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (source : ℝ → FullMatterL2) (continuousSource : Continuous source)
attribute [local irreducible] gaugeUnitary fullOperator sourceDevelopment

include continuousSource in
theorem source_return_integral (start time : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge coupling scalar continuousScalar time start
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)=
      initial+∫ r in start..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r start
        (inversePrincipal 0 (source r)) := by
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => source_return_derivative gauge continuousGauge coupling scalar continuousScalar source continuousSource start t initial)
    ((source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource start).intervalIntegrable
      (μ := volume) start time)
  rw [sourceDevelopment_starts,fullOperator_starts] at integrated
  exact (eq_add_of_sub_eq integrated.symm).trans (add_comm _ _)

theorem originalDual_source_read (start time : ℝ) (dual input : FullMatterL2) :
    inner ℂ (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start time dual) input=
      inner ℂ dual (principal 0
        (fullOperator gauge continuousGauge coupling scalar continuousScalar time start (inversePrincipal 0 input))) := by
  simp only [originalDualOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left]

include continuousSource in
theorem original_pair_source_derivative (start time : ℝ) (initial dual : FullMatterL2) :
    HasDerivAt (fun t => inner ℂ
      (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start t dual)
      (principal 0 (sourceDevelopment gauge continuousGauge coupling scalar source start initial t)))
      (inner ℂ (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start time dual)
        (source time)) time := by
  have returned := source_return_derivative gauge continuousGauge coupling scalar continuousScalar
    source continuousSource start time initial
  let read := (innerSL ℂ dual).comp (principal 0)
  have generated := read.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt time returned
  simpa only [read,ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    Function.comp_def,originalDual_source_read,inversePrincipal_left] using! generated

include continuousSource in
theorem original_pair_source_integral (start time : ℝ) (initial dual : FullMatterL2) :
    inner ℂ (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start time dual)
      (principal 0 (sourceDevelopment gauge continuousGauge coupling scalar source start initial time))=
      inner ℂ dual (principal 0 initial)+
      ∫ r in start..time, inner ℂ (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start r dual)
        (source r) := by
  have continuousRead : Continuous (fun t => inner ℂ
      (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start t dual) (source t)) := by
    have composed := (innerSL ℂ dual).continuous.comp ((principal 0).continuous.comp
      (source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource start))
    simpa only [Function.comp_def,originalDual_source_read] using! composed
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => original_pair_source_derivative gauge continuousGauge coupling scalar continuousScalar source continuousSource start t initial dual)
    (continuousRead.intervalIntegrable (μ := volume) start time)
  rw [sourceDevelopment_starts] at integrated
  have initialPair : inner ℂ (originalDualOperator gauge continuousGauge coupling scalar continuousScalar start start dual)
      (principal 0 initial)=inner ℂ dual (principal 0 initial) := by
    rw [originalDual_source_read,inversePrincipal_left,fullOperator_starts]
  rw [initialPair] at integrated
  exact (eq_add_of_sub_eq integrated.symm).trans (add_comm _ _)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
