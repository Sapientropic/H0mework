import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Return
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Unique

/-! The complete original propagator generates the same forced solution by its genuine retarded source integral. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (source : ℝ → FullMatterL2) (continuousSource : Continuous source)
attribute [local irreducible] gaugeUnitary fullOperator sourceDevelopment

include continuousSource in
theorem source_kernel_continuous (finish : ℝ) :
    Continuous (fun t => fullOperator gauge continuousGauge coupling scalar continuousScalar t finish
      (inversePrincipal 0 (source t))) := by
  let h := sourceInteraction gauge continuousGauge coupling source
  let A := scalarIntegralOperator gauge continuousGauge coupling scalar continuousScalar finish
  have continuousH : Continuous h := sourceInteraction_continuous gauge continuousGauge coupling source continuousSource
  have continuousA : Continuous A := insertionOperator_continuous
    (scalarInteraction gauge continuousGauge coupling scalar)
    (scalarInteraction_continuous gauge continuousGauge coupling scalar continuousScalar)
    (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
    (scalarInteraction_bound gauge continuousGauge coupling scalar) finish
  have reversed (t : ℝ) :
      fullOperator gauge continuousGauge coupling scalar continuousScalar t finish (inversePrincipal 0 (source t))=
        gaugeUnitary gauge continuousGauge coupling 0 finish (h t-A t (h t)) := by
    rw [fullOperator_apply]
    apply congrArg (gaugeUnitary gauge continuousGauge coupling 0 finish)
    change h t+(∫ r in t..finish, scalarInteraction gauge continuousGauge coupling scalar r (h t))=
      h t-(∫ r in finish..t, scalarInteraction gauge continuousGauge coupling scalar r (h t))
    rw [intervalIntegral.integral_symm]
    simp only [sub_eq_add_neg]
  have composed := (gaugeUnitary gauge continuousGauge coupling 0 finish).continuous.comp
    (continuousH.sub (continuousA.clm_apply continuousH))
  simpa only [reversed,Function.comp_def] using! composed

include continuousSource in
theorem sourceDevelopment_retarded (start time : ℝ) (initial : FullMatterL2) :
    sourceDevelopment gauge continuousGauge coupling scalar source start initial time=
      fullOperator gauge continuousGauge coupling scalar continuousScalar start time initial+
      ∫ r in start..time, fullOperator gauge continuousGauge coupling scalar continuousScalar r time
        (inversePrincipal 0 (source r)) := by
  let B := scalarInteraction gauge continuousGauge coupling scalar
  let h := sourceInteraction gauge continuousGauge coupling source
  let u := gaugeUnitary gauge continuousGauge coupling start 0 initial
  have continuousInput : Continuous (fun r => triangularCurve B r (h r) time) := by
    have composed := (gaugeUnitary gauge continuousGauge coupling time 0).continuous.comp
      (source_kernel_continuous gauge continuousGauge coupling scalar continuousScalar source continuousSource time)
    simpa only [fullOperator_apply,gaugeUnitary_inverse,Function.comp_def] using! composed
  have generated := congrArg (gaugeUnitary gauge continuousGauge coupling 0 time)
    (forcedCurve_retarded B (scalarInteraction_continuous gauge continuousGauge coupling scalar continuousScalar)
      (scalarInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
      (scalarInteraction_twice_zero gauge continuousGauge coupling scalar scalar)
      (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
      (scalarInteraction_bound gauge continuousGauge coupling scalar) h
      (sourceInteraction_continuous gauge continuousGauge coupling source continuousSource) start time u)
  have pull := (gaugeUnitary gauge continuousGauge coupling 0 time).toContinuousLinearEquiv.toContinuousLinearMap.intervalIntegral_comp_comm
    (continuousInput.intervalIntegrable (μ := volume) start time)
  change (∫ r in start..time, gaugeUnitary gauge continuousGauge coupling 0 time (triangularCurve B r (h r) time))=
    gaugeUnitary gauge continuousGauge coupling 0 time (∫ r in start..time, triangularCurve B r (h r) time) at pull
  rw [map_add] at generated
  erw [← pull] at generated
  simpa only [sourceDevelopment,fullOperator_apply] using! generated

include continuousSource in
theorem source_return_derivative (start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => fullOperator gauge continuousGauge coupling scalar continuousScalar t start
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial t))
      (fullOperator gauge continuousGauge coupling scalar continuousScalar time start
        (inversePrincipal 0 (source time))) time := by
  let B := scalarInteraction gauge continuousGauge coupling scalar
  let h := sourceInteraction gauge continuousGauge coupling source
  let u := gaugeUnitary gauge continuousGauge coupling start 0 initial
  have returned := forced_return_derivative B (scalarInteraction_continuous gauge continuousGauge coupling scalar continuousScalar)
    (scalarInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge coupling scalar scalar)
    (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
    (scalarInteraction_bound gauge continuousGauge coupling scalar) h
    (sourceInteraction_continuous gauge continuousGauge coupling source continuousSource) start time u
  have generated := (gaugeUnitary gauge continuousGauge coupling 0 start).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
    |>.hasFDerivAt.comp_hasDerivAt time returned
  simpa only [ContinuousLinearMap.coe_restrictScalars',fullOperator_apply,sourceDevelopment,gaugeUnitary_inverse,
    Function.comp_def] using! generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
