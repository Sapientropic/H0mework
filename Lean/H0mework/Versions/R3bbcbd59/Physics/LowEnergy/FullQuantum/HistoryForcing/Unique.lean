import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Complete

/-! Source uniqueness, zero-source recovery, and interval causality of the generated original field. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section

theorem inputPrimitive_agrees {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (first second : ℝ → E) (start time : ℝ) (initial : E)
    (same : EqOn first second (uIcc start time)) :
    inputPrimitive first start initial time=inputPrimitive second start initial time := by
  unfold inputPrimitive
  rw [intervalIntegral.integral_congr same]

theorem forcedCurve_agrees {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : ℝ → E →L[ℂ] E) (first second : ℝ → E) (start time : ℝ) (initial : E)
    (same : EqOn first second (uIcc start time)) :
    forcedCurve B first start initial time=forcedCurve B second start initial time := by
  unfold forcedCurve
  rw [inputPrimitive_agrees first second start time initial same]
  congr 1
  apply intervalIntegral.integral_congr
  intro r inside
  change B r (inputPrimitive first start initial r)=B r (inputPrimitive second start initial r)
  rw [inputPrimitive_agrees first second start r initial
    (fun s hs => same ((uIcc_subset_uIcc_left inside) hs))]

variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
attribute [local irreducible] gaugeUnitary fullOperator

include continuousScalar in
theorem sourceDevelopment_unique (source : ℝ → FullMatterL2) (continuousSource : Continuous source)
    (start : ℝ) (initial : FullMatterL2) (curve : ℝ → FullMatterL2) (starts : curve start=initial)
    (evolves : ∀ t, HasDerivAt (fun r => gaugeUnitary gauge continuousGauge coupling r 0 (curve r))
      (gaugeUnitary gauge continuousGauge coupling t 0
        (scalarDriftMap (scalar t) (curve t)+inversePrincipal 0 (source t))) t) :
    curve=sourceDevelopment gauge continuousGauge coupling scalar source start initial := by
  have transformed (t : ℝ) : HasDerivAt (fun r => gaugeUnitary gauge continuousGauge coupling r 0 (curve r))
      (scalarInteraction gauge continuousGauge coupling scalar t
        (gaugeUnitary gauge continuousGauge coupling t 0 (curve t))+
        sourceInteraction gauge continuousGauge coupling source t) t := by
    simpa only [scalarInteraction_apply,gaugeUnitary_inverse,sourceInteraction,map_add] using! evolves t
  have determined := forcedCurve_unique (scalarInteraction gauge continuousGauge coupling scalar)
    (scalarInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge coupling scalar scalar)
    (sourceInteraction gauge continuousGauge coupling source)
    (sourceInteraction_continuous gauge continuousGauge coupling source continuousSource) start
    (gaugeUnitary gauge continuousGauge coupling start 0 initial)
    (fun t => gaugeUnitary gauge continuousGauge coupling t 0 (curve t)) (by rw [starts]) transformed
  funext t
  have same := congrArg (gaugeUnitary gauge continuousGauge coupling 0 t) (congrFun determined t)
  rw [gaugeUnitary_inverse] at same
  exact same

theorem sourceDevelopment_zero_source (start time : ℝ) (initial : FullMatterL2) :
    sourceDevelopment gauge continuousGauge coupling scalar (fun _ => 0) start initial time=
      fullOperator gauge continuousGauge coupling scalar continuousScalar start time initial := by
  simp only [fullOperator_apply,sourceDevelopment,forcedCurve,inputPrimitive,sourceInteraction,
    map_zero,intervalIntegral.integral_zero,add_zero,triangularCurve,insertionIntegral]

theorem sourceDevelopment_causal (first second : ℝ → FullMatterL2) (start time : ℝ) (initial : FullMatterL2)
    (same : EqOn first second (uIcc start time)) :
    sourceDevelopment gauge continuousGauge coupling scalar first start initial time=
      sourceDevelopment gauge continuousGauge coupling scalar second start initial time := by
  unfold sourceDevelopment
  apply congrArg (gaugeUnitary gauge continuousGauge coupling 0 time)
  apply forcedCurve_agrees
  intro t inside
  change gaugeUnitary gauge continuousGauge coupling t 0 (inversePrincipal 0 (first t))=
    gaugeUnitary gauge continuousGauge coupling t 0 (inversePrincipal 0 (second t))
  rw [same inside]

include continuousScalar in
theorem sourceDevelopment_past_zero (source : ℝ → FullMatterL2) (start time : ℝ)
    (pastSource : ∀ t, t ≤ start → source t=0) (past : time ≤ start) :
    sourceDevelopment gauge continuousGauge coupling scalar source start 0 time=0 := by
  have same : EqOn source (fun _ => 0) (uIcc start time) := by
    intro t inside
    rw [uIcc_of_ge past] at inside
    exact pastSource t inside.2
  rw [sourceDevelopment_causal gauge continuousGauge coupling scalar source (fun _ => 0) start time 0 same,
    sourceDevelopment_zero_source gauge continuousGauge coupling scalar continuousScalar,map_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
