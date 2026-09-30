import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Full

/-! Pairwise nilpotence identifies the generated global development with every solution of its equation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen
noncomputable section

theorem triangularCurve_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (B : ℝ → E →L[ℂ] E) (continuousB : ∀ v, Continuous (fun t => B t v))
    (nilpotent : ∀ s t v, B s (B t v)=0) (start : ℝ) (initial : E) (curve : ℝ → E)
    (starts : curve start=initial) (evolves : ∀ t, HasDerivAt curve (B t (curve t)) t) :
    curve=triangularCurve B start initial := by
  have imageDerivative (s t : ℝ) : HasDerivAt (fun r => B s (curve r)) 0 t := by
    have generated := ((B s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (evolves t)
    simpa only [ContinuousLinearMap.coe_restrictScalars',Function.comp_def,nilpotent] using! generated
  have image (s t : ℝ) : B s (curve t)=B s initial := by
    have constant := is_const_of_deriv_eq_zero
      (fun r => (imageDerivative s r).differentiableAt) (fun r => (imageDerivative s r).deriv) t start
    simpa only [starts] using constant
  have fixedEquation (t : ℝ) : HasDerivAt curve (B t initial) t := by
    simpa only [image] using evolves t
  have difference (t : ℝ) : HasDerivAt (fun r => curve r-triangularCurve B start initial r) 0 t := by
    have generated := (fixedEquation t).sub ((insertionIntegral_derivative B continuousB start t initial).const_add initial)
    simpa only [triangularCurve,sub_self] using! generated
  funext t
  have constant := is_const_of_deriv_eq_zero (fun r => (difference r).differentiableAt)
    (fun r => (difference r).deriv) t start
  simpa only [starts,triangularCurve_starts,sub_self,sub_eq_zero] using constant

theorem full_interaction_unique (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start : ℝ) (initial : FullMatterL2) (curve : ℝ → FullMatterL2)
    (starts : curve start=initial)
    (evolves : ∀ t, HasDerivAt (fun r => gaugeUnitary gauge continuousGauge epsilon r 0 (curve r))
      (gaugeUnitary gauge continuousGauge epsilon t 0 (scalarDriftMap (scalar t) (curve t))) t) :
    curve=fun t => fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial := by
  have transformed (t : ℝ) : HasDerivAt (fun r => gaugeUnitary gauge continuousGauge epsilon r 0 (curve r))
      (scalarInteraction gauge continuousGauge epsilon scalar t
        (gaugeUnitary gauge continuousGauge epsilon t 0 (curve t))) t := by
    simpa only [scalarInteraction_apply,gaugeUnitary_inverse] using evolves t
  have generated := triangularCurve_unique (scalarInteraction gauge continuousGauge epsilon scalar)
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge epsilon scalar scalar) start
    (gaugeUnitary gauge continuousGauge epsilon start 0 initial)
    (fun r => gaugeUnitary gauge continuousGauge epsilon r 0 (curve r)) (by rw [starts]) transformed
  funext t
  have same := congrArg (gaugeUnitary gauge continuousGauge epsilon 0 t) (congrFun generated t)
  rw [gaugeUnitary_inverse] at same
  exact same

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
