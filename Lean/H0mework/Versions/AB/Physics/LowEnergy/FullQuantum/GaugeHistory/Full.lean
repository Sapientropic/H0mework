import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Scalar
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Nilpotent

/-! Gauge and scalar histories generate one exact complete spatial matter development. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section

def scalarIntegralOperator (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) : SpatialOperators :=
  insertionOperator (scalarInteraction gauge continuousGauge epsilon scalar)
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
    (scalarInteraction_bound gauge continuousGauge epsilon scalar) start time

def fullOperator (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) : SpatialOperators :=
  (gaugeUnitary gauge continuousGauge epsilon 0 time).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((1+scalarIntegralOperator gauge continuousGauge epsilon scalar continuousScalar start time).comp
      (gaugeUnitary gauge continuousGauge epsilon start 0).toContinuousLinearEquiv.toContinuousLinearMap)

theorem fullOperator_apply (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial=
      gaugeUnitary gauge continuousGauge epsilon 0 time
        (triangularCurve (scalarInteraction gauge continuousGauge epsilon scalar) start
          (gaugeUnitary gauge continuousGauge epsilon start 0 initial) time) := rfl

theorem fullOperator_starts (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge epsilon scalar continuousScalar start start initial=initial := by
  rw [fullOperator_apply,triangularCurve_starts,gaugeUnitary_inverse]

theorem fullOperator_inverse (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge epsilon scalar continuousScalar time start
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)=initial := by
  simp only [fullOperator_apply,gaugeUnitary_inverse]
  rw [triangularCurve_inverse _
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge epsilon scalar scalar),gaugeUnitary_inverse]

theorem fullOperator_interaction (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary gauge continuousGauge epsilon time 0
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)=
        triangularCurve (scalarInteraction gauge continuousGauge epsilon scalar) start
          (gaugeUnitary gauge continuousGauge epsilon start 0 initial) time := by
  rw [fullOperator_apply,gaugeUnitary_inverse]

theorem fullOperator_equation (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => gaugeUnitary gauge continuousGauge epsilon t 0
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial))
      (gaugeUnitary gauge continuousGauge epsilon time 0
        (scalarDriftMap (scalar time)
          (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial))) time := by
  simp only [fullOperator_interaction]
  have generated := triangularCurve_equation (scalarInteraction gauge continuousGauge epsilon scalar)
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge epsilon scalar scalar) start time
    (gaugeUnitary gauge continuousGauge epsilon start 0 initial)
  simpa only [scalarInteraction_apply,fullOperator_apply] using! generated

theorem fullOperator_bound (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    ‖fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial‖≤
      (1+|∫ r in start..time, ‖scalarDriftMap (scalar r)‖|)*‖initial‖ := by
  rw [fullOperator_apply,LinearIsometryEquiv.norm_map]
  have bound := triangularCurve_norm_le (scalarInteraction gauge continuousGauge epsilon scalar)
    (fun t => ‖scalarDriftMap (scalar t)‖) (scalarDriftMap.continuous.comp continuousScalar).norm
    (scalarInteraction_bound gauge continuousGauge epsilon scalar) start time
    (gaugeUnitary gauge continuousGauge epsilon start 0 initial)
  simpa only [LinearIsometryEquiv.norm_map] using bound

theorem fullOperator_compose (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start middle time : ℝ) (initial : FullMatterL2) :
    fullOperator gauge continuousGauge epsilon scalar continuousScalar middle time
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start middle initial)=
        fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial := by
  simp only [fullOperator_apply,gaugeUnitary_inverse]
  rw [triangularCurve_compose _
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge epsilon scalar scalar)]

def originalDualOperator (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) : SpatialOperators :=
  (inversePrincipal 0).adjoint.comp
    ((fullOperator gauge continuousGauge epsilon scalar continuousScalar time start).adjoint.comp (principal 0).adjoint)

theorem original_pair_preserved (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (dual field : FullMatterL2) :
    inner ℂ (originalDualOperator gauge continuousGauge epsilon scalar continuousScalar start time dual)
      (principal 0 (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time field))=
        inner ℂ dual (principal 0 field) := by
  simp only [originalDualOperator,ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,inversePrincipal_left,
    ContinuousLinearMap.adjoint_inner_left,fullOperator_inverse,ContinuousLinearMap.adjoint_inner_left]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
