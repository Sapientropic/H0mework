import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Force

/-! The exact source history solves the same free-group Duhamel equation before frequency transformation. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen ScalarGreen GaugeHistory
noncomputable section
attribute [local irreducible] fullOperator
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

def sourceForce (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  localForce (gauge time) coupling (scalar time)
    (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial)

theorem sourceForce_continuous (initial : FullMatterL2) :
    Continuous (sourceForce gauge continuousGauge coupling scalar continuousScalar initial) :=
  (HistoryLaplace.localForce_continuous gauge continuousGauge coupling scalar continuousScalar).clm_apply
    (fullOperator_continuous gauge continuousGauge coupling scalar continuousScalar 0 initial)

def sourceInteraction (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  spatialFree (-time) (sourceForce gauge continuousGauge coupling scalar continuousScalar initial time)

theorem sourceInteraction_continuous (initial : FullMatterL2) :
    Continuous (sourceInteraction gauge continuousGauge coupling scalar continuousScalar initial) := by
  have composed := spatialFree_joint.comp
    (continuous_id.neg.prodMk (sourceForce_continuous gauge continuousGauge coupling scalar continuousScalar initial))
  simpa only [sourceInteraction,Function.comp_def,Pi.neg_apply,id_eq] using! composed

theorem sourceInteraction_integral (initial : FullMatterL2) (time : ℝ) :
    spatialFree (-time) (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial)=
      initial+∫ r in (0 : ℝ)..time, sourceInteraction gauge continuousGauge coupling scalar continuousScalar initial r := by
  have derivative (t : ℝ) : HasDerivAt (fun r => spatialFree (-r)
      (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 r initial))
      (sourceInteraction gauge continuousGauge coupling scalar continuousScalar initial t) t :=
    full_freeInteraction_equation gauge continuousGauge coupling scalar continuousScalar 0 t initial
  have integrated := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => derivative t)
    ((sourceInteraction_continuous gauge continuousGauge coupling scalar continuousScalar initial).intervalIntegrable (μ := volume) 0 time)
  rw [neg_zero,fullOperator_starts,spatialFree_zero] at integrated
  exact (eq_add_of_sub_eq integrated.symm).trans (add_comm _ _)

theorem full_source_mild (initial : FullMatterL2) (time : ℝ) :
    fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial=
      spatialFree time initial+∫ r in (0 : ℝ)..time, spatialFree (time-r)
        (sourceForce gauge continuousGauge coupling scalar continuousScalar initial r) := by
  have integrated := congrArg (spatialFree time)
    (sourceInteraction_integral gauge continuousGauge coupling scalar continuousScalar initial time)
  rw [← spatialFree_add,add_neg_cancel,spatialFree_zero,map_add] at integrated
  have transported := (spatialFree time).intervalIntegral_comp_comm
    ((sourceInteraction_continuous gauge continuousGauge coupling scalar continuousScalar initial).intervalIntegrable (μ := volume) 0 time)
  rw [← transported] at integrated
  convert! integrated using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  simp only [sourceInteraction,← spatialFree_add,sub_eq_add_neg]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
