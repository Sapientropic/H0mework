import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Response

/-! The two-leg derivative is the genuine integral of the ordered insertion on the complete history. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "D" => responseOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "K" => relativeResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] fullOperator

def relativeInsertion (time : ℝ) : SpatialOperators :=
  fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 *
    localForce (direction time) coupling (scalarDirection time) *
    fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time

local notation "J" => relativeInsertion gauge direction continuousGauge coupling scalar scalarDirection continuousScalar

include continuousDirection continuousScalarDirection in
theorem relativeInsertion_continuous (initial : FullMatterL2) : Continuous (fun t => J t initial) := by
  have generated := insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection 0 0 initial
  change Continuous (fun t => fullOperator gauge continuousGauge coupling scalar continuousScalar t 0
    (localForce (direction t) coupling (scalarDirection t) (U 0 0 t initial))) at generated
  simpa only [relativeInsertion,mul_apply_eq_comp,familyOperator_zero] using! generated

theorem relativeResponse_integral (time : ℝ) (initial : FullMatterL2) :
    K time initial=∫ r in (0 : ℝ)..time, J r initial := by
  let integrand := insertionIntegrand gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection 0 time initial
  have integrable := (insertionIntegrand_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection 0 time initial).intervalIntegrable (μ := volume) 0 time
  have pull := (fullOperator gauge continuousGauge coupling scalar continuousScalar time 0).intervalIntegral_comp_comm integrable
  change (∫ r in (0 : ℝ)..time, fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 (integrand r))=
    fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 (∫ r in (0 : ℝ)..time, integrand r) at pull
  change U 0 time 0 (D time initial)=_
  rw [familyOperator_zero,responseOperator_apply]
  change fullOperator gauge continuousGauge coupling scalar continuousScalar time 0 (∫ r in (0 : ℝ)..time, integrand r)=_
  rw [← pull]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [integrand,insertionIntegrand,familyOperator_zero,relativeInsertion,mul_apply_eq_comp]
  rw [fullOperator_compose]

theorem commutator_integral (reader : SpatialOperators) (time : ℝ) (initial : FullMatterL2) :
    (reader * K time-K time * reader) initial=
      ∫ r in (0 : ℝ)..time, reader (J r initial)-J r (reader initial) := by
  have first := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection initial
  have second := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection (reader initial)
  have pull := reader.intervalIntegral_comp_comm (first.intervalIntegrable (μ := volume) 0 time)
  simp only [sub_apply,mul_apply_eq_comp,relativeResponse_integral]
  rw [← pull]
  simpa only [Function.comp_def] using! (intervalIntegral.integral_sub
    ((reader.continuous.comp first).intervalIntegrable (μ := volume) 0 time)
    (second.intervalIntegrable (μ := volume) 0 time)).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
