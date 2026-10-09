import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Native
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryCurrent.Words

/-! The true primitive current derivative is an actual time integral of complete CAR words on one source-generated test span. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen SpatialResponse
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "B" => returnedReader gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "K" => relativeResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "J" => relativeInsertion gauge direction continuousGauge coupling scalar scalarDirection continuousScalar
attribute [local irreducible] fullOperator familyOperator dualFamily responseOperator

def currentCARKernel (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time r : ℝ) : ℂ :=
  commutatorCAR (principal 0) (B (inversePrincipal 0 * variation probe scalarProbe) 0 time) (J r) dual initial

theorem currentCARKernel_continuous (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (unit : ‖initial‖=1) (time : ℝ) :
    Continuous (currentCARKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time) := by
  let reader := B (inversePrincipal 0 * variation probe scalarProbe) 0 time
  have represented : currentCARKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time=
      fun r => inner ℂ dual (principal 0 (reader (J r initial)-J r (reader initial))) := by
    funext r
    exact commutatorCAR_read (principal 0) reader (J r) dual initial unit
  rw [represented]
  have first := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection initial
  have second := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection (reader initial)
  exact (innerSL ℂ dual).continuous.comp ((principal 0).continuous.comp ((reader.continuous.comp first).sub second))

theorem currentResponse_CAR (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (unit : ‖initial‖=1) (time : ℝ) :
    bilinearRead dual initial (currentResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe time)=
      ∫ r in (0 : ℝ)..time, currentCARKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection probe scalarProbe dual initial time r := by
  let reader := B (inversePrincipal 0 * variation probe scalarProbe) 0 time
  let raw (r : ℝ) := reader (J r initial)-J r (reader initial)
  have first := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection initial
  have second := relativeInsertion_continuous gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection (reader initial)
  have continuousRaw : Continuous raw := (reader.continuous.comp first).sub second
  have pull := ((innerSL ℂ dual).comp (principal 0)).intervalIntegral_comp_comm
    (continuousRaw.intervalIntegrable (μ := volume) 0 time)
  change (∫ r in (0 : ℝ)..time, inner ℂ dual (principal 0 (raw r)))=
    inner ℂ dual (principal 0 (∫ r in (0 : ℝ)..time, raw r)) at pull
  change inner ℂ dual (principal 0 ((reader * K time-K time * reader) initial))=_
  rw [commutator_integral]
  change inner ℂ dual (principal 0 (∫ r in (0 : ℝ)..time, raw r))=_
  rw [← pull]
  apply intervalIntegral.integral_congr
  intro r _
  exact (commutatorCAR_read (principal 0) reader (J r) dual initial unit).symm

theorem physicalCurrent_CAR (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (unit : ‖initial‖=1) (time : ℝ) :
    HasDerivAt (physicalCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time)
      ((volumeWeight * ∫ r in (0 : ℝ)..time, currentCARKernel gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
        continuousScalar continuousScalarDirection probe scalarProbe dual initial time r).re) 0 := by
  have differentiated := physicalCurrent_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe dual initial time
  rw [currentResponse_CAR gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe dual initial unit time] at differentiated
  exact differentiated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
