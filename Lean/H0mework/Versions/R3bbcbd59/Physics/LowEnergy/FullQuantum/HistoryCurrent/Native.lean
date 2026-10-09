import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryCurrent.Kernel
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.SpatialResponse.Current

/-! The original primitive current reads both varied histories with its native vertex, volume, and independent dual. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
open FullSpace GaugeGreen ScalarGreen GaugeHistory HistoryVariation PerturbedGreen SpatialResponse YangMills.FullPairing
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
noncomputable section
variable (gauge direction : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (continuousDirection : Continuous direction)
    (coupling : ℝ) (scalar scalarDirection : ℝ → ScalarProfile)
    (continuousScalar : Continuous scalar) (continuousScalarDirection : Continuous scalarDirection)
local notation "U" => familyOperator gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "V" => dualFamily gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "B" => returnedReader gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
local notation "K" => relativeResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
  continuousScalar continuousScalarDirection
attribute [local irreducible] familyOperator fullOperator dualFamily

def complexCurrent (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time epsilon : ℝ) : ℂ :=
  volumeWeight * inner ℂ (V epsilon time dual) (variation probe scalarProbe (U epsilon 0 time initial))

def physicalCurrent (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time epsilon : ℝ) : ℝ :=
  (complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe dual initial time epsilon).re

def currentResponse (probe : GaugeProfile) (scalarProbe : ScalarProfile) (time : ℝ) : SpatialOperators :=
  let reader := B (inversePrincipal 0 * variation probe scalarProbe) 0 time
  principal 0 * (reader * K time-K time * reader)

theorem complexCurrent_operator (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time epsilon : ℝ) :
    complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time epsilon=
      volumeWeight * bilinearRead dual initial (principal 0 * B (inversePrincipal 0 * variation probe scalarProbe) epsilon time) := by
  rw [complexCurrent,dualFamily_read]
  rfl

theorem complexCurrent_derivative (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time : ℝ) :
    HasDerivAt (complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time)
      (volumeWeight * bilinearRead dual initial
        (currentResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
          continuousScalar continuousScalarDirection probe scalarProbe time)) 0 := by
  have twice := (returnedReader_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection (inversePrincipal 0 * variation probe scalarProbe) time).const_mul (principal 0)
  have read := ((bilinearRead dual initial).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 twice
  have weighted := read.const_mul volumeWeight
  change HasDerivAt (fun epsilon => complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
    continuousScalar continuousScalarDirection probe scalarProbe dual initial time epsilon) _ 0
  simpa only [complexCurrent_operator,currentResponse,ContinuousLinearMap.coe_restrictScalars',Function.comp_def] using! weighted

theorem physicalCurrent_derivative (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time : ℝ) :
    HasDerivAt (physicalCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time)
      ((volumeWeight * bilinearRead dual initial
        (currentResponse gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
          continuousScalar continuousScalarDirection probe scalarProbe time)).re) 0 := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (complexCurrent_derivative gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time)

theorem complexCurrent_native (probe : GaugeProfile) (scalarProbe : ScalarProfile) (dual initial : FullMatterL2)
    (time epsilon : ℝ) :
    complexCurrent gauge direction continuousGauge continuousDirection coupling scalar scalarDirection
      continuousScalar continuousScalarDirection probe scalarProbe dual initial time epsilon=
      volumeWeight * ∫ x, inner ℂ (V epsilon time dual x)
        (operator (PerturbedGreen.insertion actual (gaugeField probe) (fun _ => 0) (PerturbedGreen.spatialPoint x))
          (U epsilon 0 time initial x)+
        operator (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarProbe x)))
          (U epsilon 0 time initial x)) := by
  unfold complexCurrent
  congr 1
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [native_vertex_ae probe scalarProbe (U epsilon 0 time initial)] with x read
  rw [read]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryCurrent
