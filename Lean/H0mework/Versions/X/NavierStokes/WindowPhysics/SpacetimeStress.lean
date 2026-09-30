import H0mework.Versions.X.NavierStokes.WindowPhysics.SpacetimeFourier
import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatSpatialSynthesis
import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatEvolution

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal Topology ContDiff

namespace SaturationMonoid.NavierStokes.NativeWindowSpacetimeStress

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFullOrderAction NativeFullOrderSynthesis NativeWindowSpacetimeFourier

noncomputable section

variable {nu : Viscosity}

def read (wave : IntegerWavevector) (entry : Coordinate × Coordinate) : NativeCompleteStressAction.FullSpace →L[ℝ] ℂ :=
  (NativeCompleteStressCarrier.readCLM wave entry.1 entry.2).comp
    (WithLp.sndL 2 ℝ
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointState
      NativeCompleteStressCarrier.Space)

def coefficient (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (entry : Coordinate × Coordinate)
    (order : ℕ) (wave : IntegerWavevector) (time : ℝ) : ℂ :=
  NativeCompleteStressCarrier.read (NativeWindowHeatEvolution.jet seed lag order time).snd wave entry.1 entry.2

theorem coefficient_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (entry : Coordinate × Coordinate)
    (order : ℕ) (wave : IntegerWavevector) (time : ℝ) :
    HasDerivAt (coefficient seed lag entry order wave) (coefficient seed lag entry (order + 1) wave time) time :=
  (read wave entry).hasFDerivAt.comp_hasDerivAt time (NativeWindowHeatEvolution.jet_hasDerivAt seed lag order time)

def coefficientBudget (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (rank order : ℕ) : ℝ :=
  NativeHeatSpatialMultiplier.budget nu lag (order + 6) * NativeForwardWindowJets.budget seed rank

theorem coefficient_decay (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (entry : Coordinate × Coordinate) (rank order : ℕ) (wave : IntegerWavevector) (time : ℝ) :
    frequencySize wave ^ order * ‖coefficient seed lag entry rank wave time‖ ≤
      coefficientBudget seed lag rank order * decay wave := by
  have nonnegative := (norm_nonneg (NativeForwardWindowJets.jet seed rank time)).trans
    (NativeForwardWindowJets.jet_bound seed rank time)
  have rowBound : ‖(NativeForwardWindowJets.jet seed rank time).snd wave entry‖ ≤
      NativeForwardWindowJets.budget seed rank :=
    (PiLp.norm_apply_le _ entry).trans
      ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) _ wave).trans
        ((WithLp.norm_snd_le _ _).trans (NativeForwardWindowJets.jet_bound seed rank time)))
  have rawBound : ‖NativeCompleteStressCarrier.read (NativeForwardWindowJets.jet seed rank time).snd wave entry.1 entry.2‖ ≤
      frequencySize wave ^ 2 * NativeForwardWindowJets.budget seed rank := by
    change ‖(NativeCompleteStressCarrier.weight wave)⁻¹ • (NativeForwardWindowJets.jet seed rank time).snd wave entry‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (NativeCompleteStressCarrier.weight_pos wave).le)]
    exact mul_le_mul (NativeHeatSpatialSynthesis.stress_weight_inverse_le wave) rowBound (norm_nonneg _) (sq_nonneg _)
  change frequencySize wave ^ order * ‖NativeCompleteStressCarrier.read
    (NativeCompleteHeatTransport.tensorHeat nu lag (NativeForwardWindowJets.jet seed rank time).snd) wave entry.1 entry.2‖ ≤ _
  rw [NativeCompleteHeatTransport.tensorHeat_read]
  simpa only [Pi.smul_apply, Nat.add_assoc, coefficientBudget] using
    heated_coefficient_bound nu lag positive 2 order wave
      (NativeCompleteStressCarrier.read (NativeForwardWindowJets.jet seed rank time).snd wave entry.1 entry.2)
      (NativeForwardWindowJets.budget seed rank) nonnegative rawBound

theorem scalar_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (entry : Coordinate × Coordinate) : ContDiff ℝ ∞ (scalarField (coefficient seed lag entry)) :=
  scalarField_smooth _ (coefficient_hasDerivAt seed lag entry) (coefficientBudget seed lag)
    (coefficient_decay seed lag positive entry)

def jointTensor (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) :
    EuclideanSpace ℂ (Coordinate × Coordinate) :=
  WithLp.toLp 2 fun entry => scalarField (coefficient seed lag entry) pair

theorem jointTensor_source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime)
    (entry : Coordinate × Coordinate) :
    jointTensor seed lag pair entry = ∑' wave,
      NativeCompleteStressCarrier.read (NativeWindowHeatEvolution.source seed lag pair.1).snd wave entry.1 entry.2 *
        monomial wave pair.2 := by
  change (∑' wave, coefficient seed lag entry 0 wave pair.1 * monomial wave pair.2) = _
  unfold coefficient
  rw [NativeWindowHeatEvolution.jet_zero]

theorem jointTensor_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag) :
    ContDiff ℝ ∞ (jointTensor seed lag) := by
  apply PiLp.contDiff_toLp.comp
  exact contDiff_pi.mpr (fun entry => scalar_smooth seed lag positive entry)

theorem jointTensor_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (jointTensor seed lag)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (jointTensor seed lag)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (jointTensor_smooth seed lag positive) order exponent compact

def jointField (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime) :
    EuclideanSpace ℝ (Coordinate × Coordinate) := WithLp.toLp 2 fun entry => (jointTensor seed lag pair entry).re

theorem jointField_source (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (pair : Spacetime)
    (entry : Coordinate × Coordinate) :
    jointField seed lag pair entry = (∑' wave,
      NativeCompleteStressCarrier.read (NativeWindowHeatEvolution.source seed lag pair.1).snd wave entry.1 entry.2 *
        monomial wave pair.2).re := by
  change (jointTensor seed lag pair entry).re = _
  rw [jointTensor_source]

theorem jointField_smooth (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag) :
    ContDiff ℝ ∞ (jointField seed lag) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro entry
  exact Complex.reCLM.contDiff.comp (scalar_smooth seed lag positive entry)

theorem jointField_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (positive : 0 < lag)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧ MemLp (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (jointField seed lag)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  compact_all_order_Lp _ (jointField_smooth seed lag positive) order exponent compact

end
end SaturationMonoid.NavierStokes.NativeWindowSpacetimeStress
