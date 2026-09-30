import H0mework.Versions.X.NavierStokes.SourceHeat.PairingAverage
import H0mework.Versions.X.NavierStokes.WindowPhysics.HeatEvolution
import H0mework.Versions.X.NavierStokes.StressRegeneration.StressEnergy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewEnergyContent

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeStressPairingCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier
open NativeWindowHeatEvolution NativeWordStressEnergy

noncomputable section

variable {nu : Viscosity}

def total (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  kineticRead (source seed lag time).snd / 2

def resolved (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  ‖(source seed lag time).fst‖ ^ 2 / 2

def unresolved (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) : ℝ :=
  kineticRead (NativeCompleteHeatTransport.residualValue (source seed lag time)) / 2

theorem total_gram (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    total seed lag time = (∑ coordinate : Coordinate,
      ‖component (NativeHeatPairingAverage.sourceData seed lag time) (0, coordinate)‖ ^ 2) / 2 := by
  rw [component_energy, NativeHeatPairingAverage.source_stress]
  exact congrArg (fun value : ℝ => value / 2) (kineticRead_apply _)

theorem residual_gram (data : Data) :
    -(∑ coordinate : Coordinate,
      (data.stress 0 coordinate coordinate - NativeStressSource.quadraticFlux (wholeVelocity data.mean) 0 coordinate coordinate).re) =
    ∑ coordinate : Coordinate, ‖NativePositiveKernelCarrier.vector (kernel data) (0, coordinate)‖ ^ 2 := by
  simp only [NativePositiveKernelCarrier.vector_norm_sq]
  change _ = ∑ coordinate : Coordinate, (-(data.stress (0 - 0) coordinate coordinate -
    NativeStressSource.quadraticFlux (wholeVelocity data.mean) (0 - 0) coordinate coordinate)).re
  simp only [sub_self, Complex.neg_re, Finset.sum_neg_distrib]

theorem unresolved_gram (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    unresolved seed lag time = (∑ coordinate : Coordinate,
      ‖NativePositiveKernelCarrier.vector (kernel (NativeHeatPairingAverage.sourceData seed lag time))
        (0, coordinate)‖ ^ 2) / 2 := by
  rw [unresolved, kineticRead_apply, NativeHeatPairingAverage.residual_read]
  have actual := residual_gram (NativeHeatPairingAverage.sourceData seed lag time)
  rw [NativeHeatPairingAverage.source_mean, NativeHeatPairingAverage.source_stress] at actual
  exact congrArg (fun value : ℝ => value / 2) actual

theorem unresolved_nonnegative (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    0 ≤ unresolved seed lag time := by
  rw [unresolved_gram]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)

theorem source_reality (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    WholeRestartVelocityEndpointReality (source seed lag time).fst := by
  have actual := (NativeHeatPairingAverage.sourceData seed lag time).reality
  rwa [NativeHeatPairingAverage.source_mean] at actual

theorem split (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    total seed lag time = resolved seed lag time + unresolved seed lag time := by
  have trace := NativeCofinalFluxPairing.bilinearFlux_zero_trace (source seed lag time).fst
    (source_reality seed lag time)
  simp only [NativeCofinalFluxPairing.bilinearFlux_diagonal] at trace
  rw [total, resolved, unresolved, kineticRead_apply, kineticRead_apply, NativeHeatPairingAverage.residual_read]
  change -(∑ coordinate : Coordinate, (NativeCompleteStressCarrier.read (source seed lag time).snd 0 coordinate coordinate).re) / 2 =
    ‖(source seed lag time).fst‖ ^ 2 / 2 +
      -(∑ coordinate : Coordinate, (NativeCompleteStressCarrier.read (source seed lag time).snd 0 coordinate coordinate -
        NativeStressSource.quadraticFlux (wholeVelocity (source seed lag time).fst) 0 coordinate coordinate).re) / 2
  simp only [Complex.sub_re, Finset.sum_sub_distrib, trace]
  ring

theorem resolved_le_total (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    resolved seed lag time ≤ total seed lag time := by
  rw [split]
  exact le_add_of_nonneg_right (unresolved_nonnegative seed lag time)

theorem resolved_physical (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    resolved seed lag time = ‖NativePhysicalFourier.realField (wholeVelocity (source seed lag time).fst)‖ ^ 2 / 2 := by
  rw [NativePhysicalFourier.realField_norm_sq _ (wholeVelocity_reality _ (source_reality seed lag time)), wholeVelocity_mass]
  rfl

theorem physical_energy_le_total (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    ‖NativePhysicalFourier.realField (wholeVelocity (source seed lag time).fst)‖ ^ 2 / 2 ≤ total seed lag time := by
  rw [← resolved_physical]
  exact resolved_le_total seed lag time


theorem total_nonnegative (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    0 ≤ total seed lag time := by
  rw [total_gram]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)

theorem total_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    total seed lag time ≤ ‖kineticRead‖ * NativeUnifiedCompleteSource.budget seed / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply (le_abs_self _).trans (kineticRead.le_opNorm _ |>.trans _)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (WithLp.norm_snd_le _ (source seed lag time)).trans
    ((NativeCompleteHeatTransport.fullHeat_bound nu lag _).trans
      (NativeForwardWindowSource.source_bound seed time))

theorem physical_energy_bound (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    ‖NativePhysicalFourier.realField (wholeVelocity (source seed lag time).fst)‖ ^ 2 / 2 ≤
      ‖kineticRead‖ * NativeUnifiedCompleteSource.budget seed / 2 :=
  (physical_energy_le_total seed lag time).trans (total_bound seed lag time)

end
end SaturationMonoid.NavierStokes.NativeViewEnergyContent
