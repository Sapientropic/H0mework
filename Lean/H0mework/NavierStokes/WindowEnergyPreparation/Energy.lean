import H0mework.NavierStokes.WindowEnergyPreparation.Action
import H0mework.NavierStokes.WindowEnergyPreparation.Force

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowStressPreparationEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCompleteStressAction
open NativeWindowStressHeatTime (jet jet_zero jet_hasDerivAt)
open NativeWindowStressHeatBalance (sigma energy)
open NativeWindowStressHeatSource (physical heat heatWork)
open NativeWindowStressPreparationAction (nonlinearWindow correction)
open NativeWindowPreparationWrite (fraction inactive fraction_integrable)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {nu : Viscosity}

def nonlinearWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, inner ℝ (sigma seed F output input time)
    (physical (nonlinearWindow seed time F output input))

def forceWork (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∑ output : Coordinate, ∑ input : Coordinate, inner ℝ (sigma seed F output input time)
    (physical (correction seed time F output input))

theorem sigma_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) (output input : Coordinate) :
    HasDerivAt (sigma seed F output input)
      (physical (nonlinearWindow seed time F output input)+physical (heat seed time F output input)+
        physical (correction seed time F output input)) time := by
  have generated := (physical.hasFDerivAt.comp_hasDerivAt time
    (jet_hasDerivAt seed F output input 0 time)).neg
  have rate : -physical (jet seed F output input 1 time) =
      physical (nonlinearWindow seed time F output input)+physical (heat seed time F output input)+
        physical (correction seed time F output input) := by
    rw [← map_neg,NativeWindowStressPreparationAction.jet_generator seed time F closed,map_add,map_add]
  unfold sigma
  simpa only [Function.comp_def,Pi.neg_apply,jet_zero,rate] using! generated

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    HasDerivAt (energy seed F) (nonlinearWork seed time F+heatWork seed time F+forceWork seed time F) time := by
  have entry (output input : Coordinate) : HasDerivAt (fun actual => (1/2 : ℝ)*‖sigma seed F output input actual‖^2)
      (inner ℝ (sigma seed F output input time) (physical (nonlinearWindow seed time F output input))+
        inner ℝ (sigma seed F output input time) (physical (heat seed time F output input))+
        inner ℝ (sigma seed F output input time) (physical (correction seed time F output input))) time := by
    convert! ((sigma_hasDerivAt seed time F closed output input).norm_sq).const_mul (1/2 : ℝ) using 1
    rw [inner_add_right,inner_add_right]
    ring
  have sum := HasDerivAt.sum (u := Finset.univ) fun output _ =>
    HasDerivAt.sum (u := Finset.univ) fun input _ => entry output input
  simpa only [energy,nonlinearWork,heatWork,forceWork,sigma,Finset.sum_fn,Finset.sum_add_distrib] using! sum

theorem cube_energy_balance (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (radius : ℕ) :
    let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius
    deriv (energy seed F) time+nu.coeff*NativeWindowStressHeatSource.dirichlet seed time F+
      2*nu.coeff*(∫ point, NativeWindowStressHeatSource.interaction seed time F point) =
        nonlinearWork seed time F+forceWork seed time F := by
  dsimp only
  rw [(energy_hasDerivAt seed time _ (NativeWindowFiniteGramFourier.cube_closed radius)).deriv,
    (NativeWindowStressHeatSource.cube_heatWork seed time radius).1]
  ring

theorem fraction_bound (time : ℝ) : ‖fraction time‖ ≤ 1 := by
  change ‖∫ shift : ℝ, NativeForwardWindowSource.kernel shift*inactive (time-shift)‖ ≤ 1
  apply (norm_integral_le_integral_norm _).trans
  rw [← NativeForwardWindowSource.kernel_mass]
  apply integral_mono (fraction_integrable time).norm NativeForwardWindowSource.kernel_integrable
  intro shift
  change ‖NativeForwardWindowSource.kernel shift*inactive (time-shift)‖ ≤ NativeForwardWindowSource.kernel shift
  rw [norm_mul,Real.norm_of_nonneg (NativeForwardWindowSource.kernel_nonnegative shift)]
  exact mul_le_of_le_one_right (NativeForwardWindowSource.kernel_nonnegative shift)
    (NativeWindowPreparationWrite.inactive_bound _)

theorem correction_norm (time : ℝ) (F : Finset IntegerWavevector) (output input : Coordinate) :
    ‖correction stackedShortCurrent time F output input‖ ≤ NativeWindowStressPreparationInitial.pairBudget 0 := by
  have bound (point : PhysicalSpace) :
      ‖NativeWindowStressPreparationInitial.pair F point‖ ≤ NativeWindowStressPreparationInitial.pairBudget 0 := by
    simpa only [norm_iteratedFDeriv_zero] using NativeWindowStressPreparationInitial.pair_bound F 0 point
  have nonnegative := (norm_nonneg _).trans (bound 0)
  apply (ContinuousMap.norm_le (correction stackedShortCurrent time F output input) nonnegative).mpr
  intro point
  obtain ⟨space,rfl⟩ := NativeWindowStressHeatSource.circle_surjective point
  rw [correction,ContinuousMap.smul_apply,norm_smul,
    ← NativeWindowStressPreparationInitial.pair_original]
  exact (mul_le_mul (fraction_bound time)
    ((PiLp.norm_apply_le (NativeWindowStressPreparationInitial.pair F space) (output,input)).trans (bound space))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

def forceBudget : ℝ := ‖physical‖*NativeWindowStressPreparationInitial.pairBudget 0

theorem physical_correction_bound (time : ℝ) (F : Finset IntegerWavevector) (output input : Coordinate) :
    ‖physical (correction stackedShortCurrent time F output input)‖ ≤ forceBudget :=
  (physical.le_opNorm _).trans (mul_le_mul_of_nonneg_left (correction_norm time F output input) (norm_nonneg physical))

theorem forceWork_bound (time : ℝ) (F : Finset IntegerWavevector) :
    |forceWork stackedShortCurrent time F| ≤ energy stackedShortCurrent F time+(9/2 : ℝ)*forceBudget^2 := by
  have each (output input : Coordinate) :
      |inner ℝ (sigma stackedShortCurrent F output input time) (physical (correction stackedShortCurrent time F output input))| ≤
        (1/2 : ℝ)*‖sigma stackedShortCurrent F output input time‖^2+(1/2 : ℝ)*forceBudget^2 := by
    apply (abs_real_inner_le_norm _ _).trans
    apply (mul_le_mul_of_nonneg_left (physical_correction_bound time F output input) (norm_nonneg _)).trans
    nlinarith only [sq_nonneg (‖sigma stackedShortCurrent F output input time‖-forceBudget)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have bounded := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) (fun output _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
      (fun input _ => each output input)))
  apply bounded.trans_eq
  simp only [energy,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem forceWork_after (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (after : -1 ≤ time)
    (F : Finset IntegerWavevector) : forceWork seed time F = 0 := by
  simp only [forceWork,correction,NativeWindowPreparationWrite.fraction_after time after,zero_smul,
    map_zero,inner_zero_right,Finset.sum_const_zero]

theorem nonlinearWork_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    nonlinearWork seed time F = NativeWindowStressHeatBalance.nonlinearWork seed time F := by
  simp only [nonlinearWork,NativeWindowStressHeatBalance.nonlinearWork,
    NativeWindowStressPreparationAction.nonlinearWindow_original seed time nonnegative F closed]

theorem cube_energy_le (time : ℝ) (radius : ℕ) :
    let F := ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius
    deriv (energy stackedShortCurrent F) time+
      RationalVorticityEvaluator.butterflyGainViscosity.coeff*NativeWindowStressHeatSource.dirichlet stackedShortCurrent time F+
      2*RationalVorticityEvaluator.butterflyGainViscosity.coeff*
        (∫ point, NativeWindowStressHeatSource.interaction stackedShortCurrent time F point) ≤
      nonlinearWork stackedShortCurrent time F+energy stackedShortCurrent F time+(9/2 : ℝ)*forceBudget^2 := by
  dsimp only
  have balance := cube_energy_balance stackedShortCurrent time radius
  have paid := forceWork_bound time
    (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius)
  dsimp only at balance
  linarith [le_abs_self (forceWork stackedShortCurrent time
    (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.integerWaveFrequencyCube radius))]

open SourceGeneratedNativeResponseDisposition ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (closed : ∀ wave, wave ∈ F → waveNeg wave ∈ F) :
    (energy seed F (response.2.clockAdvance+time),nonlinearWork seed (response.2.clockAdvance+time) F,
      forceWork seed (response.2.clockAdvance+time) F) =
    (energy response.1 F time,nonlinearWork response.1 time F,forceWork response.1 time F) := by
  have shifted := add_nonneg response.2.clockAdvance_pos.le nonnegative
  rw [nonlinearWork_original seed _ shifted F closed,nonlinearWork_original response.1 time nonnegative F closed,
    forceWork_after seed _ (by linarith) F,forceWork_after response.1 time (by linarith) F]
  simp only [energy,sigma,NativeWindowStressHeatBalance.nonlinearWork,
    NativeWindowFiniteGramFourier.stress_next seed response generated time nonnegative,
    NativeWindowStressHeatBalance.nonlinearWindow_next seed response generated time nonnegative F closed]

end
end SaturationMonoid.NavierStokes.NativeWindowStressPreparationEnergy
