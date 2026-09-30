import H0mework.Versions.X.NavierStokes.Friedrichs.Energy
import H0mework.Versions.X.NavierStokes.SourceWindow.Pairing
import H0mework.Versions.X.NavierStokes.WindowHistory.Current

set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWholeMass
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeStressPairingCarrier NativeHilbertDiracCurrent NativeCanonicalFriedrichsPrincipal
noncomputable section

abbrev Fiber (data : Data) := PiLp 2 (fun _ : Fin 4 × Fin 2 => Space data)

def fiber (data : Data) (field : Spinor data) : Fiber data :=
  WithLp.toLp 2 fun entry => field entry.1 entry.2

def massForm (data : Data) (matrix : DiracMatrix) (first last : Spinor data) : ℝ :=
  (∑ spin : Fin 4, ∑ color : Fin 2, inner ℂ (first spin color) (action data matrix last spin color)).re

theorem action_identity (data : Data) (field : Spinor data) : action data 1 field = field := by
  funext spin color
  simp [action, Matrix.one_apply]

theorem massForm_identity (data : Data) (field : Spinor data) :
    massForm data 1 field field = ‖fiber data field‖^2 := by
  rw [massForm, action_identity, PiLp.norm_sq_eq_of_L2]
  simp only [Complex.re_sum, Fintype.sum_prod_type, fiber, PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro spin _
  exact Finset.sum_congr rfl fun color _ => (norm_sq_eq_re_inner (𝕜 := ℂ) (field spin color)).symm

theorem normalized_mass (data : Data) (velocity : PhysicalSpace) (field : Spinor data) :
    massForm data (normalized velocity 0) field field = ‖fiber data field‖^2 := by
  rw [normalized_time, massForm_identity]

theorem whole_coercivity : ∃ κ : ℝ, 0 < κ ∧ ∀ (data : Data) (velocity : PhysicalSpace)
    (field : Spinor data), κ*‖fiber data field‖^2 ≤ massForm data (normalized velocity 0) field field :=
  ⟨1, zero_lt_one, fun data velocity field => by rw [one_mul, normalized_mass]⟩

theorem temporal_current_mass (data : Data) (field : Spinor data)
    (first : field 0 = 0) (second : field 1 = 0) :
    (canonicalDual data field (action data (diracGamma 0) field)).re = ‖fiber data field‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [fiber, PiLp.toLp_apply, Fintype.sum_prod_type]
  simp [-WithLp.prod_inner_apply, canonicalDual, action, diracAdjointSpinSwap, diracGamma, diracGammaZero,
    Fin.sum_univ_four, Fin.sum_univ_two, first, second]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

variable {nu : Viscosity}

def sourceFiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    Fiber (NativeForwardWindowPairing.data seed time) :=
  fiber (NativeForwardWindowPairing.data seed time) (matter (NativeForwardWindowPairing.data seed time) 0)

theorem source_current (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖sourceFiber seed time‖^2 =
      (NativePairedCurrentFourier.coefficient
        (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) 0 0).re := by
  unfold sourceFiber
  rw [← temporal_current_mass _ _ (by funext color; fin_cases color <;> rfl)
    (by funext color; fin_cases color <;> rfl)]
  change (diracCurrent (NativeForwardWindowPairing.data seed time) 0 0).re = _
  rw [diracCurrent_eq _ _ _ (NativeForwardWindowPairingReadout.stress_symmetric seed time 0), pairedCurrent_eq]
  rfl

theorem source_complete_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖sourceFiber seed time‖^2 = 2+NativeViewEnergyContent.total seed 0 time/4 := by
  rw [source_current, NativeCanonicalFriedrichsEnergy.complete_current_zero,
    ← NativeCanonicalFriedrichsEnergy.complete_density_split]

theorem source_mass_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖sourceFiber seed time‖^2 ≤ 2+‖NativeWordStressEnergy.kineticRead‖*NativeUnifiedCompleteSource.budget seed/8 := by
  rw [source_complete_mass]
  linarith [NativeViewEnergyContent.total_bound seed 0 time]

abbrev HistoryFiber := PiLp 2 (fun _ : Fin 4 × Fin 2 => NativeWindowHistoryGNS.HistoryHilbert)

def historyFiber (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (field : Spinor (NativeForwardWindowPairing.data seed time)) : HistoryFiber :=
  WithLp.toLp 2 fun entry => NativeWindowHistoryGNS.mapSpinor seed time field entry.1 entry.2

theorem history_norm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (field : Spinor (NativeForwardWindowPairing.data seed time)) :
    ‖historyFiber seed time field‖ = ‖fiber (NativeForwardWindowPairing.data seed time) field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, historyFiber, fiber,
    NativeWindowHistoryGNS.mapSpinor, (NativeWindowHistoryGNS.realization seed time).norm_map]

theorem history_action_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (matrix : DiracMatrix)
    (first last : Spinor (NativeForwardWindowPairing.data seed time)) :
    (∑ spin : Fin 4, ∑ color : Fin 2,
      inner ℂ (NativeWindowHistoryGNS.mapSpinor seed time first spin color)
        (NativeWindowHistoryGNS.action matrix (NativeWindowHistoryGNS.mapSpinor seed time last) spin color)).re =
      massForm (NativeForwardWindowPairing.data seed time) matrix first last := by
  rw [NativeWindowHistoryGNS.action_map]
  simp only [NativeWindowHistoryGNS.mapSpinor, (NativeWindowHistoryGNS.realization seed time).inner_map_map]
  rfl

theorem history_normalized_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (velocity : PhysicalSpace)
    (field : Spinor (NativeForwardWindowPairing.data seed time)) :
    (∑ spin : Fin 4, ∑ color : Fin 2,
      inner ℂ (NativeWindowHistoryGNS.mapSpinor seed time field spin color)
        (NativeWindowHistoryGNS.action (normalized velocity 0)
          (NativeWindowHistoryGNS.mapSpinor seed time field) spin color)).re =
      ‖historyFiber seed time field‖^2 := by
  rw [history_action_mass, normalized_mass, history_norm]

theorem source_history_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (point : NativePhysicalFourier.Torus) :
    (∑ spin : Fin 4, ∑ color : Fin 2,
      inner ℂ (NativeWindowHistoryGNS.matter seed time 0 spin color)
        (NativeWindowHistoryGNS.action
          (normalized (NativeCanonicalFriedrichsEnergy.sourceVelocity seed time point) 0)
          (NativeWindowHistoryGNS.matter seed time 0) spin color)).re =
      2+NativeViewEnergyContent.total seed 0 time/4 := by
  unfold NativeWindowHistoryGNS.matter
  rw [history_normalized_mass, history_norm]
  exact source_complete_mass seed time

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem source_mass_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    ‖sourceFiber seed (step.2.clockAdvance+time)‖^2 = ‖sourceFiber step.1 time‖^2 := by
  exact congrArg (fun data => ‖fiber data (matter data 0)‖^2)
    (NativeWindowHistoryGNS.data_next seed step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowWholeMass
