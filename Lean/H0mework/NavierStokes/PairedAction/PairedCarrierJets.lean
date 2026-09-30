import H0mework.NavierStokes.PairedAction.PairedCarrierRegeneration

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativePairedCarrierJets

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open NativePhysicalFourier NativeStressPairingCarrier NativeHilbertDiracCurrent
open NativeResolvedPairingTransfer NativePairedCarrierRegeneration
open NativeCofinalUnifiedField (target window)
open NativeReceiptSpacetime (timeJet timeJet_zero timeJet_evolves)

noncomputable section

def shifted (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (coordinate : Coordinate) : ScalarSequence :=
  ⟨fun frequency => velocity (frequency - wave) coordinate, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have paid : Summable (fun frequency => ‖velocity frequency coordinate‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scalarSequence] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (scalarSequence velocity coordinate)).summable
    exact paid.comp_injective (fun _ _ equality => sub_left_injective equality)⟩

theorem shifted_norm (velocity : ComplexVorticityHilbertState) (wave : IntegerWavevector) (coordinate : Coordinate) :
    ‖shifted velocity wave coordinate‖ = ‖scalarSequence velocity coordinate‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have first := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (shifted velocity wave coordinate)
  have second := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (scalarSequence velocity coordinate)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at first second
  rw [first, second]
  change (∑' frequency, ‖velocity (frequency - wave) coordinate‖ ^ 2) =
    ∑' frequency, ‖velocity frequency coordinate‖ ^ 2
  rw [← (Equiv.addRight wave).tsum_eq]
  simp only [Equiv.coe_addRight, add_sub_cancel_right]

def shiftedCLM (wave : IntegerWavevector) (coordinate : Coordinate) : ComplexVorticityHilbertState →L[ℝ] ScalarSequence :=
  LinearMap.mkContinuous
    { toFun := fun velocity => shifted velocity wave coordinate
      map_add' := fun _ _ => by apply lp.ext; rfl
      map_smul' := fun _ _ => by apply lp.ext; rfl }
    1 (fun velocity => by
      change ‖shifted velocity wave coordinate‖ ≤ 1 * ‖velocity‖
      rw [one_mul, shifted_norm]
      exact lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (fun frequency => norm_le_pi_norm (velocity frequency) coordinate))

def liftCLM (data : Data) : ScalarSequence →L[ℝ] Space data :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ScalarSequence (NativePositiveKernelCarrier.Space (kernel data))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ ScalarSequence (NativePositiveKernelCarrier.Space (kernel data)))

def componentCLM (data : Data) (wave : IntegerWavevector) (coordinate : Coordinate) : ComplexVorticityHilbertState →L[ℝ] Space data :=
  (liftCLM data).comp (shiftedCLM wave coordinate)

def matterCLM (data : Data) (wave : IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ] Spinor data :=
  ContinuousLinearMap.pi fun spin => ContinuousLinearMap.pi
    (!![0, 0; 0, 0;
      (1 / 4 : ℂ) • componentCLM data wave 2,
        (1 / 4 : ℂ) • (componentCLM data wave 0 - Complex.I • componentCLM data wave 1);
      (1 / 4 : ℂ) • (componentCLM data wave 0 + Complex.I • componentCLM data wave 1),
        -(1 / 4 : ℂ) • componentCLM data wave 2] spin)

def vacuum (data : Data) (wave : IntegerWavevector) : Spinor data :=
  !![0, 0; 0, 0; background data wave, 0; 0, background data wave]

theorem transfer_background (data : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (wave : IntegerWavevector) :
    transfer data mean reality (background (resolved mean reality) wave) = background data wave := rfl

theorem transfer_component (data : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (wave : IntegerWavevector) (coordinate : Coordinate) :
    transfer data mean reality (component (resolved mean reality) (wave, coordinate)) =
      componentCLM data wave coordinate (NativeEndpointVelocityCarrier.wholeVelocity mean) := rfl

theorem writtenMatter_affine (data : Data) (mean : WholeRestartVelocityEndpointState) (reality : WholeRestartVelocityEndpointReality mean)
    (wave : IntegerWavevector) :
    writtenMatter data mean reality wave = vacuum data wave + matterCLM data wave (NativeEndpointVelocityCarrier.wholeVelocity mean) := by
  funext spin color
  change transfer data mean reality (matter (resolved mean reality) wave spin color) =
    vacuum data wave spin color + (matterCLM data wave (NativeEndpointVelocityCarrier.wholeVelocity mean)) spin color
  fin_cases spin <;> fin_cases color
  all_goals try { change transfer data mean reality 0 = 0 + 0; simp }
  · change transfer data mean reality (background (resolved mean reality) wave + (1 / 4 : ℂ) • component (resolved mean reality) (wave, 2)) =
      background data wave + (1 / 4 : ℂ) • componentCLM data wave 2 (NativeEndpointVelocityCarrier.wholeVelocity mean)
    rw [map_add, map_smul, transfer_background, transfer_component]
  · change transfer data mean reality ((1 / 4 : ℂ) • (component (resolved mean reality) (wave, 0) -
        Complex.I • component (resolved mean reality) (wave, 1))) =
      0 + (1 / 4 : ℂ) • (componentCLM data wave 0 (NativeEndpointVelocityCarrier.wholeVelocity mean) -
        Complex.I • componentCLM data wave 1 (NativeEndpointVelocityCarrier.wholeVelocity mean))
    rw [map_smul, map_sub, map_smul, transfer_component, transfer_component, zero_add]
  · change transfer data mean reality ((1 / 4 : ℂ) • (component (resolved mean reality) (wave, 0) +
        Complex.I • component (resolved mean reality) (wave, 1))) =
      0 + (1 / 4 : ℂ) • (componentCLM data wave 0 (NativeEndpointVelocityCarrier.wholeVelocity mean) +
        Complex.I • componentCLM data wave 1 (NativeEndpointVelocityCarrier.wholeVelocity mean))
    rw [map_smul, map_add, map_smul, transfer_component, transfer_component, zero_add]
  · change transfer data mean reality (background (resolved mean reality) wave - (1 / 4 : ℂ) • component (resolved mean reality) (wave, 2)) =
      background data wave + -(1 / 4 : ℂ) • componentCLM data wave 2 (NativeEndpointVelocityCarrier.wholeVelocity mean)
    rw [map_sub, map_smul, transfer_background, transfer_component, neg_smul, sub_eq_add_neg]

variable {nu : Viscosity}

def matterJet (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ) (wave : IntegerWavevector) : Spinor (cofinal initial) :=
  (if order = 0 then vacuum (cofinal initial) wave else 0) + matterCLM (cofinal initial) wave (timeJet (window initial) order actual)

theorem matterJet_zero (initial : GeneratedWholeRestartCurrent nu) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (wave : IntegerWavevector) :
    matterJet initial 0 actual wave = sourceMatter initial actual wave := by
  rw [sourceMatter, writtenMatter_affine, mean_velocity]
  simp only [matterJet, ite_true, timeJet_zero (window initial) actual inside]
  rfl

theorem matterJet_evolves (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (wave : IntegerWavevector) :
    HasDerivWithinAt (fun sample => matterJet initial order sample wave) (matterJet initial (order + 1) actual wave)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual := by
  have linear := (matterCLM (cofinal initial) wave).hasFDerivAt.comp_hasDerivWithinAt actual
    (timeJet_evolves (window initial) order actual inside)
  change HasDerivWithinAt (fun sample => matterCLM (cofinal initial) wave (timeJet (window initial) order sample))
    (matterCLM (cofinal initial) wave (timeJet (window initial) (order + 1) actual))
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual at linear
  simpa only [matterJet, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, zero_add] using
    linear.const_add (if order = 0 then vacuum (cofinal initial) wave else 0)

theorem source_matter_all_time_jets (initial : GeneratedWholeRestartCurrent nu) (order : ℕ) (actual : ℝ)
    (inside : actual ∈ Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) (wave : IntegerWavevector) :
    iteratedDerivWithin order (fun sample => sourceMatter initial sample wave)
      (Icc (0 : ℝ) (wholeRestartDuration (target initial).contact)) actual = matterJet initial order actual wave := by
  induction order generalizing actual with
  | zero => rw [iteratedDerivWithin_zero]; exact (matterJet_zero initial actual inside wave).symm
  | succ order previous =>
      rw [iteratedDerivWithin_succ, derivWithin_congr (f := fun sample => matterJet initial order sample wave)
        (fun sample member => previous sample member) (previous actual inside)]
      exact (matterJet_evolves initial order actual inside wave).derivWithin
        (uniqueDiffOn_Icc (wholeRestartDuration_pos (target initial).contact) actual inside)

end
end SaturationMonoid.NavierStokes.NativePairedCarrierJets
