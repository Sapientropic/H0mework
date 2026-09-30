import H0mework.Versions.X.NavierStokes.PhysicalJets.VorticityAction

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeResolvedSourceAction

open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open NativeReceiptTimeProfile NativeStressSource NativeUnifiedVorticityAction

noncomputable section

variable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
  {receipt : WholeContinuousMildSerrinReceipt nu initial duration}

def resolved (receipt : WholeContinuousMildSerrinReceipt nu initial duration)
    (modes : Finset IntegerWavevector) (space : PhysicalSpace) (actual : ℝ) : PhysicalSpace :=
  finiteRealComplexFourierField modes (NativeReceiptSpacetime.state receipt actual) space

theorem finite_tangent_read (modes : Finset IntegerWavevector) (viscosity : ℝ)
    (state : ComplexVorticityHilbertState) (space : PhysicalSpace) :
    finiteRealComplexFourierField modes (wholeLatticeVorticityFourierTangentAt viscosity state) space =
      projectedWholePhysicalTangent modes viscosity state space := by
  change (∑ wave ∈ modes, realModeCLM wave space
      (wholeLatticeVorticityFourierTangentAt viscosity state wave)) = _
  simp only [wholeLatticeVorticityFourierTangentAt, map_sub, Finset.sum_sub_distrib]
  change _ - _ = (∑ wave ∈ modes, realModeCLM wave space
    (ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow.wholeStateVorticityNonlinearCoefficientAt state wave)) -
      ∑ wave ∈ modes, realModeCLM wave space ((viscosity * integerWaveViscousMultiplier wave) •
        complexSharpSupportProjection modes state wave)
  congr 1
  apply Finset.sum_congr rfl
  intro wave member
  rw [complexSharpSupportProjection_apply, if_pos member]

theorem resolved_hasDerivAt (window : Window receipt) (modes : Finset IntegerWavevector)
    (space : PhysicalSpace) (actual : ℝ) (inside : actual ∈ Ioo window.first window.last) :
    HasDerivAt (resolved receipt modes space)
      (projectedWholePhysicalTangent modes nu.coeff (NativeReceiptSpacetime.state receipt actual) space) actual := by
  rw [← finite_tangent_read]
  have rows : (fun wave => rate window actual wave) =
      wholeLatticeVorticityFourierTangentAt nu.coeff (NativeReceiptSpacetime.state receipt actual) :=
    funext (rate_row window actual inside)
  rw [← rows]
  change HasDerivAt (fun time => ∑ wave ∈ modes, realModeCLM wave space (NativeReceiptSpacetime.state receipt time wave))
    (∑ wave ∈ modes, realModeCLM wave space (rate window actual wave)) actual
  apply HasDerivAt.fun_sum
  intro wave _
  exact (realModeCLM wave space).hasFDerivAt.comp_hasDerivAt actual
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).hasFDerivAt.comp_hasDerivAt actual
      (state_hasDerivAt window actual inside))

theorem resolved_native_action (window : Window receipt) (modes : Finset IntegerWavevector)
    (space : PhysicalSpace) (actual : ℝ) (inside : actual ∈ Ioo window.first window.last) :
    HasDerivAt (resolved receipt modes space)
      (resolvedClassicalPhysicalTangent modes nu.coeff (NativeReceiptSpacetime.state receipt actual) space +
        nativeTurbulenceCorrectionField modes (NativeReceiptSpacetime.state receipt actual) space) actual := by
  have source := resolved_hasDerivAt window modes space actual inside
  rwa [projectedWholePhysicalTangent_eq_classical_add_nativeTurbulence] at source

theorem resolved_residual (window : Window receipt) (modes : Finset IntegerWavevector)
    (space : PhysicalSpace) (actual : ℝ) (inside : actual ∈ Ioo window.first window.last) :
    deriv (resolved receipt modes space) actual -
      resolvedClassicalPhysicalTangent modes nu.coeff (NativeReceiptSpacetime.state receipt actual) space =
        nativeTurbulenceCorrectionField modes (NativeReceiptSpacetime.state receipt actual) space := by
  rw [(resolved_native_action window modes space actual inside).deriv]
  abel

def source (index : ℕ) (modes : Finset IntegerWavevector) (space : PhysicalSpace) : ℝ → PhysicalSpace :=
  resolved (NativeFinitePrefixTimeChart.receipt index) modes space

theorem source_native_action (index : ℕ) (modes : Finset IntegerWavevector) (space : PhysicalSpace) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) :
    HasDerivAt (source index modes space)
      (resolvedClassicalPhysicalTangent modes RationalVorticityEvaluator.butterflyGainViscosity.coeff
          (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual) space +
        nativeTurbulenceCorrectionField modes
          (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual) space) actual :=
  resolved_native_action (NativeFinitePrefixTimeChart.window index) modes space actual inside

theorem source_residual (index : ℕ) (modes : Finset IntegerWavevector) (space : PhysicalSpace) (actual : ℝ)
    (inside : actual ∈ Ioo (0 : ℝ) (NativeFinitePrefixTimeChart.duration index)) :
    deriv (source index modes space) actual -
      resolvedClassicalPhysicalTangent modes RationalVorticityEvaluator.butterflyGainViscosity.coeff
        (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual) space =
      nativeTurbulenceCorrectionField modes
        (NativeReceiptSpacetime.state (NativeFinitePrefixTimeChart.receipt index) actual) space :=
  resolved_residual (NativeFinitePrefixTimeChart.window index) modes space actual inside

end
end SaturationMonoid.NavierStokes.NativeResolvedSourceAction
