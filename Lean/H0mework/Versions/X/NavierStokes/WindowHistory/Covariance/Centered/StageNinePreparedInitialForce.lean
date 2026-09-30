import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedForcingDefect
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.RawCompletion.Pair

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedInitialForce
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section

theorem initial_history_value (M : ℕ) :
    finiteHistory stackedShortCurrent (-2) M =
      NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0) := by
  rw [← NativeWindowHistoryPreparedEnergy.initial_source M]
  rfl

theorem initial_laplacian_bound (M : ℕ) :
    ‖NativeWindowHistoryAnnihilationControl.laplacianAction butterflyGainViscosity M
        (finiteHistory stackedShortCurrent (-2) M)‖^2 ≤
      3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] := by
  let h := finiteHistory stackedShortCurrent (-2) M
  have row (j : Coordinate) :
      gradient M (NativeWindowHistoryJacobianSpatial.spatial M j h) ≤
        (2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] := by
    have word : NativeWindowHistoryJacobianSpatial.spatial M j h =
        NativeWindowHistoryPreparedEnergy.initial M [j] :=
      NativeWindowHistorySpatialWords.source_preparation M [j]
    rw [word]
    change gradient M (NativeWindowHistoryMeanProjection.embed
      (includeCLM (modes M) (modes_closed M)
        (NativeWindowStageNineSource.coefficient stackedShortCurrent M [j] 0))) ≤ _
    rw [NativeWindowHistoryMeanGradient.gradient_embed,
      NativeWindowAugmentedTestProduct.curl_original (modes M) _ (modes_zero M)]
    have paid := NativeWindowStageNineInitialMoments.initial_gradient M [j]
    exact (mul_le_mul_of_nonneg_left paid (sq_nonneg _)).trans_eq (by
      simp only [NativeWindowStageNineInitialMoments.gradientBudget,List.length_singleton])
  have summed := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun j _ => row j)
  change (∑j : Coordinate,gradient M (NativeWindowHistoryJacobianSpatial.spatial M j h)) ≤
    ∑_j : Coordinate,(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] at summed
  calc
    _ = ∑j : Coordinate,gradient M (NativeWindowHistoryJacobianSpatial.spatial M j h) :=
      (NativeResidualMetricPair.gradient_sum butterflyGainViscosity M h).symm
    _ ≤ _ := summed
    _ = _ := by simp only [Fin.sum_univ_three]; ring

theorem initial_physical_laplacian_bound (M : ℕ) :
    ‖coefficients (modes M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M)
        butterflyGainViscosity (NativeWindowTraceAdjoint.value stackedShortCurrent M 0))‖^2 ≤
      3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] := by
  have paid := initial_laplacian_bound M
  rw [initial_history_value] at paid
  change ‖(NativeWindowHistoryAnnihilationControl.laplacianFiber butterflyGainViscosity M).compLpL
      2 NativeForwardWindowPairingReadout.averageMeasure
      (NativeWindowHistoryMeanProjection.embed
        (NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0))‖^2 ≤ _ at paid
  rw [NativeWindowHistoryMeanProjection.comp_embed
      (NativeWindowHistoryAnnihilationControl.laplacianFiber butterflyGainViscosity M)] at paid
  simp only [NativeWindowHistoryAnnihilationControl.laplacianFiber,
    NativeWindowHistoryOseen.velocityPath,NativeWindowHistoryOseen.lift_included,
    NativeWindowHistoryMeanProjection.embed_norm,
    NativePhysicalPairing.include_norm (modes M) (modes_zero M)] at paid
  exact paid

def initialSquareBudget : ℝ :=
  NativeWindowHistorySchurAdvectorFiber.squareCap*(2*Real.pi)^2*
    NativeWindowPreparedPressureSource.gradientEnvelope 0

theorem initialSquareBudget_nonnegative : 0 ≤ initialSquareBudget := by
  unfold initialSquareBudget
  exact mul_nonneg
    (mul_nonneg NativeWindowHistorySchurAdvectorFiber.squareCap_nonnegative (sq_nonneg _))
    (NativeWindowPreparedPressureSource.gradientEnvelope_nonnegative 0)

def initialTransportBudget : ℝ :=
  3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0]+
    NativeWindowHistoryCreationForm.budget initialSquareBudget ((2*Real.pi)^2)*
      ((2*Real.pi)^2*NativeWindowPreparedPressureSource.gradientEnvelope 0)

theorem initial_transport_bound (M : ℕ) :
    ‖coefficients (modes M)
      (NativeWindowHistoryCreationGeometry.transport (modes M) (modes_zero M) (modes_closed M)
        butterflyGainViscosity (NativeWindowTraceAdjoint.value stackedShortCurrent M 0)
        (NativeWindowTraceAdjoint.value stackedShortCurrent M 0))‖^2 ≤
      initialTransportBudget := by
  let u := NativeWindowTraceAdjoint.value stackedShortCurrent M 0
  have coefficient : ‖NativeWindowStressHeatSource.physical
      (NativeWindowHistoryCreationGeometry.square (modes M) u)‖ ≤ initialSquareBudget :=
    (NativeWindowHistorySchurAdvectorFiber.square_bound M u).trans
      (mul_le_mul_of_nonneg_left
        (NativeStageNinePreparedGraph.value_zero_gradient_bound M)
        NativeWindowHistorySchurAdvectorFiber.squareCap_nonnegative |>.trans_eq
          (by unfold initialSquareBudget; ring))
  have paid := NativeWindowHistorySchurAdvectorAction.transport_graph_bound
    butterflyGainViscosity M u u initialSquareBudget 1 (by norm_num) coefficient
  simp only [one_mul] at paid
  have lap : pairing (modes M)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M)
        butterflyGainViscosity u)
      (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M)
        butterflyGainViscosity u) ≤
        3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] := by
    change inner ℝ (coefficients (modes M) (NativeWindowOperatorGreen.laplacian
      (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity u))
      (coefficients (modes M) (NativeWindowOperatorGreen.laplacian
      (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity u)) ≤ _
    rw [real_inner_self_eq_norm_sq]
    exact initial_physical_laplacian_bound M
  have cost : curlPair (modes M) u.1 u.1 ≤
      (2*Real.pi)^2*NativeWindowPreparedPressureSource.gradientEnvelope 0 :=
    NativeStageNinePreparedGraph.value_zero_gradient_bound M
  have C0 : 0 ≤ NativeWindowHistoryCreationForm.budget initialSquareBudget ((2*Real.pi)^2) := by
    unfold NativeWindowHistoryCreationForm.budget
    positivity
  unfold initialTransportBudget
  exact paid.trans (add_le_add lap (mul_le_mul_of_nonneg_left cost C0))

def initialForwardBudget : ℝ :=
  2*butterflyGainViscosity.coeff^2*
    (3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0])+
      2*initialTransportBudget

theorem initial_forward_bound (M : ℕ) :
    ‖NativeWindowHistoryOseen.forwardFiber stackedShortCurrent M 0
      (NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0)‖^2 ≤
      initialForwardBudget := by
  let u := NativeWindowTraceAdjoint.value stackedShortCurrent M 0
  let U := NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0
  let heat := NativeWindowHistoryMeanBlocks.diffusion butterflyGainViscosity M U
  let transport := NativeWindowHistorySchurAdvectorFiber.family butterflyGainViscosity M U U
  have first : ‖heat‖^2 ≤ butterflyGainViscosity.coeff^2*
      (3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0]) := by
    have original := NativeWindowMetricGraphMean.diffusion_laplacian butterflyGainViscosity M U
    have read : ‖NativeWindowHistoryAnnihilationControl.laplacianFiber butterflyGainViscosity M U‖^2 ≤
        3*(2*Real.pi)^2*NativeWindowStageNineInitialMoments.gradientBudget [0] := by
      have equal : (LinearMap.toContinuousLinearMap
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M)
            butterflyGainViscosity)) u =
          NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M)
            butterflyGainViscosity u := rfl
      simp only [U,NativeWindowHistoryOseen.velocityPath,
        NativeWindowHistoryAnnihilationControl.laplacianFiber,
        NativeWindowHistoryOseen.lift_included,
        NativePhysicalPairing.include_norm (modes M) (modes_zero M)]
      rw [equal]
      exact initial_physical_laplacian_bound M
    change ‖NativeWindowHistoryMeanBlocks.diffusion butterflyGainViscosity M U‖^2 ≤ _
    rw [original]
    calc
      ‖(-butterflyGainViscosity.coeff) •
          NativeWindowHistoryAnnihilationControl.laplacianFiber butterflyGainViscosity M U‖^2 =
          butterflyGainViscosity.coeff^2*
            ‖NativeWindowHistoryAnnihilationControl.laplacianFiber butterflyGainViscosity M U‖^2 := by
        rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos butterflyGainViscosity.coeff_pos]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left read (sq_nonneg _)
  have second : ‖transport‖^2 ≤ initialTransportBudget := by
    simpa only [transport,U,NativeWindowHistoryOseen.velocityPath,
      NativeWindowHistorySchurAdvectorFiber.family_original,
      NativePhysicalPairing.restrict_include,
      NativePhysicalPairing.include_norm (modes M) (modes_zero M)] using
        initial_transport_bound M
  have triangle := norm_add_le heat transport
  have source := NativeWindowHistorySchurAdvectorFiber.family_source
    stackedShortCurrent M 0 U
  have normed : ‖NativeWindowHistoryOseen.forwardFiber stackedShortCurrent M 0 U‖ ≤
      ‖heat‖+‖transport‖ := by
    rw [← source]
    exact triangle
  have a0 := norm_nonneg heat
  have b0 := norm_nonneg transport
  have f0 := norm_nonneg (NativeWindowHistoryOseen.forwardFiber stackedShortCurrent M 0 U)
  unfold initialForwardBudget
  nlinarith only [first,second,normed,a0,b0,f0,sq_nonneg (‖heat‖-‖transport‖)]

def initialForwardNormBudget : ℝ := initialForwardBudget+1

theorem initialForwardNormBudget_nonnegative : 0 ≤ initialForwardNormBudget := by
  have source := initial_forward_bound 0
  unfold initialForwardNormBudget
  nlinarith only [source,sq_nonneg
    ‖NativeWindowHistoryOseen.forwardFiber stackedShortCurrent 0 0
      (NativeWindowHistoryOseen.velocityPath stackedShortCurrent 0 0)‖]

theorem initial_forward_norm_bound (M : ℕ) :
    ‖NativeWindowHistoryOseen.forwardFiber stackedShortCurrent M 0
      (NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0)‖ ≤
      initialForwardNormBudget := by
  have source := initial_forward_bound M
  have B0 : 0 ≤ initialForwardBudget :=
    (sq_nonneg _).trans source
  unfold initialForwardNormBudget
  nlinarith only [source,B0,sq_nonneg
    (‖NativeWindowHistoryOseen.forwardFiber stackedShortCurrent M 0
      (NativeWindowHistoryOseen.velocityPath stackedShortCurrent M 0)‖-1)]

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedInitialForce
