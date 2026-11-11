import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExteriorCoPoissonAction.Arithmetic
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.KCountingGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReturnCounting

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction
open Complex Filter MeasureTheory Set BurnolPhysicalState
open BurnolPhysicalState.OriginalRieszSource BurnolPhysicalState.OriginalRieszSourceGreen
open BurnolPhysicalState.OriginalRieszFinitePairing
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson
open BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFixedBoundarySourceFibre
open OriginalKExteriorCoPoissonAction
open scoped InnerProductSpace Topology
local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2

/-- The actual zero pays L2 for the singular arithmetic event before the vectors are combined. -/
def elementaryReverseSource (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) : BurnolL2 :=
  -PositionCounting.value c zero - ReturnCounting.value c

def elementaryReverseRaw (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -(∑ n ∈ DualSourceRaw.channels x,
    ((1/2 : ℂ) * (((n : ℝ)*|x| : ℝ) : ℂ) ^ (-star c.value) - GapEuler.gapMean q c))

/-- All return samples cancel inside the whole vector; the singular power was never made an L2 input. -/
theorem elementary_reverse_raw (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    (elementaryReverseSource c zero : ℝ → ℂ) =ᵐ[volume] elementaryReverseRaw c := by
  filter_upwards [Lp.coeFn_sub (-PositionCounting.value c zero) (ReturnCounting.value c),
    Lp.coeFn_neg (PositionCounting.value c zero), PositionCounting.value_coeFn c zero,
    ReturnCounting.value_coeFn c] with x difference negative position returned
  change (-PositionCounting.value c zero - ReturnCounting.value c : BurnolL2) x = _
  rw [difference, Pi.sub_apply, negative, Pi.neg_apply, position, returned]
  simp only [PositionCounting.eventRaw, ReturnCounting.eventRaw, positionSource,
    elementaryReverseRaw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

theorem elementary_reverse_support (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    OriginalPaPhysicalGreen.originalPhysicalCutoff q (elementaryReverseSource c zero) =
      elementaryReverseSource c zero := by
  have linear : OriginalPaPhysicalGreen.originalPhysicalCutoff q
      (-PositionCounting.value c zero - ReturnCounting.value c) =
      -OriginalPaPhysicalGreen.originalPhysicalCutoff q (PositionCounting.value c zero) -
        OriginalPaPhysicalGreen.originalPhysicalCutoff q (ReturnCounting.value c) := by
    unfold OriginalPaPhysicalGreen.originalPhysicalCutoff
    rw [map_sub, map_neg, map_sub, map_neg]
  rw [elementaryReverseSource, linear, PositionCounting.value_support, ReturnCounting.value_support]

/-- The original elementary input is executed literally by the independent reverse programme. -/
theorem elementary_reverse_finite (c : BurnolCompletedMellinCoordinate) (N : ℕ) :
    DualSource.source N (elementarySource c) =
      KCountingSource.finite c N - ReturnCounting.finite c N := by
  have source : elementarySource c = KCountingSource.base c -
      burnolQuarterZeroExtension (Constructor.returnState c : Hq) := by
    unfold KCountingSource.base elementarySource gapState
    module
  rw [source, CountingDual.dual_eq_adjoint, map_sub, ←CountingDual.dual_eq_adjoint,
    ←CountingDual.dual_eq_adjoint]
  rfl

theorem elementary_reverse_tendsto (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => DualSource.source N (elementarySource c)) atTop
      (𝓝 (elementaryReverseSource c zero)) := by
  have actual := (KCountingSource.finite_tendsto c zero).sub (ReturnCounting.finite_tendsto c)
  exact actual.congr' (Eventually.of_forall (fun N => (elementary_reverse_finite c N).symm))

private theorem dual_dilation (N : ℕ) (h : ℝ) (value : BurnolL2) :
    DualSource.source N (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation h (DualSource.source N value) := by
  have channel (radius : ℝ) : ContinuousChannels.channel 1 radius (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation h (ContinuousChannels.channel 1 radius value) := by
    simp only [ContinuousChannels.channel, map_smul, burnolMultiplicativeDilation_add]
    rw [add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub, map_sum]
  congr 1
  exact (burnolMultiplicativeDilation h).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

private theorem dual_boundary (N : ℕ) (c : BurnolCompletedMellinCoordinate) (h : ℝ) (value : BurnolL2) :
    DualSource.source N (finiteBoundaryAction c h value) =
      finiteBoundaryAction c h (DualSource.source N value) := by
  unfold finiteBoundaryAction
  rw [CountingDual.dual_eq_adjoint, map_sub, map_smul, map_smul, map_add]
  simp only [←CountingDual.dual_eq_adjoint]
  rw [dual_dilation, dual_dilation]

/-- A complete source construction: compact zero-owned power action and both actual B-loss directions. -/
def coreReverseSource (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) : BurnolL2 :=
  finiteBoundaryAction c h (elementaryReverseSource c zero) - (1/2 : ℂ) •
    (FullUnit.fullReverse c h 1 - fourierL2 (FullUnit.fullForward c h 0))

theorem core_reverse_finite (c : BurnolCompletedMellinCoordinate) (h : ℝ) (N : ℕ) :
    DualSource.source N (sourceCore c h) =
      finiteBoundaryAction c h (DualSource.source N (elementarySource c)) - (1/2 : ℂ) •
        (DualSource.source N (FullUnit.fullSource c h 1) -
          fourierL2 (FiniteForcing.source N (FullUnit.fullSource c h 0))) := by
  rw [sourceCore, CountingDual.dual_eq_adjoint, map_sub, map_smul, map_sub]
  simp only [←CountingDual.dual_eq_adjoint]
  rw [dual_boundary, KCounting.dual_fourier]
  rfl

/-- The actual zero removes the power tail in the entire arithmetic action of the physical core. -/
theorem core_reverse_tendsto (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    Tendsto (fun N : ℕ => DualSource.source N (sourceCore c h)) atTop
      (𝓝 (coreReverseSource c zero h)) := by
  have continuousBoundary : Continuous (fun value : BurnolL2 => finiteBoundaryAction c h value) := by
    unfold finiteBoundaryAction
    fun_prop
  have elementary := (continuousBoundary.tendsto (elementaryReverseSource c zero)).comp
    (elementary_reverse_tendsto c zero)
  have fourier := (fourierL2.continuous.tendsto (FullUnit.fullForward c h 0)).comp
    (FullUnit.full_forward_tendsto c h nonnegative 0)
  have actual := elementary.sub (((FullUnit.full_reverse_tendsto c h nonnegative 1).sub fourier).const_smul (1/2 : ℂ))
  exact actual.congr' (Eventually.of_forall (fun N => (core_reverse_finite c h N).symm))

/-- The original K counting cotest consumes this computed core action through actual finite adjointness. -/
theorem original_core_arithmetic_ward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (KCountingGram.value c) (sourceCore c h) =
      inner ℂ (sourceKernel c) (coreReverseSource c zero h) := by
  have forward := (KCountingGram.forward_tendsto c zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := sourceCore c h))
  have reverse := (tendsto_const_nhds (x := (burnolCompletedMellinRieszVector c : BurnolL2))).inner (𝕜 := ℂ)
    (core_reverse_tendsto c zero h nonnegative)
  have same := forward.congr' (Eventually.of_forall (fun N =>
    CountingDual.source_pairing N (burnolCompletedMellinRieszVector c : BurnolL2) (sourceCore c h)))
  rw [sourceKernel_original]
  exact tendsto_nhds_unique same reverse

end OriginalKElementaryArithmeticAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
