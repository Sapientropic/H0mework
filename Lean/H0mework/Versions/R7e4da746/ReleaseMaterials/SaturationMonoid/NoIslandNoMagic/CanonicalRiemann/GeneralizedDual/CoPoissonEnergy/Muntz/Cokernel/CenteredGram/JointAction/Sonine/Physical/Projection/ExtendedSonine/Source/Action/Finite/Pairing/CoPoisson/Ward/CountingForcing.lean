import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingJointEnergy
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientContinuousMean

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountingForcing
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSource.Translator
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "C" => CenteredCountingDual.forward
local notation "ell" => CenteredCountingDual.logarithm

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def integerSource (coordinate : BurnolCompletedMellinCoordinate) : M :=
  Constructor.zeroMean (∑' n : ℕ, InverseAction.countingWindow n (ForcingTail.forcingRemainderState coordinate))

/-- The entire regular integer source and its original logarithmic mean survive. -/
def value (coordinate : BurnolCompletedMellinCoordinate) : M :=
  integerSource coordinate - ForcingMeanZero.mean coordinate • ell

private theorem forcing_decomposition (coordinate : BurnolCompletedMellinCoordinate) :
    burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) =
      SingularCounting.originalSingularSource coordinate + ForcingTail.meanZeroRemainder coordinate := by
  rw [← burnolRieszSingleFourierSource_equation]
  change burnolRieszSingleFourierSource coordinate -
    burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) = _
  conv_lhs =>
    lhs
    rw [WholeSourceCounting.original_b_decomposition]
  change _ = ForcingPrimitive.leadingCoefficient coordinate • SingularCounting.centeredPower coordinate + _
  abel

private theorem forward_add (N : ℕ) (left right : M) : C N (left + right) = C N left + C N right := by
  change SingularCounting.projectedSource N (left + right) =
    SingularCounting.projectedSource N left + SingularCounting.projectedSource N right
  exact WholeSourceCounting.projectedSource_add N left right

private theorem remainder_source (coordinate : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    C N (ForcingTail.meanZeroRemainder coordinate) =
      Constructor.zeroMean (WindowCounting.windowSource N (ForcingTail.forcingRemainderState coordinate)) -
      burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • ell := by
  have centered : (ForcingTail.meanZeroRemainder coordinate : Hq) = ForcingTail.forcingRemainderState coordinate -
      burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • intervalConstant q := Constructor.zeroMean_read _
  rw [CenteredCountingDual.forward, centered]
  have linear : WindowCounting.windowSource N (ForcingTail.forcingRemainderState coordinate -
      burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • intervalConstant q) =
      WindowCounting.windowSource N (ForcingTail.forcingRemainderState coordinate) -
        burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • WindowCounting.windowSource N (intervalConstant q) := by
    simp only [WindowCounting.windowSource, ← CountingDual.sourceCLM_apply, map_sub, map_smul]
  rw [linear, map_sub, map_smul, CenteredCountingDual.constant_source N positive]

private theorem remainder_limit (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun N : ℕ => C N (ForcingTail.meanZeroRemainder coordinate)) atTop
      (𝓝 (integerSource coordinate - burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • ell)) := by
  have generated := Constructor.zeroMean.continuous.tendsto _ |>.comp (WholeSourceWindow.forcing_window_limit coordinate)
  have uncentered : Tendsto (fun N : ℕ => Constructor.zeroMean (WindowCounting.windowSource N
      (ForcingTail.forcingRemainderState coordinate))) atTop (𝓝 (integerSource coordinate)) := by
    simpa only [Function.comp_apply, map_sub, AmbientContinuousMean.forcing_continuous,
      map_smul, Constructor.zeroMean_constant, smul_zero, sub_zero] using! generated
  apply (uncentered.sub_const (burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • ell)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N after
  exact (remainder_source coordinate N (Nat.lt_of_lt_of_le (by decide : 0 < 1) after)).symm

/-- The original zeta zero removes exactly the Dirichlet coefficient; the full forcing is not set to zero. -/
theorem original_limit (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => C N (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate))) atTop
      (𝓝 (value coordinate)) := by
  have singular := SmallScaleLog.original_singular_log_limit coordinate zero
  change Tendsto (fun N : ℕ => C N (SingularCounting.originalSingularSource coordinate)) atTop
    (𝓝 (-(ForcingPrimitive.leadingCoefficient coordinate * burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate)) • ell)) at singular
  have total := singular.add (remainder_limit coordinate)
  have same : (fun N : ℕ => C N (SingularCounting.originalSingularSource coordinate) + C N (ForcingTail.meanZeroRemainder coordinate)) =
      (fun N : ℕ => C N (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate))) := by
    funext N
    rw [forcing_decomposition, forward_add]
  rw [same] at total
  have complete : -(ForcingPrimitive.leadingCoefficient coordinate * burnolQuarterMeanCoefficient (SingularCounting.powerL2 coordinate)) • ell +
      (integerSource coordinate - burnolQuarterMeanCoefficient (ForcingTail.forcingRemainderState coordinate) • ell) = value coordinate := by
    rw [value, WholeSourceCounting.original_mean_balance]
    module
  rwa [complete] at total

/-- The independent rank-two source stays attached to the actual limiting forcing. -/
theorem joint_limit (coordinate : BurnolCompletedMellinCoordinate) (zero : riemannZeta coordinate.value = 0) :
    Tendsto (fun N : ℕ => CountingJointEnergy.forcing N coordinate) atTop
      (𝓝 (value coordinate + CountingJointEnergy.contact (Constructor.returnState coordinate))) :=
  (original_limit coordinate zero).add_const _
end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountingForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
