import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourier
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.WholeSourceWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.AmbientContact

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSource.Translator
open OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def regularSlot (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  ((∑' n : ℕ, countingWindow (n : ℝ) (ForcingTail.forcingRemainderState coordinate)) -
    ∫ scale : ℝ in Ioi 0, countingWindow scale (ForcingTail.forcingRemainderState coordinate)) +
  ((∑' n : ℕ, countingWindow (n : ℝ) (WholeSourceWindow.smoothState coordinate)) -
    ∫ scale : ℝ in Ioi 0, countingWindow scale (WholeSourceWindow.smoothState coordinate))

def positionSlot (coordinate : BurnolCompletedMellinCoordinate) : BurnolQuarterIntervalL2 :=
  ForcingPrimitive.leadingCoefficient coordinate •
      (((q : ℂ) ^ (star coordinate.value - 1) / (1 - star coordinate.value)) • intervalConstant q) +
    regularSlot coordinate - fourierMean coordinate •
      ((Real.eulerMascheroniConstant : ℂ) • intervalConstant q + SmallScaleLog.logL2)

theorem original_mean (coordinate : BurnolCompletedMellinCoordinate) :
    ForcingMeanZero.mean coordinate + burnolQuarterMeanCoefficient (WholeSourceWindow.smoothState coordinate) =
      fourierMean coordinate := rfl

/-- Both slots now read the same ambient source occurrence. -/
theorem original_position_slot (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolQuarterRestriction (AmbientCounting.value coordinate) = positionSlot coordinate := by
  have actual := (burnolQuarterRestriction.continuous.tendsto
    (AmbientCounting.value coordinate)).comp (AmbientCounting.original_ambient_limit coordinate)
  have window := WholeSourceWindow.original_window_limit coordinate zero
  have same := tendsto_nhds_unique actual window
  rw [original_mean] at same
  exact same.trans (by unfold positionSlot regularSlot; module)

theorem original_window_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (test : BurnolQuarterIntervalL2) :
    inner ℂ (AmbientCounting.value coordinate) (burnolQuarterZeroExtension test) =
      inner ℂ (positionSlot coordinate) test := by
  calc
    _ = inner ℂ (burnolQuarterRestriction (AmbientCounting.value coordinate)) test :=
      ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
    _ = _ := by rw [original_position_slot coordinate zero]

/-- The original mean-zero cotest removes constants only after the full source calculation. -/
theorem original_meanZero_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (test : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (AmbientCounting.value coordinate) (burnolQuarterZeroExtension (test : BurnolQuarterIntervalL2)) =
      inner ℂ (regularSlot coordinate) (test : BurnolQuarterIntervalL2) -
        star (fourierMean coordinate) * inner ℂ SmallScaleLog.logL2 (test : BurnolQuarterIntervalL2) := by
  have meanZero : inner ℂ (intervalConstant q) (test : BurnolQuarterIntervalL2) = 0 :=
    (Submodule.mem_orthogonal _ _).mp test.property _ (Submodule.mem_span_singleton_self _)
  rw [original_window_pair coordinate zero]
  simp only [positionSlot, inner_sub_left, inner_add_left, inner_smul_left, meanZero,
    mul_zero, zero_add]
  rfl

theorem original_fourier_source_pair_zero (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (AmbientCounting.value coordinate)
      (fourierL2 (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))) = 0 := by
  let source := burnolQuarterZeroExtension
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  have reflected : reflectL2 source = source := by
    change reflectL2 (burnolRadiusZeroExtension q
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  have unitary := fourierL2.inner_map_map (AmbientCounting.value coordinate) (fourierL2 source)
  rw [fourierL2_fourierL2, reflected] at unitary
  rw [← unitary]
  change inner ℂ (fourierL2 (AmbientCounting.value coordinate)) (burnolQuarterZeroExtension _) = 0
  calc
    _ = inner ℂ (burnolQuarterRestriction (fourierL2 (AmbientCounting.value coordinate)))
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :=
      ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction _ _
    _ = 0 := by rw [AmbientFourier.original_fourier_gap, inner_zero_left]

/-- The complete original K consumes both source slots; the logarithmic contact survives. -/
theorem original_kernel_pair (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    inner ℂ (AmbientCounting.value coordinate) (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      inner ℂ (AmbientCounting.value coordinate)
        (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate)) +
      inner ℂ (regularSlot coordinate)
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2) -
      star (fourierMean coordinate) * inner ℂ SmallScaleLog.logL2
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) : BurnolQuarterIntervalL2) := by
  rw [Kernel.original_kernel_reconstruction, inner_sub_right, inner_add_right,
    original_fourier_source_pair_zero, sub_zero, original_meanZero_pair coordinate zero]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.AmbientContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
