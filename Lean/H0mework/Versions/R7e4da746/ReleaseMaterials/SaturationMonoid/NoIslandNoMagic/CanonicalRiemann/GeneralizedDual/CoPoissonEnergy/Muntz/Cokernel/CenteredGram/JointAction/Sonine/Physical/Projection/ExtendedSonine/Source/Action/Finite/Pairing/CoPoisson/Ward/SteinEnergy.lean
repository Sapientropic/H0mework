import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ShiftPair

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.SteinEnergy

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def defect (coordinate : BurnolCompletedMellinCoordinate) : M :=
  Constructor.returnState coordinate - ShiftPair.forward (ShiftPair.reverse (Constructor.returnState coordinate))

private theorem forward_even (value : M)
    (even : reflectRestricted q (value : Hq) = value) :
    reflectRestricted q (ShiftPair.forward value : Hq) = ShiftPair.forward value := by
  have generated := ShiftPair.forward_extension value
  have reflected : reflectL2 (burnolQuarterZeroExtension (ShiftPair.forward value : Hq)) =
      burnolQuarterZeroExtension (ShiftPair.forward value : Hq) := by
    rw [generated, reflectL2_burnolMultiplicativeDilation]
    change burnolMultiplicativeDilation (Real.log 2) (reflectL2 (burnolRadiusZeroExtension q (value : Hq))) = burnolMultiplicativeDilation (Real.log 2) (burnolRadiusZeroExtension q (value : Hq))
    rw [burnolRadiusZeroExtension_reflect, even]
  have restricted := congrArg burnolQuarterRestriction reflected
  change burnolQuarterRestriction (reflectL2 (burnolQuarterZeroExtension (ShiftPair.forward value : Hq))) = _ at restricted
  rw [show burnolQuarterRestriction = restrictToInterval q from rfl,
    restrictToInterval_reflectL2] at restricted
  simpa only [show restrictToInterval q = burnolQuarterRestriction from rfl,
    burnolQuarterRestriction_zeroExtension] using restricted

private theorem energy_norm (value : M)
    (even : reflectRestricted q (value : Hq) = value) :
    inner ℂ value (L value) = (‖value‖ ^ 2 : ℂ) - (‖S value‖ ^ 2 : ℂ) := by
  have paired := OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection (S value) value even
  have conjugated := congrArg (starRingEnd ℂ) paired
  simp only [inner_conj_symm] at conjugated
  change inner ℂ value (value - S (S value)) = _
  rw [inner_sub_right, conjugated, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  rfl

private theorem defect_norm (value : M) :
    ‖value - ShiftPair.forward (ShiftPair.reverse value)‖ ^ 2 =
      ‖value‖ ^ 2 - ‖ShiftPair.reverse value‖ ^ 2 := by
  have paired := ShiftPair.adjoint_pair (ShiftPair.reverse value) value
  rw [inner_self_eq_norm_sq_to_K] at paired
  have pairedOpp : inner ℂ value (ShiftPair.forward (ShiftPair.reverse value)) = (‖ShiftPair.reverse value‖ ^ 2 : ℂ) := by
    have actual := congrArg (starRingEnd ℂ) paired
    simpa only [inner_conj_symm, map_pow, RCLike.conj_ofReal] using! actual
  rw [norm_sub_sq (𝕜 := ℂ), ShiftPair.isometry, pairedOpp]
  change ‖value‖ ^ 2 - 2 * ((‖ShiftPair.reverse value‖ : ℂ) ^ 2).re + ‖ShiftPair.reverse value‖ ^ 2 = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- The original inverse equation produces a positive defect after the fixed dilation. -/
theorem original_energy (coordinate : BurnolCompletedMellinCoordinate) :
    inner ℂ (ShiftPair.forward (burnolRieszSingleFourierSource coordinate))
      (L (ShiftPair.forward (burnolRieszSingleFourierSource coordinate))) -
      inner ℂ (burnolRieszSingleFourierSource coordinate)
        (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) =
      (‖defect coordinate‖ ^ 2 : ℂ) := by
  rw [← burnolRieszSingleFourierSource_equation coordinate,
    energy_norm _ (forward_even _ (burnolRieszSingleFourierSource_reflection_fixed coordinate)),
    energy_norm _ (burnolRieszSingleFourierSource_reflection_fixed coordinate),
    ShiftPair.isometry, ShiftPair.fourier_intertwining]
  have actual := defect_norm (Constructor.returnState coordinate)
  have complexActual := congrArg (fun x : ℝ => (x : ℂ)) actual
  push_cast at complexActual
  change (‖_‖ ^ 2 : ℂ) - (‖ShiftPair.reverse (Constructor.returnState coordinate)‖ ^ 2 : ℂ) -
    ((‖_‖ ^ 2 : ℂ) - (‖Constructor.returnState coordinate‖ ^ 2 : ℂ)) = _
  unfold defect
  rw [complexActual]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.SteinEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
