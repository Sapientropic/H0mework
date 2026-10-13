import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance boundaryFeetComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Source
export OriginalKConstantContactSourceAction.ConstantSource (value velocity seed)
end Source
local notation "P" => burnolEvenAmbientProjection


local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualSeedWindowPrice (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (1 / 4 : ℂ) * (star (FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation (-h) (test : BurnolL2))) +
    star (FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation h (test : BurnolL2))) -
    2 * star (FiniteMobiusResolventFlux.actualMean (test : BurnolL2)))

/-- Actual projection adjoint and the original normalized quarter seed pay the complete moving contact in its real order. -/
theorem actual_seed_boundary_window_price (test : BurnolPaAmbientCarrier) (h : ℝ) :
    inner ℂ test (actualSeedBoundaryIncrement h) = actualSeedWindowPrice test h := by
  have projected := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left test
      (pairedBurnolMultiplicativeDilation h Source.seed - Source.seed)
  change inner ℂ test (actualSeedBoundaryIncrement h) =
    inner ℂ (test : BurnolL2) (pairedBurnolMultiplicativeDilation h Source.seed - Source.seed) at projected
  rw [projected]
  unfold pairedBurnolMultiplicativeDilation
  simp only [smul_apply, add_apply]
  change inner ℂ (test : BurnolL2)
    ((1 / 2 : ℂ) • (burnolMultiplicativeDilation h Source.seed + burnolMultiplicativeDilation (-h) Source.seed) - Source.seed) = _
  have positive := (burnolMultiplicativeDilation h).inner_map_eq_flip Source.seed (test : BurnolL2)
  rw [← burnolMultiplicativeDilation_neg_eq_symm] at positive
  have negative := (burnolMultiplicativeDilation (-h)).inner_map_eq_flip Source.seed (test : BurnolL2)
  rw [← burnolMultiplicativeDilation_neg_eq_symm, neg_neg] at negative
  have sourcePositive := OriginalKConstantContactSourceAction.actual_constant_seed_input_price
    (burnolMultiplicativeDilation (-h) (test : BurnolL2))
  have sourceNegative := OriginalKConstantContactSourceAction.actual_constant_seed_input_price
    (burnolMultiplicativeDilation h (test : BurnolL2))
  have sourceInitial := OriginalKConstantContactSourceAction.actual_constant_seed_input_price (test : BurnolL2)
  unfold actualSeedWindowPrice
  simp only [inner_sub_right, inner_smul_right, inner_add_right]
  rw [← inner_conj_symm (test : BurnolL2) (burnolMultiplicativeDilation h Source.seed), positive, sourcePositive,
    ← inner_conj_symm (test : BurnolL2) (burnolMultiplicativeDilation (-h) Source.seed), negative, sourceNegative,
    ← inner_conj_symm (test : BurnolL2) Source.seed, sourceInitial]
  simp only [Complex.star_def, map_mul, map_div₀, map_one, map_ofNat]
  ring

private theorem actual_fourier_seed_increment (h : ℝ) :
    actualFourierSeedBoundaryIncrement h = Fphysical (actualSeedBoundaryIncrement h) := by
  apply Subtype.ext
  have source : pairedBurnolMultiplicativeDilation h (fourierL2 Source.seed) =
      fourierL2 (pairedBurnolMultiplicativeDilation h Source.seed) := by
    unfold pairedBurnolMultiplicativeDilation
    simp only [smul_apply, add_apply]
    change (1 / 2 : ℂ) • (burnolMultiplicativeDilation h (fourierL2 Source.seed) +
      burnolMultiplicativeDilation (-h) (fourierL2 Source.seed)) =
      fourierL2 ((1 / 2 : ℂ) • (burnolMultiplicativeDilation h Source.seed + burnolMultiplicativeDilation (-h) Source.seed))
    rw [map_smul, map_add, fourierL2_burnolMultiplicativeDilation,
      fourierL2_burnolMultiplicativeDilation, neg_neg]
    module
  unfold actualFourierSeedBoundaryIncrement actualSeedBoundaryIncrement
  rw [source, ← map_sub]
  exact (fourierL2_evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius _).symm

theorem actual_fourier_seed_boundary_window_price (test : BurnolPaAmbientCarrier) (h : ℝ) :
    inner ℂ test (actualFourierSeedBoundaryIncrement h) = actualSeedWindowPrice (Fphysical test) h := by
  rw [actual_fourier_seed_increment]
  have original := OriginalRieszFiniteSynthesis.fourier_pairing (actualSeedBoundaryIncrement h) test
  change inner ℂ (Fphysical (actualSeedBoundaryIncrement h)) test =
    inner ℂ (actualSeedBoundaryIncrement h) (Fphysical test) at original
  have generated : inner ℂ test (Fphysical (actualSeedBoundaryIncrement h)) =
      inner ℂ (Fphysical test) (actualSeedBoundaryIncrement h) := by
    simpa only [Complex.star_def, inner_conj_symm] using congrArg star original
  rw [generated, actual_seed_boundary_window_price]

def actualBoundarySourceRead (coordinate : BurnolCompletedMellinCoordinate) (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (pairedMellinTranslationCharacter coordinate.value h - 1) * inner ℂ test (burnolCompletedMellinRieszVector coordinate) -
    (1 / 2 : ℂ) * inner ℂ (test : BurnolL2) (actualCorrectedVelocityIntegral coordinate h) -
    OriginalRieszSource.Kernel.A coordinate * actualSeedWindowPrice test h +
    OriginalRieszSource.Kernel.beta coordinate * actualSeedWindowPrice (Fphysical test) h

/-- The full physical boundary price consumes its actual corrected source action and both original moving window contacts. -/
theorem actual_boundary_source_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (test : BurnolPaAmbientCarrier) (h : ℝ) :
    inner ℂ test (burnolZeroPairedFixedAnnulusBoundary coordinate zero h) = actualBoundarySourceRead coordinate test h := by
  rw [← actual_boundary_programme_realizes coordinate zero h]
  unfold actualBoundaryProgramme actualBoundarySourceRead
  simp only [inner_add_right, inner_sub_right, inner_smul_right]
  rw [actual_seed_boundary_window_price, actual_fourier_seed_boundary_window_price]
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left test (actualCorrectedVelocityIntegral coordinate h)
  change inner ℂ test (P (actualCorrectedVelocityIntegral coordinate h)) =
    inner ℂ (test : BurnolL2) (actualCorrectedVelocityIntegral coordinate h) at physical
  rw [physical]


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
