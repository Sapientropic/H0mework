import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountingEnergy

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountingJointEnergy
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSourceGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "L" => burnolMeanZeroOneMinusSquare
local notation "C" => CenteredCountingDual.forward
local notation "B" => CenteredCountingDual.reverse
local notation "ell" => CenteredCountingDual.logarithm
local notation "k" => CenteredCountingDual.constantFourier

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def contact (state : M) : M :=
  (2 : ℂ) • (inner ℂ ell state • k - inner ℂ k state • ell)

def forcing (N : ℕ) (coordinate : BurnolCompletedMellinCoordinate) : M :=
  C N (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) +
    contact (Constructor.returnState coordinate)

private theorem centered_even (state : Hq) (even : reflectRestricted q state = state) :
    reflectRestricted q (Constructor.zeroMean state : Hq) = Constructor.zeroMean state := by
  change reflectRestricted q (burnolQuarterMeanZeroProjection state) = burnolQuarterMeanZeroProjection state
  rw [← burnolQuarterMeanZeroProjection_reflect, even]

private theorem ambient_even (state : M) (even : reflectRestricted q (state : Hq) = state) :
    reflectL2 (E (state : Hq)) = E (state : Hq) := by
  change reflectL2 (burnolRadiusZeroExtension q (state : Hq)) = _
  rw [burnolRadiusZeroExtension_reflect, even]
  rfl

private theorem channel_reflect (side a : ℝ) (seed : BurnolL2) :
    reflectL2 (ContinuousChannels.channel side a seed) = ContinuousChannels.channel side a (reflectL2 seed) := by
  simp only [ContinuousChannels.channel, map_smul, reflectL2_burnolMultiplicativeDilation]

private theorem dual_reflect (N : ℕ) (seed : BurnolL2) :
    reflectL2 (DualSource.source N seed) = DualSource.source N (reflectL2 seed) := by
  have average : reflectL2 (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel 1 a seed) =
      ∫ a : ℝ in Ioc 0 (N : ℝ), reflectL2 (ContinuousChannels.channel 1 a seed) :=
    (reflectL2.toContinuousLinearMap.integral_comp_comm (ContinuousChannels.channel_integrable 1 N seed)).symm
  unfold DualSource.source
  rw [map_sub, map_sum, average]
  simp only [channel_reflect]

private theorem forward_reflect (N : ℕ) (seed : BurnolL2) :
    reflectL2 (FiniteForcing.source N seed) = FiniteForcing.source N (reflectL2 seed) := by
  have average : reflectL2 (∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel (-1) a seed) =
      ∫ a : ℝ in Ioc 0 (N : ℝ), reflectL2 (ContinuousChannels.channel (-1) a seed) :=
    (reflectL2.toContinuousLinearMap.integral_comp_comm (ContinuousChannels.channel_integrable (-1) N seed)).symm
  unfold FiniteForcing.source ContinuousChannels.normalization
  rw [map_sub, map_sum, average]
  simp only [channel_reflect, Channels.sourceChannel, map_smul, reflectL2_burnolMultiplicativeDilation]

private theorem forward_even (N : ℕ) (state : M) (even : reflectRestricted q (state : Hq) = state) :
    reflectRestricted q (C N state : Hq) = C N state := by
  apply centered_even
  change reflectRestricted q (restrictToInterval q (FiniteForcing.source N (E (state : Hq)))) = _
  rw [← restrictToInterval_reflectL2, forward_reflect, ambient_even state even]
  rfl

private theorem reverse_even (N : ℕ) (state : M) (even : reflectRestricted q (state : Hq) = state) :
    reflectRestricted q (B N state : Hq) = B N state := by
  apply centered_even
  change reflectRestricted q (restrictToInterval q (DualSource.source N (E (state : Hq)))) = _
  rw [← restrictToInterval_reflectL2, dual_reflect, ambient_even state even]
  rfl

private theorem fourier_even (state : M) (even : reflectRestricted q (state : Hq) = state) :
    reflectRestricted q (S state : Hq) = S state := by
  have fixed : sourceMeanZeroReflection state = state := Subtype.ext even
  have read := congrArg (fun x : M => (x : Hq)) (sourceMeanZeroFourier_reflect state)
  rw [fixed] at read
  exact read.symm

private theorem k_even : reflectRestricted q (k : Hq) = k := by
  apply centered_even
  rw [← sourceTruncatedFourier_reflect, reflectRestricted_intervalConstant]

private theorem ell_even : reflectRestricted q (ell : Hq) = ell := by
  apply centered_even
  apply Lp.ext
  have scaled := (negMeasurePreserving_restrict q).quasiMeasurePreserving.ae SmallScaleLog.log_coeFn
  filter_upwards [Lp.coeFn_compMeasurePreserving SmallScaleLog.logL2 (negMeasurePreserving_restrict q),
    scaled, SmallScaleLog.log_coeFn] with x reflection negRaw raw
  change reflectRestricted q SmallScaleLog.logL2 x = SmallScaleLog.logL2 (-x) at reflection
  rw [reflection, negRaw, raw]
  simp only [SmallScaleLog.logRaw, abs_neg]

private theorem contact_even (state : M) : reflectRestricted q (contact state : Hq) = contact state := by
  change reflectRestricted q ((2 : ℂ) • (inner ℂ ell state • (k : Hq) - inner ℂ k state • (ell : Hq))) = _
  rw [map_smul, map_sub, map_smul, map_smul, k_even, ell_even]
  rfl

private theorem contact_pair (left right : M) : inner ℂ (contact left) right =
    2 * (inner ℂ left ell * inner ℂ k right - inner ℂ left k * inner ℂ ell right) := by
  have scaled (a : ℂ) (x y : M) : inner ℂ (a • x) y = star a * inner ℂ x y := inner_smul_left x y a
  rw [contact, scaled, inner_sub_left, scaled, scaled]
  simp only [star_ofNat, star_def, inner_conj_symm]

/-- The vector equation is generated by the paired source and actual output parity. -/
theorem commutator (N : ℕ) (positive : 0 < N) (state : M)
    (even : reflectRestricted q (state : Hq) = state) : C N (S state) - S (B N state) = contact state := by
  let difference := C N (S state) - S (B N state) - contact state
  have evenDifference : reflectRestricted q (difference : Hq) = difference := by
    change reflectRestricted q (((C N (S state) : Hq) - (S (B N state) : Hq)) - (contact state : Hq)) = _
    rw [map_sub, map_sub, forward_even N _ (fourier_even state even), fourier_even _ (reverse_even N state even), contact_even]
    rfl
  have generated := CenteredCountingDual.commutator_pairing N positive state difference even evenDifference
  rw [← contact_pair] at generated
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change inner ℂ difference difference = 0
  change inner ℂ (C N (S state) - S (B N state) - contact state) difference = 0
  rw [inner_sub_left, generated, sub_self]

/-- The two original inverse equations retain the same complete forcing and the rank-two contact. -/
theorem original_equations (N : ℕ) (positive : 0 < N) (coordinate : BurnolCompletedMellinCoordinate) :
    C N (burnolRieszSingleFourierSource coordinate) - S (B N (Constructor.returnState coordinate)) = forcing N coordinate ∧
    C N (Constructor.returnState coordinate) - S (B N (burnolRieszSingleFourierSource coordinate)) =
      contact (burnolRieszSingleFourierSource coordinate) := by
  have source : C N (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate)) =
      C N (burnolRieszSingleFourierSource coordinate) - C N (S (Constructor.returnState coordinate)) := by
    rw [← burnolRieszSingleFourierSource_equation]
    change C N (burnolRieszSingleFourierSource coordinate - S (Constructor.returnState coordinate)) = _
    simp only [CenteredCountingDual.forward, WindowCounting.windowSource, Submodule.coe_sub,
      ← CountingDual.sourceCLM_apply, map_sub]
  constructor
  · rw [forcing, source, ← commutator N positive (Constructor.returnState coordinate)
      (burnolRieszSingleFourierReturn_reflection_fixed coordinate)]
    abel
  · exact commutator N positive _ (burnolRieszSingleFourierSource_reflection_fixed coordinate)

private theorem energy (state : M) (even : reflectRestricted q (state : Hq) = state) :
    (inner ℂ state (L state)).re = ‖state‖ ^ 2 - ‖S state‖ ^ 2 := by
  have paired := meanZero_fourier_pairing_of_reflection state (S state) (fourier_even state even)
  change (inner ℂ state (state - S (S state))).re = _
  rw [inner_sub_right, ← paired, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  change ((‖state‖ : ℂ) ^ 2 - (‖S state‖ : ℂ) ^ 2).re = _
  rw [Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

/-- Complete same-N inverse energy includes both actual exterior squares and all mean/contact terms. -/
theorem original_energy (N : ℕ) (positive : 0 < N) (coordinate : BurnolCompletedMellinCoordinate) :
    let b := burnolRieszSingleFourierSource coordinate
    let r := Constructor.returnState coordinate
    (inner ℂ (B N b) (L (B N b))).re + (inner ℂ (B N r) (L (B N r))).re =
      ((‖CountingEnergy.outside N b‖ ^ 2 + 2 * ‖CountingEnergy.head N b‖ ^ 2 - 2 * ‖inner ℂ ell b‖ ^ 2) +
      (‖CountingEnergy.outside N r‖ ^ 2 + 2 * ‖CountingEnergy.head N r‖ ^ 2 - 2 * ‖inner ℂ ell r‖ ^ 2)) +
      2 * (inner ℂ (C N b) (forcing N coordinate)).re +
      2 * (inner ℂ (C N r) (contact b)).re - ‖forcing N coordinate‖ ^ 2 - ‖contact b‖ ^ 2 := by
  dsimp only
  obtain ⟨first, second⟩ := original_equations N positive coordinate
  have firstSquare := norm_sub_sq (𝕜 := ℂ) (C N (burnolRieszSingleFourierSource coordinate)) (forcing N coordinate)
  have secondSquare := norm_sub_sq (𝕜 := ℂ) (C N (Constructor.returnState coordinate)) (contact (burnolRieszSingleFourierSource coordinate))
  rw [sub_eq_iff_eq_add] at first second
  have rearrangeFirst : C N (burnolRieszSingleFourierSource coordinate) - forcing N coordinate = S (B N (Constructor.returnState coordinate)) := by rw [first]; abel
  have rearrangeSecond : C N (Constructor.returnState coordinate) - contact (burnolRieszSingleFourierSource coordinate) = S (B N (burnolRieszSingleFourierSource coordinate)) := by rw [second]; abel
  rw [rearrangeFirst] at firstSquare
  rw [rearrangeSecond] at secondSquare
  rw [energy _ (reverse_even N _ (burnolRieszSingleFourierSource_reflection_fixed coordinate)),
    energy _ (reverse_even N (Constructor.returnState coordinate) (burnolRieszSingleFourierReturn_reflection_fixed coordinate))]
  have source := CountingEnergy.original_norms N positive coordinate
  dsimp only at source
  change _ = ‖C N (burnolRieszSingleFourierSource coordinate)‖ ^ 2 -
    2 * (inner ℂ (C N (burnolRieszSingleFourierSource coordinate)) (forcing N coordinate)).re + _ at firstSquare
  change _ = ‖C N (Constructor.returnState coordinate)‖ ^ 2 -
    2 * (inner ℂ (C N (Constructor.returnState coordinate)) (contact (burnolRieszSingleFourierSource coordinate))).re + _ at secondSquare
  linarith
end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountingJointEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
