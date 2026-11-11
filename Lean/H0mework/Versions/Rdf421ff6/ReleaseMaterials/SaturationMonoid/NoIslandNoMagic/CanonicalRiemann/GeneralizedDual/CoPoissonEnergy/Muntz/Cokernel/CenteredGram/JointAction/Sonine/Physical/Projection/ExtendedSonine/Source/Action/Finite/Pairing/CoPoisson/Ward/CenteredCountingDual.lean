import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDualSupport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ArithmeticAdjoint

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CenteredCountingDual

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "T" => burnolTruncatedFourier
local notation "W" => WindowCounting.windowSource

def forward (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (W N (state : BurnolQuarterIntervalL2))

def reverse (N : ℕ) (state : BurnolQuarterMeanZeroCarrier) : BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (R (DualSource.source N (E (state : BurnolQuarterIntervalL2))))

def logarithm : BurnolQuarterMeanZeroCarrier := Constructor.zeroMean SmallScaleLog.logL2
def constantFourier : BurnolQuarterMeanZeroCarrier := Constructor.zeroMean (T (intervalConstant q))

private theorem zeroMean_pair (left : BurnolQuarterIntervalL2) (right : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (Constructor.zeroMean left) right = inner ℂ left (right : BurnolQuarterIntervalL2) :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right right left

private theorem pair_zeroMean (left : BurnolQuarterMeanZeroCarrier) (right : BurnolQuarterIntervalL2) :
    inner ℂ left (Constructor.zeroMean right) = inner ℂ (left : BurnolQuarterIntervalL2) right := by
  have actual := congrArg (star : ℂ → ℂ) (zeroMean_pair right left)
  simpa only [star_def, inner_conj_symm] using actual

/-- The two centered directions are generated from the full finite source and its independently defined reverse. -/
theorem source_pairing (N : ℕ) (left right : BurnolQuarterMeanZeroCarrier) :
    inner ℂ (forward N left) right = inner ℂ left (reverse N right) := by
  rw [forward, reverse, zeroMean_pair, pair_zeroMean]
  change inner ℂ (R (FiniteForcing.source N (E (left : BurnolQuarterIntervalL2))))
    (right : BurnolQuarterIntervalL2) = _
  rw [← ContinuousLinearMap.adjoint_inner_right R, CountingDual.source_pairing]
  exact ContinuousLinearMap.adjoint_inner_left R _ _

private theorem reverse_pairing (N : ℕ) (left right : BurnolL2) :
    inner ℂ (DualSource.source N left) right = inner ℂ left (FiniteForcing.source N right) := by
  rw [CountingDual.dual_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N) _ _

private theorem forward_fourier (N : ℕ) (seed : BurnolL2) :
    FiniteForcing.source N (fourierL2 seed) = fourierL2 (DualSource.source N seed) := by
  have channel (a : ℝ) : ContinuousChannels.channel (-1) a (fourierL2 seed) =
      fourierL2 (ContinuousChannels.channel 1 a seed) := by
    simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul,
      fourierL2_burnolMultiplicativeDilation]
  have integer (n : ℕ) : Channels.sourceChannel n (fourierL2 seed) =
      fourierL2 (ContinuousChannels.channel 1 n seed) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, neg_one_mul] using channel n
  unfold FiniteForcing.source ContinuousChannels.normalization DualSource.source
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N seed)

private theorem cutoff_pair (left right : BurnolL2) (supported : right = E (R right)) :
    inner ℂ (E (R left)) right = inner ℂ left right := by
  rw [supported]
  have leftRead := ContinuousLinearMap.adjoint_inner_right R (E (R left)) (R right)
  have rightRead := ContinuousLinearMap.adjoint_inner_right R left (R right)
  change inner ℂ (E (R left)) (E (R right)) = _ at leftRead
  change inner ℂ left (E (R right)) = _ at rightRead
  rw [leftRead, rightRead, burnolQuarterRestriction_zeroExtension]

private theorem pair_cutoff (left right : BurnolL2) (supported : left = E (R left)) :
    inner ℂ left (E (R right)) = inner ℂ left right := by
  have actual := congrArg (star : ℂ → ℂ) (cutoff_pair right left supported)
  simpa only [star_def, inner_conj_symm] using actual

private theorem fourier_pair (left : BurnolL2) (right : BurnolQuarterIntervalL2)
    (even : reflectRestricted q right = right) :
    inner ℂ (fourierL2 left) (E right) = inner ℂ left (fourierL2 (E right)) := by
  have reflected : reflectL2 (E right) = E right := by
    change reflectL2 (burnolRadiusZeroExtension q right) = _
    rw [burnolRadiusZeroExtension_reflect, even]
    rfl
  have actual := fourierL2.inner_map_map left (fourierL2 (E right))
  rwa [fourierL2_fourierL2, reflected] at actual

/-- The whole reverse normalization stays in q for both actual cotests, which pays both cutoff removals. -/
theorem uncentered_fourier_pairing (N : ℕ) (positive : 0 < N)
    (left right : BurnolQuarterMeanZeroCarrier)
    (leftEven : reflectRestricted q (left : BurnolQuarterIntervalL2) = left)
    (rightEven : reflectRestricted q (right : BurnolQuarterIntervalL2) = right) :
    inner ℂ (W N (T (left : BurnolQuarterIntervalL2))) (right : BurnolQuarterIntervalL2) =
      inner ℂ (left : BurnolQuarterIntervalL2) (W N (T (right : BurnolQuarterIntervalL2))) := by
  have leftSupport := CenteredCountingDualSupport.source_support left leftEven N positive
  have rightSupport := CenteredCountingDualSupport.source_support right rightEven N positive
  calc
    _ = inner ℂ (FiniteForcing.source N (E (T (left : BurnolQuarterIntervalL2))))
        (E (right : BurnolQuarterIntervalL2)) :=
      (ContinuousLinearMap.adjoint_inner_right R _ _).symm
    _ = inner ℂ (E (T (left : BurnolQuarterIntervalL2)))
        (DualSource.source N (E (right : BurnolQuarterIntervalL2))) := CountingDual.source_pairing N _ _
    _ = inner ℂ (fourierL2 (E (left : BurnolQuarterIntervalL2)))
        (DualSource.source N (E (right : BurnolQuarterIntervalL2))) := cutoff_pair _ _ rightSupport
    _ = inner ℂ (FiniteForcing.source N (fourierL2 (E (left : BurnolQuarterIntervalL2))))
        (E (right : BurnolQuarterIntervalL2)) := (CountingDual.source_pairing N _ _).symm
    _ = inner ℂ (fourierL2 (DualSource.source N (E (left : BurnolQuarterIntervalL2))))
        (E (right : BurnolQuarterIntervalL2)) := by rw [forward_fourier]
    _ = inner ℂ (DualSource.source N (E (left : BurnolQuarterIntervalL2)))
        (fourierL2 (E (right : BurnolQuarterIntervalL2))) := fourier_pair _ _ rightEven
    _ = inner ℂ (DualSource.source N (E (left : BurnolQuarterIntervalL2)))
        (E (T (right : BurnolQuarterIntervalL2))) := (pair_cutoff _ _ leftSupport).symm
    _ = inner ℂ (E (left : BurnolQuarterIntervalL2))
        (FiniteForcing.source N (E (T (right : BurnolQuarterIntervalL2)))) := reverse_pairing N _ _
    _ = _ := ContinuousLinearMap.adjoint_inner_left R _ _

private theorem window_linear (N : ℕ) (left right : BurnolQuarterIntervalL2) (scalar : ℂ) :
    W N (left - scalar • right) = W N left - scalar • W N right := by
  simp only [WindowCounting.windowSource, ← CountingDual.sourceCLM_apply, map_sub, map_smul]

theorem constant_source (N : ℕ) (positive : 0 < N) :
    Constructor.zeroMean (W N (intervalConstant q)) = logarithm := by
  rw [WindowCounting.constant_source N positive, map_add, map_smul, Constructor.zeroMean_constant,
    smul_zero, zero_add]
  rfl

private theorem fourier_mean (state : BurnolQuarterMeanZeroCarrier)
    (even : reflectRestricted q (state : BurnolQuarterIntervalL2) = state) :
    burnolQuarterMeanCoefficient (T (state : BurnolQuarterIntervalL2)) = 2 * inner ℂ constantFourier state := by
  have pairing := ArithmeticAdjoint.counting_fourier_pairing 1 (by norm_num)
    (intervalConstant q) (state : BurnolQuarterIntervalL2) even
  have one (value : BurnolQuarterIntervalL2) : InverseAction.countingWindow 1 value = value := by
    simp only [InverseAction.countingWindow, Real.sqrt_one, Complex.ofReal_one, inv_one,
      Real.log_one, neg_zero, burnolMultiplicativeDilation_zero, one_smul,
      burnolQuarterRestriction_zeroExtension]
  rw [one, one] at pairing
  rw [constantFourier, zeroMean_pair, pairing, burnolQuarterMeanCoefficient,
    Complex.ofReal_pow, burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

private theorem forward_fourier_split (N : ℕ) (positive : 0 < N) (state : BurnolQuarterMeanZeroCarrier) :
    forward N (S state) = Constructor.zeroMean (W N (T (state : BurnolQuarterIntervalL2))) -
      burnolQuarterMeanCoefficient (T (state : BurnolQuarterIntervalL2)) • logarithm := by
  rw [forward, burnolMeanZeroTruncatedFourier_coe, burnolMeanZeroProjection_eq_sub_constant,
    window_linear, map_sub, map_smul, constant_source N positive]

/-- The middle mean projection retains the exact logarithm/sinc rank-two contact of the complete finite program. -/
theorem rank_two_pairing (N : ℕ) (positive : 0 < N)
    (left right : BurnolQuarterMeanZeroCarrier)
    (leftEven : reflectRestricted q (left : BurnolQuarterIntervalL2) = left)
    (rightEven : reflectRestricted q (right : BurnolQuarterIntervalL2) = right) :
    inner ℂ (forward N (S left)) right - inner ℂ left (forward N (S right)) =
      2 * (inner ℂ left logarithm * inner ℂ constantFourier right -
        inner ℂ left constantFourier * inner ℂ logarithm right) := by
  have scaled_left (a : ℂ) (x y : BurnolQuarterMeanZeroCarrier) :
      inner ℂ (a • x) y = star a * inner ℂ x y := by
    exact inner_smul_left x y a
  have scaled_right (a : ℂ) (x y : BurnolQuarterMeanZeroCarrier) :
      inner ℂ x (a • y) = a * inner ℂ x y := by
    exact inner_smul_right x y a
  rw [forward_fourier_split N positive left, forward_fourier_split N positive right,
    inner_sub_left, inner_sub_right, scaled_left, scaled_right,
    zeroMean_pair, pair_zeroMean, uncentered_fourier_pairing N positive left right leftEven rightEven,
    fourier_mean left leftEven, fourier_mean right rightEven]
  simp only [star_mul, star_ofNat, star_def, inner_conj_symm]
  ring

/-- The contact is read on the actual forward/reverse commutator, not on an assumed symmetric replacement. -/
theorem commutator_pairing (N : ℕ) (positive : 0 < N)
    (left right : BurnolQuarterMeanZeroCarrier)
    (leftEven : reflectRestricted q (left : BurnolQuarterIntervalL2) = left)
    (rightEven : reflectRestricted q (right : BurnolQuarterIntervalL2) = right) :
    inner ℂ (forward N (S left) - S (reverse N left)) right =
      2 * (inner ℂ left logarithm * inner ℂ constantFourier right -
        inner ℂ left constantFourier * inner ℂ logarithm right) := by
  have fourier := OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection
    (reverse N left) right rightEven
  have reversed := congrArg (star : ℂ → ℂ) (source_pairing N (S right) left)
  simp only [star_def, inner_conj_symm] at reversed
  rw [inner_sub_left, fourier, ← reversed]
  exact rank_two_pairing N positive left right leftEven rightEven

theorem original_pairing (N : ℕ) (positive : 0 < N)
    (left right : BurnolCompletedMellinCoordinate) :
    inner ℂ (forward N (Constructor.returnState left) - S (reverse N (burnolRieszSingleFourierSource left)))
      (burnolRieszSingleFourierSource right) =
      2 * (inner ℂ (burnolRieszSingleFourierSource left) logarithm *
          inner ℂ constantFourier (burnolRieszSingleFourierSource right) -
        inner ℂ (burnolRieszSingleFourierSource left) constantFourier *
          inner ℂ logarithm (burnolRieszSingleFourierSource right)) :=
  commutator_pairing N positive _ _ (burnolRieszSingleFourierSource_reflection_fixed left)
    (burnolRieszSingleFourierSource_reflection_fixed right)

theorem forward_zero (state : BurnolQuarterMeanZeroCarrier) : forward 0 state = 0 := by
  simp [forward, WindowCounting.windowSource, FiniteForcing.source, ContinuousChannels.normalization]

theorem reverse_zero (state : BurnolQuarterMeanZeroCarrier) : reverse 0 state = 0 := by
  simp [reverse, DualSource.source]

end
end OriginalRieszFinitePairing.CoPoisson.Ward.CenteredCountingDual
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
