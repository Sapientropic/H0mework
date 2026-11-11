import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CenteredCountingDual
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSourceGram
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountingEnergy
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalRieszSourceGreen OriginalPaPhysicalGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "C" => CenteredCountingDual.forward
local notation "B" => CenteredCountingDual.reverse
local notation "ell" => CenteredCountingDual.logarithm

local instance : CompleteSpace M := IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def outside (N : ℕ) (state : M) : BurnolL2 :=
  FiniteForcing.source N (E (state : Hq)) - E (R (FiniteForcing.source N (E (state : Hq))))

def head (N : ℕ) (state : M) : ℂ :=
  inner ℂ (DualSource.source N ConstantDual.seed) (E (state : Hq))

private theorem constant_norm : ‖intervalConstant q‖ ^ 2 = (1 / 2 : ℝ) := by
  have actual : ‖intervalConstant q‖ ^ 2 = (2 * q : ℝ) := by
    exact_mod_cast burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)
  norm_num at actual
  exact actual

private theorem centered_norm (state : Hq) :
    ‖state‖ ^ 2 = ‖Constructor.zeroMean state‖ ^ 2 + (1 / 2 : ℝ) * ‖burnolQuarterMeanCoefficient state‖ ^ 2 := by
  have orth : inner ℂ (Constructor.zeroMean state : Hq)
      (burnolQuarterMeanCoefficient state • intervalConstant q) = 0 := by
    rw [inner_smul_right]
    have zero : inner ℂ (intervalConstant q) (Constructor.zeroMean state : Hq) = 0 :=
      (Submodule.mem_orthogonal _ _).mp (Constructor.zeroMean state).property _ (Submodule.mem_span_singleton_self _)
    rw [inner_eq_zero_symm.mpr zero, mul_zero]
  have actual := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orth
  simp only [← sq] at actual
  have split : (Constructor.zeroMean state : Hq) + burnolQuarterMeanCoefficient state • intervalConstant q = state := by
    rw [Constructor.zeroMean_read, sub_add_cancel]
  rw [split, norm_smul, mul_pow, constant_norm] at actual
  exact actual.trans (by change _ = ‖(Constructor.zeroMean state : Hq)‖ ^ 2 + _; ring)

private theorem extension_norm (state : Hq) : ‖E state‖ ^ 2 = ‖state‖ ^ 2 := by
  have actual := quarter_extension_inner state state
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at actual
  exact_mod_cast actual

private theorem window_norm (value : BurnolL2) :
    ‖value‖ ^ 2 = ‖R value‖ ^ 2 + ‖value - E (R value)‖ ^ 2 := by
  have orth : inner ℂ (E (R value)) (value - E (R value)) = 0 := by
    have pair : inner ℂ (E (R value)) value = inner ℂ (R value) (R value) :=
      ContinuousLinearMap.adjoint_inner_left R value (R value)
    rw [inner_sub_right, pair, quarter_extension_inner, sub_self]
  have actual := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ orth
  simp only [← sq] at actual
  rw [add_sub_cancel, extension_norm] at actual
  exact actual

private theorem mean_pair (state : Hq) :
    burnolQuarterMeanCoefficient state = 2 * inner ℂ (intervalConstant q) state := by
  unfold burnolQuarterMeanCoefficient
  rw [Complex.ofReal_pow, burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ) < q)]
  norm_num
  ring

private theorem forward_mean (N : ℕ) (state : M) :
    burnolQuarterMeanCoefficient (R (FiniteForcing.source N (E (state : Hq)))) = 2 * head N state := by
  rw [mean_pair]
  congr 1
  have first : inner ℂ (intervalConstant q) (R (FiniteForcing.source N (E (state : Hq)))) =
      inner ℂ ConstantDual.seed (FiniteForcing.source N (E (state : Hq))) :=
    (ContinuousLinearMap.adjoint_inner_left R _ _).symm
  rw [first]
  change inner ℂ ConstantDual.seed (FiniteForcing.source N (E (state : Hq))) = _
  unfold head
  rw [CountingDual.dual_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_left (CountingDual.sourceCLM N) _ _).symm

private theorem reverse_mean (N : ℕ) (positive : 0 < N) (state : M) :
    burnolQuarterMeanCoefficient (R (DualSource.source N (E (state : Hq)))) = 2 * inner ℂ ell state := by
  rw [mean_pair]
  congr 1
  have first : inner ℂ (intervalConstant q) (R (DualSource.source N (E (state : Hq)))) =
      inner ℂ (WindowCounting.windowSource N (intervalConstant q)) (state : Hq) := by
    calc
      _ = inner ℂ ConstantDual.seed (DualSource.source N (E (state : Hq))) :=
        (ContinuousLinearMap.adjoint_inner_left R _ _).symm
      _ = inner ℂ (FiniteForcing.source N ConstantDual.seed) (E (state : Hq)) := (CountingDual.source_pairing N _ _).symm
      _ = _ := ContinuousLinearMap.adjoint_inner_right R _ _
  rw [first, WindowCounting.constant_source N positive, inner_add_left, inner_smul_left]
  have meanZero : inner ℂ (intervalConstant q) (state : Hq) = 0 :=
    (Submodule.mem_orthogonal _ _).mp state.property _ (Submodule.mem_span_singleton_self _)
  rw [meanZero, mul_zero, zero_add]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right state SmallScaleLog.logL2).symm

/-- Ambient normality pays the full off-window square and both unequal mean corrections. -/
theorem source_norm (N : ℕ) (positive : 0 < N) (state : M)
    (even : reflectRestricted q (state : Hq) = state) :
    ‖B N state‖ ^ 2 - ‖C N state‖ ^ 2 =
      ‖outside N state‖ ^ 2 + 2 * ‖head N state‖ ^ 2 - 2 * ‖inner ℂ ell state‖ ^ 2 := by
  have normal := DualSourceGram.finite_gram N (E (state : Hq)) (E (state : Hq))
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at normal
  have norms : ‖FiniteForcing.source N (E (state : Hq))‖ ^ 2 =
      ‖DualSource.source N (E (state : Hq))‖ ^ 2 := by exact_mod_cast normal
  have support := CenteredCountingDualSupport.source_support state even N positive
  have reverseNorm : ‖DualSource.source N (E (state : Hq))‖ ^ 2 =
      ‖R (DualSource.source N (E (state : Hq)))‖ ^ 2 := by
    conv_lhs => rw [support]
    exact extension_norm _
  have direct := window_norm (FiniteForcing.source N (E (state : Hq)))
  have first := centered_norm (R (FiniteForcing.source N (E (state : Hq))))
  have second := centered_norm (R (DualSource.source N (E (state : Hq))))
  rw [forward_mean, norm_mul] at first
  rw [reverse_mean N positive, norm_mul] at second
  norm_num at first second
  change _ = ‖C N state‖ ^ 2 + _ at first
  change _ = ‖B N state‖ ^ 2 + (1 / 2 : ℝ) * (2 * ‖inner ℂ ell state‖) ^ 2 at second
  change _ = _ + ‖outside N state‖ ^ 2 at direct
  nlinarith

/-- The square is the actual q-exterior part of the same complete finite forward source. -/
theorem outside_norm (N : ℕ) (state : M) :
    ‖outside N state‖ ^ 2 = ∫ x : ℝ in (symmetricInterval q)ᶜ,
      ‖FiniteForcing.source N (E (state : Hq)) x‖ ^ 2 := by
  rw [burnolL2_norm_sq_eq_integral_norm_sq, ← integral_indicator (measurableSet_symmetricInterval q).compl]
  apply integral_congr_ae
  let source := FiniteForcing.source N (E (state : Hq))
  filter_upwards [Lp.coeFn_sub source (E (R source)), originalPhysicalCutoff_coeFn q source] with x subAt cutAt
  change ‖(source - E (R source)) x‖ ^ 2 = _
  rw [subAt]
  change ‖source x - E (R source) x‖ ^ 2 = _
  change E (R source) x = _ at cutAt
  rw [cutAt]
  by_cases inside : x ∈ symmetricInterval q
  · simp only [indicator_of_mem inside, indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from fun h => h inside), sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · simp only [indicator_of_notMem inside, indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside), sub_zero]
    rfl

/-- Both original inverse inputs consume the same N and their source-generated parity. -/
theorem original_norms (N : ℕ) (positive : 0 < N) (coordinate : BurnolCompletedMellinCoordinate) :
    let b := burnolRieszSingleFourierSource coordinate
    let r := Constructor.returnState coordinate
    (‖B N b‖ ^ 2 - ‖C N b‖ ^ 2) + (‖B N r‖ ^ 2 - ‖C N r‖ ^ 2) =
      (‖outside N b‖ ^ 2 + 2 * ‖head N b‖ ^ 2 - 2 * ‖inner ℂ ell b‖ ^ 2) +
      (‖outside N r‖ ^ 2 + 2 * ‖head N r‖ ^ 2 - 2 * ‖inner ℂ ell r‖ ^ 2) := by
  dsimp only
  rw [source_norm N positive _ (burnolRieszSingleFourierSource_reflection_fixed coordinate),
    source_norm N positive (Constructor.returnState coordinate) (burnolRieszSingleFourierReturn_reflection_fixed coordinate)]
end
end OriginalRieszFinitePairing.CoPoisson.Ward.CountingEnergy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
