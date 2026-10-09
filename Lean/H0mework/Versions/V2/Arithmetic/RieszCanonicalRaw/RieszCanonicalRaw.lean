import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource
/-!
# Canonical raw Riesz state from the single Fourier source

All appearances of an interval L² source occur under its canonical Fourier
integral or a continuous mean functional.  The final raw state is generated
from the gap/tail formula and binds the actual Riesz vector almost everywhere.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace
noncomputable section

local instance rawSourceConstantComplete :
    CompleteSpace (intervalConstantLine (1 / 4 : ℝ)) := by
  apply IsComplete.completeSpace_coe
  exact (intervalConstantLine_isClosed (1 / 4 : ℝ)).isComplete

def burnolQuarterMeanCoefficient (value : BurnolQuarterIntervalL2) : ℂ :=
  inner ℂ (intervalConstant (1 / 4 : ℝ)) value /
    ((‖intervalConstant (1 / 4 : ℝ)‖ ^ 2 : ℝ) : ℂ)

theorem burnolMeanZeroProjection_eq_sub_constant (value : BurnolQuarterIntervalL2) :
    burnolQuarterMeanZeroProjection value =
      value - burnolQuarterMeanCoefficient value • intervalConstant (1 / 4 : ℝ) := by
  change (intervalConstantLine (1 / 4 : ℝ)).orthogonal.starProjection value = _
  rw [Submodule.starProjection_orthogonal_val]
  change value - (ℂ ∙ intervalConstant (1 / 4 : ℝ)).starProjection value = _
  rw [Submodule.starProjection_singleton]
  rfl

def burnolMeanZeroFourierRaw (state : BurnolQuarterMeanZeroCarrier) (u : ℝ) : ℂ :=
  burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ) (state : BurnolQuarterIntervalL2) u -
    burnolQuarterMeanCoefficient (burnolTruncatedFourier (state : BurnolQuarterIntervalL2))

theorem burnolMeanZeroFourier_ae_raw (state : BurnolQuarterMeanZeroCarrier) :
    (burnolMeanZeroTruncatedFourier state : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] burnolMeanZeroFourierRaw state := by
  let base := burnolTruncatedFourier (state : BurnolQuarterIntervalL2)
  have baseRead : (base : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ) (state : BurnolQuarterIntervalL2) := by
    have restriction := LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ))
      (fourierL2 (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2)))
    have fourierRead := ae_restrict_of_ae (s := symmetricInterval (1 / 4 : ℝ))
      (burnolRadiusFourierL2_zeroExtension_ae_eq_raw (state : BurnolQuarterIntervalL2))
    exact restriction.trans fourierRead
  have projected :
      (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) =
        base - burnolQuarterMeanCoefficient base • intervalConstant (1 / 4 : ℝ) :=
    burnolMeanZeroProjection_eq_sub_constant base
  change ((burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[_] _
  rw [projected]
  filter_upwards [Lp.coeFn_sub base
      (burnolQuarterMeanCoefficient base • intervalConstant (1 / 4 : ℝ)),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient base) (intervalConstant (1 / 4 : ℝ)),
    baseRead, intervalConstant_coeFn (1 / 4 : ℝ)] with x hsub hsmul hbase hconstant
  rw [hsub]
  change base x -
    (burnolQuarterMeanCoefficient base • intervalConstant (1 / 4 : ℝ) : BurnolQuarterIntervalL2) x = _
  rw [hsmul]
  change base x - burnolQuarterMeanCoefficient base * intervalConstant (1 / 4 : ℝ) x = _
  rw [hbase, hconstant, mul_one]
  rfl

theorem burnolZeroExtensionMeanZeroFourier_ae_raw (state : BurnolQuarterMeanZeroCarrier) :
    (burnolQuarterZeroExtension
        (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval (1 / 4 : ℝ)).indicator (burnolMeanZeroFourierRaw state) := by
  have raw := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp
    (burnolMeanZeroFourier_ae_raw state)
  filter_upwards [burnolRadiusZeroExtension_coe
    (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2), raw] with x he hraw
  change burnolRadiusZeroExtension (1 / 4 : ℝ)
    (burnolMeanZeroTruncatedFourier state : BurnolQuarterIntervalL2) x = _
  rw [he]
  by_cases hx : x ∈ symmetricInterval (1 / 4 : ℝ)
  · simp only [Set.indicator_of_mem hx]
    exact hraw hx
  · simp only [Set.indicator_of_notMem hx]

def burnolGapRieszRaw (radius : ℝ) (x : ℝ) : ℂ :=
  star ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹) *
    (symmetricInterval radius).indicator (fun _ : ℝ => (1 : ℂ)) x

theorem burnolGapRiesz_ae_raw (radius : ℝ) :
    (burnolAmbientGapRieszVector radius : ℝ → ℂ) =ᵐ[volume] burnolGapRieszRaw radius := by
  let c : ℂ := star ((‖intervalConstant radius‖ ^ 2 : ℂ)⁻¹)
  let extension := burnolRadiusZeroExtension radius (intervalConstant radius)
  have constantRead := (ae_restrict_iff' (measurableSet_symmetricInterval radius)).mp
    (intervalConstant_coeFn radius)
  change ((c • extension : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul c extension,
    burnolRadiusZeroExtension_coe (intervalConstant radius), constantRead]
    with x scaled extended constant
  rw [scaled]
  change c * burnolRadiusZeroExtension radius (intervalConstant radius) x = _
  rw [extended]
  by_cases hx : x ∈ symmetricInterval radius
  · simp only [burnolGapRieszRaw, Set.indicator_of_mem hx, constant hx]
    rfl
  · simp only [burnolGapRieszRaw, Set.indicator_of_notMem hx, mul_zero]

def burnolAmbientMellinKernelRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value) *
      burnolGapRieszRaw (1 / 4 : ℝ) x +
    burnolRadiusMellinTailKernelRaw (1 / 4 : ℝ) coordinate.value x

theorem burnolAmbientMellinKernel_ae_raw (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolAmbientCompletedMellinKernelFormula coordinate : ℝ → ℂ) =ᵐ[volume]
      burnolAmbientMellinKernelRaw coordinate := by
  let c := star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value)
  let gap := burnolAmbientGapRieszVector (1 / 4 : ℝ)
  let tail := burnolRadiusMellinTailKernelL2 (1 / 4 : ℝ) (by norm_num)
    coordinate.value coordinate.rightHalf
  change ((c • gap + tail : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  have rawTail : (tail : ℝ → ℂ) =ᵐ[volume]
      burnolRadiusMellinTailKernelRaw (1 / 4 : ℝ) coordinate.value :=
    MemLp.coeFn_toLp
      (burnolRadiusMellinTailKernelRaw_memLp (by norm_num) coordinate.value coordinate.rightHalf)
  filter_upwards [Lp.coeFn_add (c • gap) tail, Lp.coeFn_smul c gap,
    burnolGapRiesz_ae_raw (1 / 4 : ℝ), rawTail] with x ha hs hg ht
  rw [ha]
  change (c • gap : BurnolL2) x + tail x = _
  rw [hs]
  change c * burnolAmbientGapRieszVector (1 / 4 : ℝ) x + tail x = _
  rw [hg, ht]
  rfl

def burnolEvenRaw (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (raw x + raw (-x))

theorem burnolEvenRaw_ae (value : BurnolL2) (raw : ℝ → ℂ)
    (read : (value : ℝ → ℂ) =ᵐ[volume] raw) :
    (burnolAmbientEvenPart value : ℝ → ℂ) =ᵐ[volume]
      burnolEvenRaw raw := by
  unfold burnolAmbientEvenPart burnolEvenRaw
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (value + reflectL2 value),
    Lp.coeFn_add value (reflectL2 value),
    Lp.coeFn_compMeasurePreserving value negMeasurePreserving,
    read, negMeasurePreserving.quasiMeasurePreserving.ae read] with x hs ha hr hv hn
  rw [hs]
  change (1 / 2 : ℂ) * (value + reflectL2 value : BurnolL2) x = _
  rw [ha]
  change (1 / 2 : ℂ) * (value x + reflectL2 value x) = _
  change reflectL2 value x = value (-x) at hr
  rw [hr, hv, hn]

def burnolRieszCorrectionRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (symmetricInterval (1 / 4 : ℝ)).indicator
      (burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)) x -
    burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x

/-- A source-chosen representative, using only the explicit gap/tail and
finite-interval Fourier integrals.  No L² point representative is selected. -/

def burnolRieszStateRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
      (burnolAmbientMellinKernelRaw coordinate x + burnolAmbientMellinKernelRaw coordinate (-x)) +
    (1 / 2 : ℂ) *
      (burnolRieszCorrectionRaw coordinate x + burnolRieszCorrectionRaw coordinate (-x))

theorem burnolRieszState_ae_raw (coordinate : BurnolCompletedMellinCoordinate) :
    ((burnolCompletedMellinRieszVector coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolRieszStateRaw coordinate := by
  let b := burnolRieszSingleFourierSource coordinate
  let first := burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2)
  let second := fourierL2 (burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2))
  have correctionRead : ((first - second : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolRieszCorrectionRaw coordinate := by
    filter_upwards [Lp.coeFn_sub first second,
      burnolZeroExtensionMeanZeroFourier_ae_raw b,
      burnolRadiusFourierL2_zeroExtension_ae_eq_raw (b : BurnolQuarterIntervalL2)]
      with x hsub hfirst hsecond
    rw [hsub]
    change first x - second x = _
    change first x = _ at hfirst
    change second x = _ at hsecond
    rw [hfirst, hsecond]
    rfl
  rw [burnolCompletedMellinRieszVector_eq_singleFourierSource]
  change ((burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate) +
    burnolAmbientEvenPart (first - second) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add
      (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))
      (burnolAmbientEvenPart (first - second)),
    burnolEvenRaw_ae _ _ (burnolAmbientMellinKernel_ae_raw coordinate),
    burnolEvenRaw_ae (first - second) _ correctionRead] with x added kernel correction
  rw [added]
  change burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate) x +
    burnolAmbientEvenPart (first - second) x = _
  rw [kernel, correction]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
