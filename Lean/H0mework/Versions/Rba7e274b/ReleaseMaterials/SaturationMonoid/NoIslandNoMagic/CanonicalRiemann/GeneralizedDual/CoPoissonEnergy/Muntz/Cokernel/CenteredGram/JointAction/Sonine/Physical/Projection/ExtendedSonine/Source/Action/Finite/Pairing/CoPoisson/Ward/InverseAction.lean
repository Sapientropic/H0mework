import H0mework.Versions.V2.Arithmetic.RieszEuler.Solve
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.WindowEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction

open Complex Filter FourierTransform MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszSource

noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

def rawMean (raw : ℝ → ℂ) : ℂ := 2 * ∫ x : ℝ, raw x ∂μq

def centeredRaw (raw : ℝ → ℂ) (x : ℝ) : ℂ := raw x - rawMean raw

def squareRaw (raw : ℝ → ℂ) : ℝ → ℂ :=
  centeredRaw (Constructor.fourierRaw (centeredRaw (Constructor.fourierRaw raw)))

def countingWindow (scale : ℝ) (state : BurnolQuarterIntervalL2) : BurnolQuarterIntervalL2 :=
  (Real.sqrt scale : ℂ)⁻¹ • burnolQuarterRestriction
    (burnolMultiplicativeDilation (-Real.log scale) (burnolQuarterZeroExtension state))

def countingRaw (scale : ℝ) (raw : ℝ → ℂ) (x : ℝ) : ℂ :=
  (scale : ℂ)⁻¹ * (symmetricInterval q).indicator raw (x / scale)

def centeredCounting (scale : ℝ) (state : BurnolQuarterMeanZeroCarrier) :
    BurnolQuarterMeanZeroCarrier :=
  Constructor.zeroMean (countingWindow scale (state : BurnolQuarterIntervalL2))

theorem meanZeroFourier_raw (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    burnolMeanZeroFourierRaw state = centeredRaw (Constructor.fourierRaw raw) := by
  have fourier := Constructor.fourierRaw_congr _ _ represents
  have mean := Constructor.mean_integral (burnolTruncatedFourier (state : BurnolQuarterIntervalL2))
  rw [integral_congr_ae (Constructor.truncatedFourier_read _), fourier] at mean
  funext x
  unfold burnolMeanZeroFourierRaw centeredRaw rawMean
  rw [← Constructor.fourierRaw_state, fourier, mean]

theorem square_raw (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    burnolMeanZeroFourierRaw (burnolMeanZeroTruncatedFourier state) = squareRaw raw := by
  have first : (burnolMeanZeroTruncatedFourier state : ℝ → ℂ) =ᵐ[μq]
      centeredRaw (Constructor.fourierRaw raw) := by
    rw [← meanZeroFourier_raw state raw represents]
    exact burnolMeanZeroFourier_ae_raw state
  exact meanZeroFourier_raw _ _ first

private theorem sqrt_exp (scale : ℝ) (positive : 0 < scale) :
    Real.sqrt scale = Real.exp (Real.log scale / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos positive]
  congr 1
  ring

theorem countingWindow_raw (scale : ℝ) (positive : 0 < scale)
    (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (countingWindow scale state : ℝ → ℂ) =ᵐ[μq] countingRaw scale raw := by
  let source := burnolQuarterZeroExtension state
  have sourceRead : (source : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator raw := by
    have localRead := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp represents
    filter_upwards [burnolQuarterZeroExtension_coe state, localRead] with x extended actual
    rw [extended]
    by_cases inside : x ∈ symmetricInterval q
    · rw [indicator_of_mem inside, indicator_of_mem inside, actual inside]
    · rw [indicator_of_notMem inside, indicator_of_notMem inside]
  have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (r := Real.exp (-Real.log scale)) (Real.exp_ne_zero _)
  have movedRead : ∀ᵐ x : ℝ ∂volume,
      source (Real.exp (-Real.log scale) * x) =
        (symmetricInterval q).indicator raw (Real.exp (-Real.log scale) * x) := by
    simpa only [smul_eq_mul] using qmp.ae sourceRead
  have amplitude : (Real.sqrt scale)⁻¹ * Real.exp (-Real.log scale / 2) = scale⁻¹ := by
    rw [sqrt_exp scale positive, ← Real.exp_neg, ← Real.exp_add,
      show -(Real.log scale / 2) + -Real.log scale / 2 = -Real.log scale by ring,
      Real.exp_neg, Real.exp_log positive]
  filter_upwards [Lp.coeFn_smul (Real.sqrt scale : ℂ)⁻¹
    (burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log scale) source)),
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (burnolMultiplicativeDilation (-Real.log scale) source),
    ae_restrict_of_ae (s := symmetricInterval q)
      (burnolMultiplicativeDilation_coeFn (-Real.log scale) source),
    ae_restrict_of_ae (s := symmetricInterval q) movedRead] with x scaled restricted dilated moved
  change ((Real.sqrt scale : ℂ)⁻¹ •
    burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log scale) source) :
      BurnolQuarterIntervalL2) x = _
  rw [scaled]
  change (Real.sqrt scale : ℂ)⁻¹ *
    burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log scale) source) x = _
  change burnolQuarterRestriction (burnolMultiplicativeDilation (-Real.log scale) source) x = _
    at restricted
  rw [restricted, dilated]
  unfold burnolL2RawNormalizedDilation
  rw [moved, ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, amplitude,
    Complex.ofReal_inv, Real.exp_neg, Real.exp_log positive]
  simp only [countingRaw, div_eq_mul_inv, mul_comm]

private theorem zeroMean_raw (state : BurnolQuarterIntervalL2) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (Constructor.zeroMean state : ℝ → ℂ) =ᵐ[μq] centeredRaw raw := by
  have mean : burnolQuarterMeanCoefficient state = rawMean raw := by
    rw [Constructor.mean_integral, integral_congr_ae represents]
    rfl
  change ((Constructor.zeroMean state : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] _
  rw [Constructor.zeroMean_read]
  filter_upwards [Lp.coeFn_sub state (burnolQuarterMeanCoefficient state • intervalConstant q),
    Lp.coeFn_smul (burnolQuarterMeanCoefficient state) (intervalConstant q), represents,
    intervalConstant_coeFn q] with x subAt scaled actual constant
  rw [subAt]
  change state x - (burnolQuarterMeanCoefficient state • intervalConstant q : BurnolQuarterIntervalL2) x = _
  rw [scaled]
  change state x - burnolQuarterMeanCoefficient state * intervalConstant q x = _
  rw [actual, mean, constant, mul_one]
  rfl

theorem centeredCounting_raw (scale : ℝ) (positive : 0 < scale)
    (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    (centeredCounting scale state : ℝ → ℂ) =ᵐ[μq] centeredRaw (countingRaw scale raw) :=
  zeroMean_raw _ _ (countingWindow_raw scale positive _ raw represents)

/-- The Fourier side uses precisely the overlap of the original q-window
with its q/scale window. This is a finite change of variables, with no tail swap. -/
theorem counting_fourier_overlap (scale : ℝ) (positive : 0 < scale)
    (raw : ℝ → ℂ) (frequency : ℝ) :
    Constructor.fourierRaw (countingRaw scale raw) frequency =
      ∫ y : ℝ in (-q / scale)..(q / scale),
        Constructor.phase frequency (scale * y) * (symmetricInterval q).indicator raw y := by
  rw [Constructor.fourierRaw_integral]
  let integrand := fun y : ℝ =>
    Constructor.phase frequency (scale * y) * (symmetricInterval q).indicator raw y
  calc
    _ = (scale : ℂ)⁻¹ * ∫ y : ℝ in (-q)..q, integrand (y / scale) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y _
      dsimp only [integrand, countingRaw]
      rw [mul_div_cancel₀ y positive.ne']
      ring
    _ = _ := by
      simpa only [Complex.real_smul, Complex.ofReal_inv] using
        (intervalIntegral.inv_smul_integral_comp_div (f := integrand) (a := -q) (b := q) scale)

/-- Both sides of the actual square commutator are evaluated through the
original finite Fourier integral, overlap indicator and every mean projection. -/
theorem square_commutator_raw (scale : ℝ) (positive : 0 < scale)
    (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ → ℂ)
    (represents : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    ((centeredCounting scale (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier state)) -
        burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (centeredCounting scale state)) :
      BurnolQuarterMeanZeroCarrier) : ℝ → ℂ) =ᵐ[μq]
      fun x => centeredRaw (countingRaw scale (squareRaw raw)) x -
        squareRaw (centeredRaw (countingRaw scale raw)) x := by
  have squareRead : (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier state) :
      ℝ → ℂ) =ᵐ[μq] squareRaw raw := by
    rw [← square_raw state raw represents]
    exact burnolMeanZeroFourier_ae_raw _
  have first := centeredCounting_raw scale positive _ _ squareRead
  have moved := centeredCounting_raw scale positive state raw represents
  have second : (burnolMeanZeroTruncatedFourier
      (burnolMeanZeroTruncatedFourier (centeredCounting scale state)) : ℝ → ℂ) =ᵐ[μq]
        squareRaw (centeredRaw (countingRaw scale raw)) := by
    rw [← square_raw _ _ moved]
    exact burnolMeanZeroFourier_ae_raw _
  exact (Lp.coeFn_sub _ _).trans (first.sub second)

/-- The exact input of the inverse equation supplies this commutator;
there is no endpoint or zero-value premise. -/
theorem original_source_square_commutator (coordinate : BurnolCompletedMellinCoordinate)
    (scale : ℝ) (positive : 0 < scale) :
    ((centeredCounting scale (burnolMeanZeroTruncatedFourier
          (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate))) -
        burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier
          (centeredCounting scale (burnolRieszSingleFourierSource coordinate))) :
      BurnolQuarterMeanZeroCarrier) : ℝ → ℂ) =ᵐ[μq]
      fun x => centeredRaw (countingRaw scale (squareRaw (burnolRieszSingleFourierSourceRaw coordinate))) x -
        squareRaw (centeredRaw (countingRaw scale (burnolRieszSingleFourierSourceRaw coordinate))) x :=
  square_commutator_raw scale positive _ _ (burnolRieszSingleFourierSource_ae_raw coordinate)

theorem original_inverse_raw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    squareRaw (burnolRieszSingleFourierSourceRaw coordinate) x =
      burnolRieszSingleFourierSourceRaw coordinate x - burnolRieszFourierForcingRaw coordinate x := by
  rw [← square_raw (burnolRieszSingleFourierSource coordinate)
    (burnolRieszSingleFourierSourceRaw coordinate) (burnolRieszSingleFourierSource_ae_raw coordinate)]
  unfold burnolRieszSingleFourierSourceRaw
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward.InverseAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
