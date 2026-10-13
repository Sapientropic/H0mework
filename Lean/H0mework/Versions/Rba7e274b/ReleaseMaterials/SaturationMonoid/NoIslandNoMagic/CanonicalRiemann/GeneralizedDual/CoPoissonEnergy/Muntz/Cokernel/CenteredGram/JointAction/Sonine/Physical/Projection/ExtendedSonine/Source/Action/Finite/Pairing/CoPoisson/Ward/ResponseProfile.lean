import H0mework.Versions.V2.Arithmetic.RieszSourceKernel.Core
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RegularQuadrature

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ResponseProfile

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

local instance : IsFiniteMeasure μq where
  measure_univ_lt_top := lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top q)

def etaMean : ℂ := burnolQuarterMeanCoefficient (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))
def etaRaw (x : ℝ) : ℂ := Edge.raw q x - etaMean
def vRaw : ℝ → ℂ := burnolMeanZeroFourierRaw Response.u
def uRaw (x : ℝ) : ℂ := etaRaw x + burnolMeanZeroFourierRaw Response.v x

private theorem meanFourier_continuous (state : BurnolQuarterMeanZeroCarrier) :
    Continuous (burnolMeanZeroFourierRaw state) :=
  (burnolRadiusTruncatedFourierRaw_continuous (state : BurnolQuarterIntervalL2)).sub continuous_const

theorem eta_continuous : Continuous etaRaw := (Edge.raw_continuous q).sub continuous_const
theorem u_continuous : Continuous uRaw := eta_continuous.add (meanFourier_continuous Response.v)
theorem v_continuous : Continuous vRaw := meanFourier_continuous Response.u

theorem eta_read : (Response.eta : ℝ → ℂ) =ᵐ[μq] etaRaw := by
  have actual : (Response.eta : BurnolQuarterIntervalL2) =
      Constructor.compact (Edge.raw q) (Edge.raw_continuous q) - etaMean • intervalConstant q := by
    unfold etaMean
    rw [← Constructor.zeroMean_read, Edge.zeroMean_raw_eq_endpointColumns]
    rfl
  change ((Response.eta : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] _
  rw [actual]
  filter_upwards [Lp.coeFn_sub (Constructor.compact (Edge.raw q) (Edge.raw_continuous q))
      (etaMean • intervalConstant q), Lp.coeFn_smul etaMean (intervalConstant q),
    Constructor.compact_read (Edge.raw q) (Edge.raw_continuous q), intervalConstant_coeFn q]
    with x difference scalar raw constant
  rw [difference, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, raw, constant, mul_one]
  rfl

theorem v_read : (Response.v : ℝ → ℂ) =ᵐ[μq] vRaw := burnolMeanZeroFourier_ae_raw Response.u

theorem u_read : (Response.u : ℝ → ℂ) =ᵐ[μq] uRaw := by
  have actual : (Response.u : BurnolQuarterIntervalL2) =
      (Response.eta : BurnolQuarterIntervalL2) +
        (burnolMeanZeroTruncatedFourier Response.v : BurnolQuarterIntervalL2) := by
    have source := congrArg (fun value : BurnolQuarterMeanZeroCarrier => (value : BurnolQuarterIntervalL2))
      Response.source_pair_equation
    exact sub_eq_iff_eq_add.mp source
  change ((Response.u : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[μq] _
  rw [actual]
  filter_upwards [Lp.coeFn_add (Response.eta : BurnolQuarterIntervalL2)
      (burnolMeanZeroTruncatedFourier Response.v : BurnolQuarterIntervalL2),
    eta_read, burnolMeanZeroFourier_ae_raw Response.v] with x addition eta fourier
  rw [addition, Pi.add_apply, eta, fourier]
  rfl

private theorem fourier_profile (state : BurnolQuarterMeanZeroCarrier) (raw : ℝ → ℂ)
    (read : (state : ℝ → ℂ) =ᵐ[μq] raw) :
    burnolMeanZeroFourierRaw state = fun x => Constructor.fourierRaw raw x -
      burnolQuarterMeanCoefficient (burnolTruncatedFourier (state : BurnolQuarterIntervalL2)) := by
  have actual := Constructor.fourierRaw_congr _ _ read
  funext x
  change Constructor.fourierRaw (state : BurnolQuarterIntervalL2) x - _ = _
  rw [actual]

def etaSlope (x : ℝ) : ℂ :=
  (q : ℂ) * ((-2 * (Real.pi : ℂ) * I * (q : ℂ) * Constructor.phase q x) +
    (-2 * (Real.pi : ℂ) * I * (-q : ℂ) * Constructor.phase (-q) x)) -
      Constructor.fourierDerivative (fun _ : ℝ => (1 : ℂ)) x

private theorem edge_derivative (x : ℝ) : HasDerivAt (Edge.raw q) (etaSlope x) x := by
  have constantRaw := Constructor.fourierRaw_congr _ _ (intervalConstant_coeFn q)
  have actual : Edge.raw q = fun x => (q : ℂ) * (Constructor.phase q x + Constructor.phase (-q) x) -
      Constructor.fourierRaw (fun _ : ℝ => (1 : ℂ)) x := by
    funext t
    change (q : ℂ) * (Constructor.phase q t + Constructor.phase (-q) t) -
      Constructor.fourierRaw (intervalConstant q) t = _
    rw [constantRaw]
  rw [actual]
  convert! (((Constructor.phase_derivative q x).add (Constructor.phase_derivative (-q) x)).const_mul
    (q : ℂ)).sub (Constructor.fourierRaw_hasDerivAt (fun _ : ℝ => (1 : ℂ)) continuous_const x) using 1
  simp only [etaSlope, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat]

theorem eta_derivative (x : ℝ) : HasDerivAt etaRaw (etaSlope x) x := (edge_derivative x).sub_const _

theorem eta_slope_continuous : Continuous etaSlope := by
  unfold etaSlope
  exact (continuous_const.mul ((continuous_const.mul (Constructor.phaseContinuous q)).add
    (continuous_const.mul (Constructor.phaseContinuous (-q))))).sub
      (Constructor.fourierDerivative_continuous _ continuous_const)

def uSlope (x : ℝ) : ℂ := etaSlope x + Constructor.fourierDerivative vRaw x
def vSlope : ℝ → ℂ := Constructor.fourierDerivative uRaw

theorem u_derivative (x : ℝ) : HasDerivAt uRaw (uSlope x) x := by
  unfold uRaw
  rw [fourier_profile Response.v vRaw v_read]
  exact (eta_derivative x).add ((Constructor.fourierRaw_hasDerivAt vRaw v_continuous x).sub_const _)

theorem v_derivative (x : ℝ) : HasDerivAt vRaw (vSlope x) x := by
  unfold vRaw
  rw [fourier_profile Response.u uRaw u_read]
  exact (Constructor.fourierRaw_hasDerivAt uRaw u_continuous x).sub_const _

theorem u_slope_continuous : Continuous uSlope :=
  eta_slope_continuous.add (Constructor.fourierDerivative_continuous vRaw v_continuous)
theorem v_slope_continuous : Continuous vSlope := Constructor.fourierDerivative_continuous uRaw u_continuous

/-- The selector ranges over the two fixed responses of the original inverse. -/
def state (side : Bool) : BurnolQuarterMeanZeroCarrier := if side then Response.v else Response.u
def raw (side : Bool) : ℝ → ℂ := if side then vRaw else uRaw
def slope (side : Bool) : ℝ → ℂ := if side then vSlope else uSlope

theorem continuous (side : Bool) : Continuous (raw side) := by
  cases side
  · exact u_continuous
  · exact v_continuous
theorem slope_continuous (side : Bool) : Continuous (slope side) := by
  cases side
  · exact u_slope_continuous
  · exact v_slope_continuous
theorem derivative (side : Bool) (x : ℝ) : HasDerivAt (raw side) (slope side x) x := by
  cases side
  · exact u_derivative x
  · exact v_derivative x
theorem read (side : Bool) : (state side : ℝ → ℂ) =ᵐ[μq] raw side := by
  cases side
  · exact u_read
  · exact v_read
theorem reflection (side : Bool) : reflectRestricted q (state side : BurnolQuarterIntervalL2) = state side := by
  cases side
  · exact Response.u_reflection
  · exact Response.v_reflection

theorem even_on (side : Bool) (x : ℝ) (inside : x ∈ symmetricInterval q) : raw side (-x) = raw side x := by
  let reflectionMap := negMeasurePreserving_restrict q
  have parity : (fun x : ℝ => raw side (-x)) =ᵐ[μq] raw side := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (state side : BurnolQuarterIntervalL2) reflectionMap,
      reflectionMap.quasiMeasurePreserving.ae (read side), read side] with x reflected negative direct
    change reflectRestricted q (state side : BurnolQuarterIntervalL2) x = (state side : BurnolQuarterIntervalL2) (-x) at reflected
    rw [reflection side] at reflected
    exact negative.symm.trans (reflected.symm.trans direct)
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : -q ≠ q) parity
    ((continuous side).comp continuous_neg).continuousOn (continuous side).continuousOn inside

theorem half_integral_zero (side : Bool) : (∫ x : ℝ in Ioc 0 q, raw side x) = 0 := by
  have mean := Constructor.mean_zero (state side)
  rw [Constructor.mean_integral, integral_congr_ae (read side)] at mean
  have split := intervalIntegral.integral_add_adjacent_intervals
    ((continuous side).intervalIntegrable (μ := volume) (-q) 0)
    ((continuous side).intervalIntegrable (μ := volume) 0 q)
  have reflected : (∫ x : ℝ in (-q)..0, raw side x) = ∫ x : ℝ in (0 : ℝ)..q, raw side x := by
    have reflection := intervalIntegral.integral_comp_neg (f := raw side) (a := (0 : ℝ)) (b := q)
    simp only [neg_zero] at reflection
    rw [← reflection]
    apply intervalIntegral.integral_congr
    intro x inside
    have located : x ∈ Icc 0 q := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)] using inside
    exact even_on side x ⟨by linarith [located.1], located.2⟩
  change (2 : ℂ) * (∫ x : ℝ in Icc (-q) q, raw side x) = 0 at mean
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : -q ≤ q),
    ← split, reflected, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)] at mean
  linear_combination mean / 4

private def compactBound (f : ℝ → ℂ) (regular : Continuous f) : ℝ :=
  max 0 (isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 q) regular.continuousOn).choose

private theorem compact_bounded (f : ℝ → ℂ) (regular : Continuous f) (x : ℝ) (inside : x ∈ Icc 0 q) :
    ‖f x‖ ≤ compactBound f regular :=
  ((isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 q) regular.continuousOn).choose_spec x inside).trans
    (le_max_right _ _)

def bound (side : Bool) : ℝ := compactBound (raw side) (continuous side)
def slopeBound (side : Bool) : ℝ := compactBound (slope side) (slope_continuous side)
theorem bound_nonnegative (side : Bool) : 0 ≤ bound side := le_max_left _ _
theorem slopeBound_nonnegative (side : Bool) : 0 ≤ slopeBound side := le_max_left _ _
theorem bounded (side : Bool) (x : ℝ) (inside : x ∈ Icc 0 q) : ‖raw side x‖ ≤ bound side :=
  compact_bounded _ _ x inside
theorem slope_bounded (side : Bool) (x : ℝ) (inside : x ∈ Icc 0 q) : ‖slope side x‖ ≤ slopeBound side :=
  compact_bounded _ _ x inside

theorem lipschitz (side : Bool) (x : ℝ) (hx : x ∈ Icc 0 q) (y : ℝ) (hy : y ∈ Icc 0 q) :
    ‖raw side y - raw side x‖ ≤ slopeBound side * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t _ => (derivative side t).hasDerivWithinAt)
    (slope_bounded side) (convex_Icc 0 q) hx hy

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ResponseProfile
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
