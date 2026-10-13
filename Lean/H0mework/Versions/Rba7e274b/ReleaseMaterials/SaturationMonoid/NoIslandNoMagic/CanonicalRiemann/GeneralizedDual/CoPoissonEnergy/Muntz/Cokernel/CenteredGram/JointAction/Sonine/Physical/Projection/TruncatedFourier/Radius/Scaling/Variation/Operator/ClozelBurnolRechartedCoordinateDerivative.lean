import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.KernelDerivative
import Mathlib.MeasureTheory.Function.Holder

/-! Fixed-chart coordinate multiplication and the formal radius derivative operator. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set Asymptotics
open scoped ENNReal InnerProductSpace Pointwise Topology

noncomputable section

attribute [local instance 1100] Module.complexToReal NormedSpace.complexToReal

local notation "μunit" =>
  (Measure.restrict (volume : Measure ℝ) (symmetricInterval 1))

local instance burnolStrikeUnitFiniteMeasure : IsFiniteMeasure μunit where
  measure_univ_lt_top := by
    exact lt_top_iff_ne_top.mpr (restrictedInterval_univ_ne_top 1)

local instance burnolStrikeUnitRealNormedSpace :
    NormedSpace ℝ BurnolUnitIntervalL2 :=
  NormedSpace.restrictScalars ℝ ℂ BurnolUnitIntervalL2

theorem burnolUnitCoordinate_memLp_top :
    MemLp (fun x : ℝ => (x : ℂ)) ∞ μunit := by
  apply memLp_top_of_bound (C := 1)
  · fun_prop
  · filter_upwards [burnolUnitInterval_norm_le_one] with x hx
    simpa only [Complex.norm_real] using hx

def burnolUnitCoordinateLInf : Lp ℂ ∞ μunit :=
  burnolUnitCoordinate_memLp_top.toLp (fun x : ℝ => (x : ℂ))

/-- Fixed-chart coordinate multiplication on the actual unit-interval L²
carrier. -/
def burnolUnitCoordinateMultiplier :
    BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL μunit ∞ 2 2
    burnolUnitCoordinateLInf

theorem burnolUnitCoordinateMultiplier_coe
    (state : BurnolUnitIntervalL2) :
    (burnolUnitCoordinateMultiplier state : ℝ → ℂ) =ᵐ[μunit]
      fun x : ℝ => (x : ℂ) * state x := by
  change (burnolUnitCoordinateLInf • state : BurnolUnitIntervalL2) =ᵐ[μunit] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      burnolUnitCoordinateLInf state,
    MemLp.coeFn_toLp burnolUnitCoordinate_memLp_top] with x productRead coordinateRead
  rw [productRead]
  change burnolUnitCoordinateLInf x * state x = (x : ℂ) * state x
  rw [show burnolUnitCoordinateLInf x = (x : ℂ) by exact coordinateRead]

/-- The generated fixed-chart first-variation operator. -/
def burnolRadiusRechartedTruncatedFourierDerivative
    {radius : ℝ} (positive : 0 < radius) :
    BurnolUnitIntervalL2 →L[ℂ] BurnolUnitIntervalL2 :=
  ((radius : ℂ)⁻¹) • burnolRadiusRechartedTruncatedFourier positive -
    (4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ)) •
      burnolUnitCoordinateMultiplier.comp
        ((burnolRadiusRechartedTruncatedFourier positive).comp
          burnolUnitCoordinateMultiplier)

theorem burnolUnitFourierMomentRaw_eq_coordinateMultiplier
    (state : BurnolUnitIntervalL2) (frequency : ℝ) :
    burnolUnitFourierMomentRaw state frequency =
      (-2 * (Real.pi : ℂ) * Complex.I) *
        burnolUnitFourierRaw (burnolUnitCoordinateMultiplier state) frequency := by
  rw [burnolUnitFourierMomentRaw_eq_integral]
  unfold burnolUnitFourierRaw
  let coefficient : ℂ := -2 * (Real.pi : ℂ) * Complex.I
  have integrandEq :
      (fun y : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * y) • state y) =ᵐ[μunit]
        coefficient • (burnolUnitCoordinateMultiplier state : ℝ → ℂ) := by
    filter_upwards [burnolUnitCoordinateMultiplier_coe state] with y read
    simp only [Pi.smul_apply, read, coefficient, smul_eq_mul]
    ring
  have congruent := VectorFourier.fourierIntegral_congr_ae 𝐞 μunit
    (innerₗ ℝ) integrandEq
  rw [congrFun congruent frequency]
  have scalar := VectorFourier.fourierIntegral_const_smul 𝐞 μunit
    (innerₗ ℝ) (burnolUnitCoordinateMultiplier state : ℝ → ℂ) coefficient
  rw [congrFun scalar frequency]
  rfl

theorem burnolRadiusRechartedTruncatedFourierDerivative_coe
    {radius : ℝ} (positive : 0 < radius)
    (state : BurnolUnitIntervalL2) :
    (burnolRadiusRechartedTruncatedFourierDerivative positive state : ℝ → ℂ) =ᵐ[μunit]
      burnolRadiusRechartedFirstVariationRaw radius state := by
  let T := burnolRadiusRechartedTruncatedFourier positive
  let X := burnolUnitCoordinateMultiplier
  let coefficient : ℂ := 4 * (Real.pi : ℂ) * Complex.I * (radius : ℂ)
  change (((radius : ℂ)⁻¹ • T state) - coefficient • X (T (X state)) :
      BurnolUnitIntervalL2) =ᵐ[μunit] _
  filter_upwards [Lp.coeFn_sub ((radius : ℂ)⁻¹ • T state)
      (coefficient • X (T (X state))),
    Lp.coeFn_smul (radius : ℂ)⁻¹ (T state),
    Lp.coeFn_smul coefficient (X (T (X state))),
    burnolRadiusRechartedTruncatedFourier_coe positive state,
    burnolUnitCoordinateMultiplier_coe (T (X state)),
    burnolRadiusRechartedTruncatedFourier_coe positive (X state)]
      with x subRead firstSmulRead secondSmulRead stateRead outerXRead innerRead
  rw [subRead]
  simp only [Pi.sub_apply]
  rw [firstSmulRead, secondSmulRead]
  simp only [Pi.smul_apply]
  dsimp only [T, X] at stateRead outerXRead innerRead ⊢
  rw [stateRead, outerXRead, innerRead]
  rw [burnolRadiusRechartedTruncatedFourierRaw_eq_frequencyChart,
    burnolRadiusRechartedTruncatedFourierRaw_eq_frequencyChart]
  unfold burnolRadiusRechartedFirstVariationRaw
  rw [burnolUnitFourierMomentRaw_eq_coordinateMultiplier]
  simp only [smul_eq_mul, real_smul, coefficient]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  push_cast
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
