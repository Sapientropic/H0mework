import H0mework.Arithmetic.TruncatedFourier.IntegralKernel
import H0mework.Arithmetic.TruncatedFourier.RadiusActualBridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

theorem burnolQuarterZeroExtensionRaw_memLp
    (state : BurnolQuarterIntervalL2) :
    MemLp ((symmetricInterval (1 / 4 : ℝ)).indicator fun x : ℝ ↦ state x) 2
      (volume : Measure ℝ) :=
  burnolRadiusZeroExtensionRaw_memLp state

def burnolQuarterZeroExtensionValue
    (state : BurnolQuarterIntervalL2) : BurnolL2 :=
  burnolRadiusZeroExtensionValue state

theorem burnolQuarterZeroExtensionValue_norm
    (state : BurnolQuarterIntervalL2) :
    ‖burnolQuarterZeroExtensionValue state‖ = ‖state‖ :=
  burnolRadiusZeroExtensionValue_norm state

theorem burnolQuarterZeroExtensionValue_add
    (left right : BurnolQuarterIntervalL2) :
    burnolQuarterZeroExtensionValue (left + right) =
      burnolQuarterZeroExtensionValue left +
        burnolQuarterZeroExtensionValue right :=
  burnolRadiusZeroExtensionValue_add left right

theorem burnolQuarterZeroExtensionValue_smul
    (coefficient : ℂ) (state : BurnolQuarterIntervalL2) :
    burnolQuarterZeroExtensionValue (coefficient • state) =
      coefficient • burnolQuarterZeroExtensionValue state :=
  burnolRadiusZeroExtensionValue_smul coefficient state

def burnolQuarterZeroExtensionExplicit :
    BurnolQuarterIntervalL2 →L[ℂ] BurnolL2 :=
  burnolRadiusZeroExtensionExplicit (1 / 4 : ℝ)

theorem burnolQuarterZeroExtensionExplicit_coe
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterZeroExtensionExplicit state =ᵐ[(volume : Measure ℝ)]
      (symmetricInterval (1 / 4 : ℝ)).indicator fun x : ℝ ↦ state x :=
  burnolRadiusZeroExtensionExplicit_coe state

theorem burnolQuarterZeroExtensionExplicit_is_adjoint :
    burnolQuarterZeroExtensionExplicit = burnolQuarterZeroExtension :=
  burnolRadiusZeroExtensionExplicit_is_adjoint (1 / 4 : ℝ)

theorem burnolQuarterZeroExtension_coe
    (state : BurnolQuarterIntervalL2) :
    burnolQuarterZeroExtension state =ᵐ[(volume : Measure ℝ)]
      (symmetricInterval (1 / 4 : ℝ)).indicator fun x : ℝ ↦ state x :=
  burnolRadiusZeroExtension_coe state

theorem burnolQuarterZeroExtensionRaw_integrable
    (state : BurnolQuarterIntervalL2) :
    Integrable
      ((symmetricInterval (1 / 4 : ℝ)).indicator fun x : ℝ ↦ state x)
      (volume : Measure ℝ) :=
  burnolRadiusZeroExtensionRaw_integrable state

theorem burnolTruncatedFourierRaw_eq_fourier_zeroExtension
    (state : BurnolQuarterIntervalL2) (frequency : ℝ) :
    burnolTruncatedFourierRaw state frequency =
      FourierTransform.fourier
        ((symmetricInterval (1 / 4 : ℝ)).indicator fun x : ℝ ↦ state x)
        frequency :=
  burnolRadiusTruncatedFourierRaw_eq_fourier_zeroExtension state frequency

theorem burnolRealInner_flip_fourier
    (test : SchwartzMap ℝ ℂ) (frequency : ℝ) :
    VectorFourier.fourierIntegral 𝐞 (volume : Measure ℝ)
        (innerₗ ℝ).flip (test : ℝ → ℂ) frequency =
      FourierTransform.fourier test frequency :=
  burnolRadiusRealInner_flip_fourier test frequency

theorem burnolQuarterFourier_pairing
    (state : BurnolQuarterIntervalL2) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, FourierTransform.fourier test x •
        (symmetricInterval (1 / 4 : ℝ)).indicator
          (fun y : ℝ ↦ state y) x) =
      ∫ x : ℝ, test x • burnolTruncatedFourierRaw state x :=
  burnolRadiusFourier_pairing state test

theorem burnolFourierL2_zeroExtension_ae_eq_raw
    (state : BurnolQuarterIntervalL2) :
    (fourierL2 (burnolQuarterZeroExtension state) : ℝ → ℂ) =ᵐ[
      (volume : Measure ℝ)] burnolTruncatedFourierRaw state :=
  burnolRadiusFourierL2_zeroExtension_ae_eq_raw state

theorem burnolTruncatedFourier_apply_eq_integral
    (state : BurnolQuarterIntervalL2) :
    burnolTruncatedFourier state = burnolTruncatedFourierIntegral state :=
  burnolRadiusTruncatedFourier_apply_eq_integral
    (by norm_num : (0 : ℝ) < 1 / 4) state

theorem burnolTruncatedFourier_eq_integral :
    burnolTruncatedFourier = burnolTruncatedFourierIntegral :=
  burnolRadiusTruncatedFourier_eq_integral
    (by norm_num : (0 : ℝ) < 1 / 4)

theorem burnolTruncatedFourier_opNorm_le_half :
    ‖burnolTruncatedFourier‖ ≤ (1 / 2 : ℝ) := by
  have generated := burnolRadiusTruncatedFourier_opNorm_le
    (by norm_num : (0 : ℝ) < 1 / 4)
  have radiusRead : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  rw [radiusRead] at generated
  exact generated

theorem burnolTruncatedFourier_opNorm_lt_one :
    ‖burnolTruncatedFourier‖ < 1 :=
  lt_of_le_of_lt burnolTruncatedFourier_opNorm_le_half (by norm_num)

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
