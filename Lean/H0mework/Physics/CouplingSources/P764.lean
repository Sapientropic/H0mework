import H0mework.Physics.CouplingSources.P763
import H0mework.Arithmetic.PrimeShadow.P667

/-!
# Proposition 764: physicalized numerical pressure closure

P763 says the physicalized SU(7) numerical spine supplies the QCD RG slope,
the nine Yukawa depths, and the CKM phase-depth matrix.  P666/P667 say the
same central root carries the Yukawa leave-one-out pressure and the coded
prime-shadow pressure.

This file welds those together into one pressure-level closure certificate:
the physicalized finite Standard-Model numerical spine and the validation
pressure gates live in the same Lean object.
-/

noncomputable section

namespace SaturationMonoid
namespace GrandUnification

open StandardModelConstraint
open StandardModelConstraint.RunningSigmaBeta
open AffineRelaxation

universe u

/-- Physicalized SU(7) numerical spine plus the pressure gates that keep the
same finite numerical output from floating free:

* QCD `b0 = 7` and the alpha inverse residual;
* nine Yukawa depths and CKM/Jarlskog `386`;
* leave-one-out prediction under an eight-slot lock;
* coded-descent prime-shadow synchronization.
-/
structure PhysicalizedNumericalPressureClosureCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  physicalized_spine :
    SU7PhysicalizedNumericalProducerSpineCertificate
  yukawa_pressure_root :
    Nonempty (YukawaLeaveOneOutPressureUnifiedRootCertificate E)
  coded_descent_pressure_root :
    Nonempty (CodedDescentPrimeShadowProducerPressureUnifiedRootCertificate E)
  qcd_b0_from_physicalized_spine :
    betaCoeff qcdBlockIncidenceOneLoopInput = 7
  alpha_s_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  selected_nine_yukawa_depths :
    selectedYukawaDepthTableCandidate.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  pressure_nine_yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_matrix_depth_sum :
    ckmJarlskogDepthFromMatrix = (ckmCPDepthSum : Int)
  ckm_pressure_depth_sum :
    ckmJarlskogFourProductDepthSum
        primitiveCardYukawaProducerInputCandidate.depthTable =
      (ckmCPDepthSum : Int)
  leave_one_out_locked_candidate_predicts :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C : YukawaLeaveOneOutCandidate T target,
          T.observed target = T.predictionAt C.sigma target
  leave_one_out_locked_prediction_unique :
    ∀ {T : FrozenGUTScaleYukawaTable} {target : YukawaParameter},
      EightSlotSigmaLock target T.observed T.amplitude T.exponent ->
        ∀ C₁ C₂ : YukawaLeaveOneOutCandidate T target,
          T.predictionAt C₁.sigma target =
            T.predictionAt C₂.sigma target
  coded_descent_prime_shadow_sync :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : CommonPredicateSupportedCodedDomain
        (codedDescentSupportIndexedPrimeShadowProducer A).toCommonPredicateProducer),
      HalfSigmaRateGoldbachComplete x.1.val.rate ↔
        H1SpectralNoObstructionComplete x.1.spectral

/-- THEOREM: the current physicalized numerical spine is closed under the
Yukawa leave-one-out and coded-prime-shadow pressure gates. -/
theorem physicalizedNumericalPressureClosureCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    PhysicalizedNumericalPressureClosureCertificate E where
  physicalized_spine :=
    su7PhysicalizedNumericalProducerSpineCertificate
  yukawa_pressure_root :=
    ⟨yukawaLeaveOneOutPressureUnifiedRootCertificate (E := E)⟩
  coded_descent_pressure_root :=
    ⟨codedDescentPrimeShadowProducerPressureUnifiedRootCertificate (E := E)⟩
  qcd_b0_from_physicalized_spine :=
    su7PhysicalizedNumericalProducerSpineCertificate.qcd_b0_from_representation
  alpha_s_inverse_residual :=
    codedDescentPressure_alpha_s_residual (E := E)
  selected_nine_yukawa_depths :=
    su7PhysicalizedNumericalProducerSpineCertificate.nine_yukawa_depths
  pressure_nine_yukawa_depths :=
    yukawaPressure_finite_depths (E := E)
  ckm_matrix_depth_sum :=
    su7PhysicalizedNumericalProducerSpineCertificate.ckm_matrix_depth_sum
  ckm_pressure_depth_sum :=
    (yukawaLeaveOneOutPressureUnifiedRootCertificate
      (E := E)).finite_ckm_depth_sum
  leave_one_out_locked_candidate_predicts := by
    intro T target lock C
    exact yukawaPressure_locked_candidate_predicts (E := E) lock C
  leave_one_out_locked_prediction_unique := by
    intro T target lock C₁ C₂
    exact yukawaPressure_locked_prediction_unique (E := E) lock C₁ C₂
  coded_descent_prime_shadow_sync := by
    intro A x
    exact codedDescentPressure_prime_shadow_sync (E := E) A x

end GrandUnification
end SaturationMonoid
