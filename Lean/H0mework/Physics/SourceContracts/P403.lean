import H0mework.Physics.AlphaSources.P402

/-!
# Proposition 403: direct strong-coupling closure from the residual target

P288/P289/P373 isolate the remaining strong-coupling obligation in inverse
coupling coordinates.  P373 proves that a producer supplying the P289 residual
correction hits the displayed inverse target.

This file transports that statement back to the direct coupling coordinate:

`1 / (alpha_GUT^{-1} + twoLoopCorrection + residualCorrection) = 1179/10000`.

Thus the residual producer target is not merely an inverse-coordinate receipt;
it is exactly the direct displayed `alpha_s(M_Z)` closure currently used by the
Standard-Model projection.

Boundary: this is still arithmetic transport.  It does not derive the residual
from threshold, three-loop, representation, or beta-function physics.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Direct strong-coupling closure -/

/-- Corrected inverse strong coupling after adding the P289 residual correction
to the corrected GUT anchor plus current two-loop-SM inverse correction. -/
def alphaStrongCorrectedInverseAfterResidual
    (K : Type*) [Field K] : K :=
  alphaGUTInverseSectorNormalized K +
    alphaStrongTwoLoopSMInverseCorrection K +
    alphaStrongResidualInverseCorrectionNeeded K

/-- THEOREM 1: the corrected inverse coupling is exactly the displayed
observational inverse anchor. -/
theorem alphaStrongCorrectedInverseAfterResidual_eq_displayedInverse
    (K : Type*) [Field K] :
    alphaStrongCorrectedInverseAfterResidual K =
      alphaStrongDisplayedInverse K := by
  unfold alphaStrongCorrectedInverseAfterResidual
    alphaStrongResidualInverseCorrectionNeeded
    alphaStrongDisplayedInverseCorrectionFromCorrectedGUT
  ring

/-- Direct corrected strong coupling obtained by inverting the corrected
inverse coupling. -/
def alphaStrongCorrectedOutputAfterResidual
    (K : Type*) [Field K] : K :=
  (1 : K) / alphaStrongCorrectedInverseAfterResidual K

/-- THEOREM 2: after the residual inverse correction, the direct strong
coupling equals the displayed `0.1179` anchor. -/
theorem alphaStrongCorrectedOutputAfterResidual_eq_displayed
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    alphaStrongCorrectedOutputAfterResidual K =
      alphaStrongDisplayed K := by
  rw [alphaStrongCorrectedOutputAfterResidual,
    alphaStrongCorrectedInverseAfterResidual_eq_displayedInverse]
  norm_num [alphaStrongDisplayedInverse, alphaStrongDisplayed]

/-! ## Producer-certificate transport -/

namespace StrongCouplingResidualProducerCertificate

variable {K : Type*} [Field K]

/-- Corrected inverse strong coupling using a supplied residual producer
certificate. -/
def correctedInverse
    (C : StrongCouplingResidualProducerCertificate K) : K :=
  alphaGUTInverseSectorNormalized K +
    alphaStrongTwoLoopSMInverseCorrection K +
    C.inverseCorrection

/-- THEOREM 3: any residual producer matching the P289 target hits the
displayed inverse strong-coupling anchor. -/
theorem correctedInverse_eq_displayedInverse
    (C : StrongCouplingResidualProducerCertificate K) :
    C.correctedInverse = alphaStrongDisplayedInverse K := by
  unfold correctedInverse
  rw [C.inverseCorrection_eq_needed]
  exact alphaStrongCorrectedInverseAfterResidual_eq_displayedInverse K

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Direct corrected strong coupling from a supplied residual producer
certificate. -/
def correctedOutput
    (C : StrongCouplingResidualProducerCertificate K) : K :=
  (1 : K) / C.correctedInverse

/-- THEOREM 4: any residual producer matching the P289 target closes the direct
displayed strong coupling. -/
theorem correctedOutput_eq_displayed
    (C : StrongCouplingResidualProducerCertificate K) :
    C.correctedOutput = alphaStrongDisplayed K := by
  rw [correctedOutput, C.correctedInverse_eq_displayedInverse]
  norm_num [alphaStrongDisplayedInverse, alphaStrongDisplayed]

end StrongCouplingResidualProducerCertificate

namespace StandardModelGrandUnificationTargetCertificate

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 5: inside a P373/P402 grand-unification target certificate, the
strong residual producer closes the direct displayed strong coupling, not only
the inverse-coordinate correction target. -/
theorem corrected_alphaStrong_eq_displayed
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    C.strongResidualProducer.correctedOutput =
      alphaStrongDisplayed ℝ :=
  C.strongResidualProducer.correctedOutput_eq_displayed

/-- THEOREM 6: the compact target receipt can now be cited with the direct
strong-coupling closure alongside the three integer gauge anchors and CKM
phase closure. -/
theorem direct_strong_closure_receipt
    (C : StandardModelGrandUnificationTargetCertificate Index A CKMCarrier) :
    alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
      gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
      alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
      C.strongResidualProducer.correctedOutput =
        alphaStrongDisplayed ℝ ∧
      (ckmCPDepthSum : ℝ) * C.cpRunningSigma =
        cpRawPhaseClaim ℝ := by
  rcases C.three_gauge_integer_anchors with ⟨hem, hweak, hgut⟩
  exact ⟨hem, hweak, hgut, C.corrected_alphaStrong_eq_displayed,
    C.running_sigma_closes_raw_cp_phase⟩

end StandardModelGrandUnificationTargetCertificate

end StandardModelConstraint
end SaturationMonoid
