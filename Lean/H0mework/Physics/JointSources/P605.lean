import H0mework.Realization.Descent.P422
import H0mework.Physics.RepresentationSources.P514
import H0mework.Physics.AlphaSources.P602
import H0mework.Physics.YukawaSources.P604

/-!
# Proposition 605: one receipt for the three Standard-Model producer nails

P600-P604 closed the three shortest producer-debt nails separately:

* `alpha_s`: the exact inverse residual `-89000/128511` is produced by an
  embedded-complement numerator and a 4D Poincare-resolution denominator;
* Yukawa depths: primitive finite cards generate the unique accepted
  nine-depth table `[50, 346, 372, 489, 583, 682, 880, 908, 982]`;
* CKM phase arithmetic: the same depth table gives the Jarlskog depth sum
  `386`.

This file does not add a new physics mechanism.  It makes the current shortest
chain citeable as one object:

`gauge core + information/matter core + 4D Poincare resolution +
primitive-card Yukawa producer -> the three main nails`.

Boundary: the receipt is still finite-card / current-formal-geometry closure.
It does not prove a smooth de Rham spacetime producer, threshold spectrum,
three-loop RG, Higgs-extra-representation dynamics, or the full CKM matrix.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection
open InformationMatterProjection

/-! ## Current formal 4D Poincare witness -/

/-- The current formal 4D Poincare certificate used by this receipt when a
concrete parameter-free witness is desired.

This is P422's degree-orbit normal form.  It inhabits the present abstract
Poincare interface, but it is explicitly not a smooth/de Rham spacetime
producer. -/
def currentFormalFourDPoincareCertificate : FourDPoincareCertificate :=
  FourDimensionalPoincareOrbitCohomologyNormalForm.unitOrbitNormalForm
    |>.toPoincareDualityCohomologyCertificate

/-! ## Main producer-nails receipt -/

/-- One receipt for the three currently closed Standard-Model producer nails.

The parameters are the two honest open physical interfaces on the `alpha_s`
side: a 4D Poincare certificate `C` and an embedding of the unified
48-direction gauge carrier into the 137-point structural electromagnetic
carrier.  The canonical formal instance is given below by using P422's formal
Poincare witness and P601's canonical embedding.
-/
structure MainProducerNailsCertificate
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) where
  gauge_core :
    GaugeUnificationCoreCertificate ℚ
  information_matter_core :
    FiniteInformationMatterUnificationCoreCertificate.{0, 0, 0}
  alpha_s_resolution_producer :
    AlphaStrongPoincareResolutionProducerReceipt C e
  yukawa_primitive_producer :
    YukawaPrimitiveCardProducerReceipt
  alpha_s_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer C e).producedGap =
      -((89000 : ℚ) / 128511)
  alpha_s_closes_displayed :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPoincareResolutionResidualGapProducer C e).producedGap) =
      alphaStrongDisplayed ℚ
  yukawa_depth_table :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ckmDepthSum_fromYukawaDepthTable
      primitiveCardYukawaProducerInputCandidate.depthTable =
        (ckmCPDepthSum : Int)
  gauge_core_residual_target :
    alphaStrongResidualInverseCorrectionNeeded ℚ =
      -((89000 : ℚ) / 128511)
  information_matter_component_card :
    Fintype.card MatterComponentPosition = 17

/-- THEOREM 1: parameterized main-nails receipt.

For any supplied 4D Poincare certificate and any supplied embedding of the
unified gauge carrier into the electromagnetic structural carrier, the current
finite core carries the `alpha_s` inverse residual, displayed-alpha closure,
the primitive-card Yukawa depth table, and the CKM depth sum `386`. -/
noncomputable def mainProducerNailsCertificate
    (C : FourDPoincareCertificate)
    (e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier) :
    MainProducerNailsCertificate C e where
  gauge_core := gaugeUnificationCoreCertificate ℚ
  information_matter_core := finiteInformationMatterUnificationCoreCertificate
  alpha_s_resolution_producer :=
    alphaStrongPoincareResolutionProducerReceipt C e
  yukawa_primitive_producer := yukawaPrimitiveCardProducerReceipt
  alpha_s_inverse_residual :=
    alphaStrongPoincareResolutionResidualGapProducer_inverseCorrection C e
  alpha_s_closes_displayed := by
    change
      (1 : ℚ) /
          (alphaStrongTwoLoopSMOutputInverse ℚ +
            inverseCorrectionFromAlphaGap
              (alphaStrongTwoLoopSMOutput ℚ)
              (alphaStrongGapProducerOfSU7FiniteContributionLaw
                (alphaStrongPoincareResolutionContribution C e)
                (alphaStrongPoincareResolutionContribution_law C e)).producedGap) =
        alphaStrongDisplayed ℚ
    exact
      alphaStrongGapProducerOfSU7FiniteContributionLaw_closes_displayedAlpha
        (alphaStrongPoincareResolutionContribution C e)
        (alphaStrongPoincareResolutionContribution_law C e)
  yukawa_depth_table :=
    primitiveCardYukawaProducerInputCandidate_massOrder_eq
  ckm_depth_sum :=
    primitiveCardYukawaProducerInputCandidate_ckmDepthSum_eq_386
  gauge_core_residual_target :=
    alphaStrongResidualInverseCorrectionNeeded_eq ℚ
  information_matter_component_card :=
    matterComponentPosition_card

/-- THEOREM 2: canonical current-formal main-nails receipt.

This is the on-the-nose harness-facing instance: P422's current formal
Poincare certificate plus P601's canonical gauge embedding.  Its boundary is
exactly the boundary of those two inputs. -/
noncomputable def canonicalCurrentFormalMainProducerNailsCertificate :
    MainProducerNailsCertificate
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural :=
  mainProducerNailsCertificate
    currentFormalFourDPoincareCertificate
    unifiedGaugeIntoAlphaEMStructural

namespace MainProducerNailsCertificate

/-- THEOREM 3: any main-nails receipt exposes the exact `alpha_s` inverse
residual target. -/
theorem alpha_s_residual
    {C : FourDPoincareCertificate}
    {e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier}
    (R : MainProducerNailsCertificate C e) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPoincareResolutionResidualGapProducer C e).producedGap =
      -((89000 : ℚ) / 128511) :=
  R.alpha_s_inverse_residual

/-- THEOREM 4: any main-nails receipt exposes the primitive-card generated
nine-depth table. -/
theorem yukawa_depths
    {C : FourDPoincareCertificate}
    {e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier}
    (R : MainProducerNailsCertificate C e) :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  R.yukawa_depth_table

/-- THEOREM 5: any main-nails receipt exposes the CKM/Jarlskog depth sum
`386`. -/
theorem ckm_depth_sum_eq_386
    {C : FourDPoincareCertificate}
    {e : UnifiedGaugeFreedomCarrier ↪ AlphaEMStructuralCarrier}
    (R : MainProducerNailsCertificate C e) :
    ckmDepthSum_fromYukawaDepthTable
      primitiveCardYukawaProducerInputCandidate.depthTable =
        (ckmCPDepthSum : Int) :=
  R.ckm_depth_sum

end MainProducerNailsCertificate

end StandardModelConstraint
end SaturationMonoid
