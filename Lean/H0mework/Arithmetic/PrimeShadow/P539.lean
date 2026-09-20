import H0mework.Physics.AlphaSources.P532
import H0mework.Arithmetic.PrimeShadow.P538

/-!
# Proposition 539: unified hard gate v4 with canonical prime-shadow spine

P532 bundled the physical hard gates through the producer-facing `alpha_s`
source-accounting surface.  P538 tightened the mathematical Goldbach/RH route:
any structured grand-producer front door must carry a canonical prime-indexed
shadow, and that shadow cannot be faithfully binary-coded.

This file joins those two surfaces.  The unified hard gate now exposes the
physical residual producer accounting and the canonical prime-shadow spine in
one object.  The result is still not a proof of Goldbach/RH or a completed
Standard Model producer.  It is a stronger front-door normal form: future
producers must pass both the physical source-accounting gate and the
non-binary prime-indexed mathematical gate.
-/

noncomputable section

namespace SaturationMonoid

open AffineRelaxation
open StandardModelConstraint

universe u

/-! ## Unified hard gate v4 -/

/-- Unified hard gate v4: v3 physical producer accounting plus the canonical
prime-indexed mathematical producer spine from P538. -/
structure UnifiedGrandHardGateV4Certificate where
  base :
    UnifiedGrandHardGateV3Certificate.{u}
  canonical_prime_support :
    PrimeIndexedSupport PrimeExponent
  no_binary_prime_support :
    Not (∃ f : PrimeExponent -> Fin 2, Function.Injective f)

/-- THEOREM 1: the unified hard gate v4 is inhabited by the current
machine-checked gates. -/
def unifiedGrandHardGateV4Certificate :
    UnifiedGrandHardGateV4Certificate.{u} where
  base := unifiedGrandHardGateV3Certificate
  canonical_prime_support := PrimeIndexedSupport.canonical
  no_binary_prime_support := no_injective_primeExponent_to_fin_two

namespace UnifiedGrandHardGateV4Certificate

/-- THEOREM 2: v4 keeps the producer-level alpha residual accounting law. -/
theorem alpha_residual_partial_closure_iff_omitted_null
    (G : UnifiedGrandHardGateV4Certificate.{u})
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool) :
    P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
      P.omittedSum selected = 0 :=
  G.base.alpha_residual_partial_closure_iff_omitted_null P selected

/-- THEOREM 3: v4 still rejects the old `Prop`-valued truth shadow at the
structured unified front door. -/
theorem rejects_truth_value_shadow_front_door
    (G : UnifiedGrandHardGateV4Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A] :
    Not
      (Nonempty
        (UnifiedGrandStructuredProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry
          truthValuePrimeShadowProducer)) :=
  G.base.base.rejects_truth_value_shadow_front_door

/-- THEOREM 4: any structured front door exposes its prime-indexed support as
part of the v4 mathematical hard gate. -/
def structured_front_door_prime_support
    (_G : UnifiedGrandHardGateV4Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F : UnifiedGrandStructuredProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P) :
    PrimeIndexedSupport P.PrimeShadow :=
  structuredFrontDoorPrimeIndexedSupport F

/-- THEOREM 5: every structured front door receives the canonical prime map
from `PrimeExponent` into its mathematical shadow. -/
def structured_front_door_canonical_prime_map
    (G : UnifiedGrandHardGateV4Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F : UnifiedGrandStructuredProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P) :
    PrimeIndexedSupport.Hom
      PrimeIndexedSupport.canonical
      (G.structured_front_door_prime_support F) :=
  structuredFrontDoorCanonicalPrimeMap F

/-- THEOREM 6: the canonical prime map is unique for every structured front
door. -/
theorem structured_front_door_canonical_prime_map_unique
    (G : UnifiedGrandHardGateV4Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F : UnifiedGrandStructuredProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P)
    (f :
      PrimeIndexedSupport.Hom
        PrimeIndexedSupport.canonical
        (G.structured_front_door_prime_support F)) :
    f = G.structured_front_door_canonical_prime_map F :=
  PrimeIndexedSupport.canonical_initial
    (G.structured_front_door_prime_support F) f

/-- THEOREM 7: v4 forbids a binary mathematical shadow at any structured
unified front door. -/
theorem no_binary_structured_front_door
    (_G : UnifiedGrandHardGateV4Certificate.{u})
    {Index A CKMCarrier PhysicalGeometry : Type u} [AddCommGroup A]
    {P : EulerPrimeCouplingProducers}
    (F : UnifiedGrandStructuredProducerFrontDoor
      Index A CKMCarrier PhysicalGeometry P) :
    Not (∃ encode : P.PrimeShadow -> Fin 2, Function.Injective encode) :=
  no_binary_coding_of_structuredFrontDoor F

/-- THEOREM 8: v4 keeps any selected alpha source-family closure connected to
the displayed strong-coupling anchor. -/
theorem alpha_residual_selected_gap_closes_displayed
    (G : UnifiedGrandHardGateV4Certificate.{u})
    (P : AlphaStrongResidualGapProducer)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      P.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (P.selectedSum selected)) =
      alphaStrongDisplayed ℚ :=
  G.base.alpha_residual_selected_gap_closes_displayed P selected hselected

end UnifiedGrandHardGateV4Certificate

end SaturationMonoid
