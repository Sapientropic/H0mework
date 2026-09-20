import H0mework.Realization.RelaxationFlow.P476
import H0mework.Realization.Relations.P516
import H0mework.Physics.JointSources.P619

/-!
# Proposition 620: current unified-equation finite core

The newest finite producer work (P617-P619) closes the three shortest
Standard-Model producer-debt nails at the finite layer:

* `alpha_s` inverse residual `-89000/128511`;
* Yukawa depths `[50, 346, 372, 489, 583, 682, 880, 908, 982]`;
* CKM/Jarlskog depth sum `386`.

Earlier files already closed two broader spines:

* P476: the shared coordinate-action normal form of the unified equation
  `X -> X + sigma * (Target - X)` in residual coordinates, and of one-loop
  gauge running in inverse-coupling coordinates;
* P515/P516: the physical/mathematical projection core and its producer front
  door.

This file puts those pieces under one root certificate.  It is intentionally
still finite/projection-level: it does not construct smooth threshold spectra,
three-loop RG, Higgs-extra dynamics, full CKM matrix entries, or the
prime-shadow producer required for Goldbach/RH.  It proves that the current
formula spine, projection core, producer front door, and three finite physical
nails now have a single Lean entry point.
-/

noncomputable section

namespace SaturationMonoid

open StandardModelConstraint

/-! ## Unified finite core -/

/-- The current root certificate for the finite unified-equation layer.

The fields deliberately keep three kinds of evidence separate:

* the formula/action spine (`coordinate_spine`);
* the physical/mathematical projection core and producer front door;
* the newly closed finite Standard-Model producer nails.
-/
structure CurrentUnifiedEquationFiniteCoreCertificate where
  real_decay_coordinate :
    ∀ {E : Type} [AddCommGroup E] [Module ℝ E],
      ∀ target : E, ∀ lambda : ℝ,
        CoordinateActionLaw
          (fun t x =>
            AffineRelaxation.realDecayRelaxFlow target lambda t x)
          (fun x => target - x)
          (fun t v => AffineRelaxation.realDecayResidual lambda t • v)
          (fun _ _ => True)
  standard_model_inverse_coordinate :
    ∀ G : StandardModelConstraint.RunningSigmaBeta.StandardModelGaugeFactor,
      CoordinateActionLaw
        (fun t sigma =>
          StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow
            G sigma t)
        (fun sigma => (1 : ℝ) / sigma)
        (fun t c =>
          c +
            (StandardModelConstraint.RunningSigmaBeta.standardModelAsymptoticB0
              G : ℝ) * t)
        (fun _ sigma => sigma ≠ 0)
  running_sigma_two_coordinate_joint :
    ∀ {Seed Scale Index A CKMCarrier : Type} [AddCommGroup A],
      ∀ C : StandardModelConstraint.RunningSigmaStandardModelCertificate
          Seed Scale Index A ℝ CKMCarrier,
      ∀ seed y lambda step,
      C.sigma (C.yukawaScale seed y) =
          AffineRelaxation.realDecayRate lambda step ->
      ∀ G : StandardModelConstraint.RunningSigmaBeta.StandardModelGaugeFactor,
      ∀ sigma0 t s,
      sigma0 ≠ 0 ->
      1 + (StandardModelConstraint.RunningSigmaBeta.standardModelAsymptoticB0
            G : ℝ) * sigma0 * t ≠ 0 ->
      1 + (StandardModelConstraint.RunningSigmaBeta.standardModelAsymptoticB0
            G : ℝ) * sigma0 * (t + s) ≠ 0 ->
      C.pinned.base.generated seed (yukawaSlot y) =
          AffineRelaxation.realDecayRelaxFlow
            (0 : ℝ) lambda
            ((C.pinned.yukawaExponent seed y : ℝ) * step)
            (C.pinned.yukawaAmplitude y)
        ∧
      StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow G
          (StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow
            G sigma0 t) s =
        StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow G
          sigma0 (t + s)
  projection_core :
    FinitePhysicsMathematicsUnificationProjectionCoreCertificate
  front_door_available :
    ∀ {Index A CKMCarrier PhysicalGeometry : Type} [AddCommGroup A],
      ∀ {P : AffineRelaxation.EulerPrimeCouplingProducers},
      UnifiedGrandProducerFrontDoor
          Index A CKMCarrier PhysicalGeometry P ->
        UnifiedGrandProducerOutput Index A CKMCarrier P
  finite_producer_nails :
    StandardModelConstraint.FiniteProducerDebtThreeNailReceipt
  alpha_inverse_residual :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)
  yukawa_depths :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982]
  ckm_depth_sum :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ)
  alpha_displayed_closure :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPhysicalFiniteGeometryProducer
              currentFormalFourDPoincareCertificate
              unifiedGaugeIntoAlphaEMStructural).producedGap) =
      alphaStrongDisplayed ℚ

/-- THEOREM 1: the current unified-equation finite core is inhabited. -/
def currentUnifiedEquationFiniteCoreCertificate :
    CurrentUnifiedEquationFiniteCoreCertificate where
  real_decay_coordinate :=
    fun target lambda =>
      AffineRelaxation.realDecayCoordinateActionLaw target lambda
  standard_model_inverse_coordinate :=
    StandardModelConstraint.RunningSigmaBeta.standardModelInverseCoordinateActionLaw
  running_sigma_two_coordinate_joint := by
    intro Seed Scale Index A CKMCarrier _ C seed y lambda step hsampled
      G sigma0 t s hsigma hden_t hden_ts
    exact
      StandardModelConstraint.generated_yukawa_and_standardModel_gauge_flow
        C seed y lambda step hsampled G sigma0 t s hsigma hden_t hden_ts
  projection_core := finitePhysicsMathematicsUnificationProjectionCoreCertificate
  front_door_available := by
    intro Index A CKMCarrier PhysicalGeometry _ P F
    exact unifiedGrandProducerOutput_of_frontDoor F
  finite_producer_nails :=
    StandardModelConstraint.finiteProducerDebtThreeNailReceipt
  alpha_inverse_residual :=
    StandardModelConstraint.finiteProducerDebtThreeNailReceipt.alpha_inverse_residual
  yukawa_depths :=
    StandardModelConstraint.finiteProducerDebtThreeNailReceipt
      |>.yukawa_depths_from_primitive_cards
  ckm_depth_sum :=
    StandardModelConstraint.finiteProducerDebtThreeNailReceipt
      |>.ckm_jarlskog_depth_sum
  alpha_displayed_closure :=
    alphaStrongPhysicalFiniteGeometryProducer_closes_displayedAlpha
      currentFormalFourDPoincareCertificate
      unifiedGaugeIntoAlphaEMStructural

namespace CurrentUnifiedEquationFiniteCoreCertificate

/-- THEOREM 2: the unified finite core exposes the exact alpha_s inverse
residual producer output. -/
theorem alpha_s_residual
    (C : CurrentUnifiedEquationFiniteCoreCertificate) :
    inverseCorrectionFromAlphaGap
        (alphaStrongTwoLoopSMOutput ℚ)
        (alphaStrongPhysicalFiniteGeometryProducer
          currentFormalFourDPoincareCertificate
          unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511) :=
  C.alpha_inverse_residual

/-- THEOREM 3: the unified finite core exposes the generated Yukawa depth
table. -/
theorem yukawa_depth_table
    (C : CurrentUnifiedEquationFiniteCoreCertificate) :
    primitiveCardYukawaProducerInputCandidate.depthTable.massOrder =
      [50, 346, 372, 489, 583, 682, 880, 908, 982] :=
  C.yukawa_depths

/-- THEOREM 4: the unified finite core exposes the finite CKM/Jarlskog
sector-axis depth sum. -/
theorem ckm_depth_sum_eq_386
    (C : CurrentUnifiedEquationFiniteCoreCertificate) :
    ckmJarlskogDepthSumFromRationalGrid
        (gridOfStencil
          (rationalStencilOfCKMSectorAxisPrimitiveCardPacket
            canonicalCKMSectorAxisPrimitiveCardPacket)) =
      (386 : ℚ) :=
  C.ckm_depth_sum

/-- THEOREM 5: the unified finite core closes displayed `alpha_s` from the
finite physical-geometry producer. -/
theorem alpha_s_displayed_closure
    (C : CurrentUnifiedEquationFiniteCoreCertificate) :
    (1 : ℚ) /
        (alphaStrongTwoLoopSMOutputInverse ℚ +
          inverseCorrectionFromAlphaGap
            (alphaStrongTwoLoopSMOutput ℚ)
            (alphaStrongPhysicalFiniteGeometryProducer
              currentFormalFourDPoincareCertificate
              unifiedGaugeIntoAlphaEMStructural).producedGap) =
      alphaStrongDisplayed ℚ :=
  C.alpha_displayed_closure

/-- THEOREM 6: the core contains the formula-level coordinate-action normal
form for fixed-target relaxation. -/
theorem real_decay_coordinate_action
    (C : CurrentUnifiedEquationFiniteCoreCertificate)
    {E : Type} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda : ℝ) :
    CoordinateActionLaw
      (fun t x => AffineRelaxation.realDecayRelaxFlow target lambda t x)
      (fun x => target - x)
      (fun t v => AffineRelaxation.realDecayResidual lambda t • v)
      (fun _ _ => True) :=
  C.real_decay_coordinate target lambda

/-- THEOREM 7: the same core contains the inverse-coordinate normal form for
one-loop Standard-Model gauge running. -/
theorem standard_model_inverse_coordinate_action
    (C : CurrentUnifiedEquationFiniteCoreCertificate)
    (G : StandardModelConstraint.RunningSigmaBeta.StandardModelGaugeFactor) :
    CoordinateActionLaw
      (fun t sigma =>
        StandardModelConstraint.RunningSigmaBeta.standardModelOneLoopSigmaFlow
          G sigma t)
      (fun sigma => (1 : ℝ) / sigma)
      (fun t c =>
        c +
          (StandardModelConstraint.RunningSigmaBeta.standardModelAsymptoticB0
            G : ℝ) * t)
      (fun _ sigma => sigma ≠ 0) :=
  C.standard_model_inverse_coordinate G

end CurrentUnifiedEquationFiniteCoreCertificate

end SaturationMonoid
