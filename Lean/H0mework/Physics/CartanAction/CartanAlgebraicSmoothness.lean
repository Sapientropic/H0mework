import H0mework.Physics.CartanAction.CartanPointCoframeRegularity
import H0mework.Physics.IdentityGerms.IdentityECNonlinearLeviCivitaFirstGerm

/-!
# Smoothness of the finite Cartan algebraic maps

This module upgrades the two finite-dimensional algebraic regularity seams
used by the Cartan connection construction from first differentiability to
smoothness.  It consumes only the primitive coframe/response and coframe-jet
carriers already used by the existing producers.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanAlgebraicSmoothness

open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeLocalDifferentiability
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanPointCoframeRegularity
open StageNineDiracDualFormNativeIdentityECNonlinearLeviCivitaFirstGerm
open StageNineGlobalIntegratedAction
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The inverse KIN-1 torsion response is smooth at every nondegenerate
coframe fiber.  This is the exact algebraic seam consumed by synchronized
coframe-profile regularity; no contorsion field is introduced. -/
theorem cartanTorsionOfThreeForm_component_contDiffAt
    (coframe : LorentzianCoframe)
    (response : PhysicalBivectorThreeForm)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (pair : Fin 6) (internal : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
        cartanTorsionOfThreeForm carrier.1 carrier.2 pair internal)
      (coframe, response) := by
  have inverseEntrySmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          carrier.1⁻¹ row column)
        (coframe, response) := by
    exact
      ((contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (coframe_inv_contDiffAt coframe nondegenerate) row) column).comp
        (coframe, response) contDiffAt_fst)
  have undualEntrySmooth
      (bivectorPair : Fin 6) (triple : Fin 4) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          internalBivectorUndualThreeForm carrier.2 bivectorPair triple)
        (coframe, response) := by
    fin_cases bivectorPair <;>
      simp [internalBivectorUndualThreeForm,
        lorentzianCoframeHodge] <;>
      fun_prop
  have orderedUndualSmooth
      (internalFirst internalSecond first second third : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          orderedPhysicalBivectorThreeFormComponent
            (internalBivectorUndualThreeForm carrier.2)
            internalFirst internalSecond first second third)
        (coframe, response) := by
    unfold orderedPhysicalBivectorThreeFormComponent
      orderedInternalBivectorThreeFormComponent
    apply ContDiffAt.sum
    intro triple _
    apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro bivectorPair _
      exact (undualEntrySmooth bivectorPair triple).mul (by fun_prop)
    · fun_prop
  have firstContractionSmooth
      (targetInternal first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanThreeFormFirstContraction carrier.1
            (internalBivectorUndualThreeForm carrier.2)
            targetInternal first second)
        (coframe, response) := by
    unfold cartanThreeFormFirstContraction
    apply ContDiffAt.sum
    intro contractedInternal _
    apply ContDiffAt.sum
    intro direction _
    exact (inverseEntrySmooth direction contractedInternal).mul
      (orderedUndualSmooth targetInternal contractedInternal
        direction first second)
  have doubleContractionSmooth
      (direction : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanThreeFormDoubleContraction carrier.1
            (internalBivectorUndualThreeForm carrier.2) direction)
        (coframe, response) := by
    unfold cartanThreeFormDoubleContraction
    apply ContDiffAt.sum
    intro targetInternal _
    apply ContDiffAt.sum
    intro spacetime _
    exact (inverseEntrySmooth spacetime targetInternal).mul
      (firstContractionSmooth targetInternal spacetime direction)
  unfold cartanTorsionOfThreeForm
    cartanTorsionOfUndualThreeForm
  apply ContDiffAt.add
  · exact firstContractionSmooth internal
      (pairFirst pair) (pairSecond pair)
  · apply ContDiffAt.mul (by fun_prop)
    apply ContDiffAt.sub
    · exact
        (doubleContractionSmooth (pairFirst pair)).mul (by fun_prop)
    · exact
        (doubleContractionSmooth (pairSecond pair)).mul (by fun_prop)

/-- The algebraic Cartan response is smooth at every nondegenerate coframe
fiber.  Its only non-polynomial operation is matrix inversion. -/
theorem cartanContorsionCoframeResponseComponent_contDiffAt
    (coframe : LorentzianCoframe)
    (response : PhysicalBivectorThreeForm)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ ∞
      (cartanContorsionCoframeResponseComponent
        formDirection internalPair) (coframe, response) := by
  have inverseEntrySmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          carrier.1⁻¹ row column)
        (coframe, response) := by
    exact
      ((contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (coframe_inv_contDiffAt coframe nondegenerate) row) column).comp
        (coframe, response) contDiffAt_fst)
  have torsionEntrySmooth
      (pair : Fin 6) (internal : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanTorsionOfThreeForm carrier.1 carrier.2 pair internal)
        (coframe, response) :=
    cartanTorsionOfThreeForm_component_contDiffAt
      coframe response nondegenerate pair internal
  have pulledTorsionEntrySmooth
      (framePair : Fin 6) (internal : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          pullbackCartanTorsionTwoForm carrier.1
            (cartanTorsionOfThreeForm carrier.1 carrier.2)
            framePair internal)
        (coframe, response) := by
    unfold pullbackCartanTorsionTwoForm coframeTwoFormLinear
      coframeWedge
    simp only [Matrix.transpose_apply]
    change ContDiffAt ℝ ∞
      (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
        ∑ spacetimePair : Fin 6,
          (carrier.1⁻¹ (pairFirst spacetimePair) (pairFirst framePair) *
                carrier.1⁻¹ (pairSecond spacetimePair)
                  (pairSecond framePair) -
              carrier.1⁻¹ (pairSecond spacetimePair) (pairFirst framePair) *
                carrier.1⁻¹ (pairFirst spacetimePair)
                  (pairSecond framePair)) *
            cartanTorsionOfThreeForm carrier.1 carrier.2
              spacetimePair internal)
      (coframe, response)
    apply ContDiffAt.sum
    intro spacetimePair _
    apply ContDiffAt.mul
    · apply ContDiffAt.sub
      · exact
          (inverseEntrySmooth
            (pairFirst spacetimePair) (pairFirst framePair)).mul
            (inverseEntrySmooth
              (pairSecond spacetimePair) (pairSecond framePair))
      · exact
          (inverseEntrySmooth
            (pairSecond spacetimePair) (pairFirst framePair)).mul
            (inverseEntrySmooth
              (pairFirst spacetimePair) (pairSecond framePair))
    · exact torsionEntrySmooth spacetimePair internal
  have raisedPulledTorsionEntrySmooth
      (framePair : Fin 6) (internal : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          minkowskiRaiseCartanTorsion
            (pullbackCartanTorsionTwoForm carrier.1
              (cartanTorsionOfThreeForm carrier.1 carrier.2))
            framePair internal)
        (coframe, response) := by
    unfold minkowskiRaiseCartanTorsion
    apply ContDiffAt.mul
    · fun_prop
    · exact pulledTorsionEntrySmooth framePair internal
  have orderedRaisedTorsionSmooth
      (internal first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          orderedCartanTorsionComponent
            (minkowskiRaiseCartanTorsion
              (pullbackCartanTorsionTwoForm carrier.1
                (cartanTorsionOfThreeForm carrier.1 carrier.2)))
            internal first second)
        (coframe, response) := by
    unfold orderedCartanTorsionComponent
    apply ContDiffAt.sum
    intro pair _
    exact (raisedPulledTorsionEntrySmooth pair internal).mul (by fun_prop)
  have internalContorsionEntrySmooth
      (internalDirection : LorentzianIndex) (pair : Fin 6) :
      ContDiffAt ℝ ∞
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          internalFrameContorsionOfTorsion
            (minkowskiRaiseCartanTorsion
              (pullbackCartanTorsionTwoForm carrier.1
                (cartanTorsionOfThreeForm carrier.1 carrier.2)))
            internalDirection pair)
        (coframe, response) := by
    unfold internalFrameContorsionOfTorsion
    apply ContDiffAt.mul
    · fun_prop
    · exact
        (((orderedRaisedTorsionSmooth
            (pairFirst pair) internalDirection (pairSecond pair)).sub
          (orderedRaisedTorsionSmooth
            internalDirection (pairSecond pair) (pairFirst pair))).add
          (orderedRaisedTorsionSmooth
            (pairSecond pair) (pairFirst pair) internalDirection))
  unfold cartanContorsionCoframeResponseComponent
    contorsionOfCartanTorsion
    pushforwardLorentzBivectorOneForm
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro internalDirection _
  apply ContDiffAt.mul
  · fun_prop
  · exact internalContorsionEntrySmooth internalDirection internalPair

/-- The pointwise nonlinear Levi--Civita component is smooth in its primitive
coframe and first-derivative inputs at the identity/zero contact. -/
theorem identityECSpinConnectionComponentOfCarrier_contDiffAt
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn)
      ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative)) := by
  have coframeInverseSmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          carrier.1⁻¹ row column)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    exact
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (coframe_inv_contDiffAt (1 : LorentzianCoframe) (by simp))
          row) column).comp
        ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative))
        contDiffAt_fst
  have metricInverseSmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (lorentzianMetricOfCoframe carrier.1)⁻¹ row column)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    exact
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (lorentzianMetric_inv_contDiffAt
            (1 : LorentzianCoframe) (by simp)) row) column).comp
        ((1 : LorentzianCoframe), (0 : LorentzianCoframeDerivative))
        contDiffAt_fst
  have metricDerivativeSmooth
      (first second third : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).metricDerivative
            first second third)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold pointwiseCoframeJetOfCarrier
      PointwiseLorentzianCoframeJet.metricDerivative
    apply ContDiffAt.sum
    intro internal _
    apply ContDiffAt.mul
    · fun_prop
    · apply ContDiffAt.add <;> fun_prop
  have loweredConnectionSmooth
      (lower first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).loweredLeviCivitaConnection
            lower first second)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    fun_prop (disch := exact metricDerivativeSmooth _ _ _)
  have raisedConnectionSmooth
      (upper first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).leviCivitaConnection
            upper first second)
        ((1 : LorentzianCoframe),
          (0 : LorentzianCoframeDerivative)) := by
    unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
      PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
      PointwiseLorentzianCoframeJet.metric
      PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    simp only [Matrix.mulVec, dotProduct]
    apply ContDiffAt.sum
    intro lower _
    exact (metricInverseSmooth upper lower).mul
      (loweredConnectionSmooth lower first second)
  unfold identityECSpinConnectionComponentOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply]
  apply ContDiffAt.sum
  intro intermediate _
  apply ContDiffAt.mul
  · apply ContDiffAt.sub
    · apply ContDiffAt.sum
      intro coordinate _
      apply ContDiffAt.mul
      · fun_prop
      · exact
          raisedConnectionSmooth coordinate formDirection intermediate
    · fun_prop
  · exact coframeInverseSmooth intermediate internalIn

/-- The nonlinear Levi--Civita component is smooth at every nondegenerate
coframe jet, not only at the identity/zero normalization used by the first
fixed contact.  This is the local analytic mouth required when the same
source/current action is recomputed at an arbitrary spacetime occurrence.

The carrier contains only the actual coframe and its first derivative; no
connection value, equation receipt, or target jet is supplied. -/
theorem spinConnectionComponentOfCarrier_contDiffAt
    (coframe : LorentzianCoframe)
    (derivative : LorentzianCoframeDerivative)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (identityECSpinConnectionComponentOfCarrier
        formDirection internalOut internalIn)
      (coframe, derivative) := by
  have coframeInverseSmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          carrier.1⁻¹ row column)
        (coframe, derivative) := by
    exact
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (coframe_inv_contDiffAt coframe nondegenerate) row) column).comp
        (coframe, derivative) contDiffAt_fst
  have metricInverseSmooth
      (row column : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (lorentzianMetricOfCoframe carrier.1)⁻¹ row column)
        (coframe, derivative) := by
    exact
      (contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (lorentzianMetric_inv_contDiffAt coframe nondegenerate)
          row) column).comp
        (coframe, derivative) contDiffAt_fst
  have metricDerivativeSmooth
      (first second third : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).metricDerivative
            first second third)
        (coframe, derivative) := by
    unfold pointwiseCoframeJetOfCarrier
      PointwiseLorentzianCoframeJet.metricDerivative
    apply ContDiffAt.sum
    intro internal _
    apply ContDiffAt.mul
    · fun_prop
    · apply ContDiffAt.add <;> fun_prop
  have loweredConnectionSmooth
      (lower first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).loweredLeviCivitaConnection
            lower first second)
        (coframe, derivative) := by
    unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
    fun_prop (disch := exact metricDerivativeSmooth _ _ _)
  have raisedConnectionSmooth
      (upper first second : LorentzianIndex) :
      ContDiffAt ℝ ∞
        (fun carrier : IdentityECCoframeJetCarrier =>
          (pointwiseCoframeJetOfCarrier carrier).leviCivitaConnection
            upper first second)
        (coframe, derivative) := by
    unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
      PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
      PointwiseLorentzianCoframeJet.metric
      PointwiseLorentzianCoframeJet.loweredLeviCivitaVector
    simp only [Matrix.mulVec, dotProduct]
    apply ContDiffAt.sum
    intro lower _
    exact (metricInverseSmooth upper lower).mul
      (loweredConnectionSmooth lower first second)
  unfold identityECSpinConnectionComponentOfCarrier
    PointwiseLorentzianCoframeJet.lorentzSpinConnection
    PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
    PointwiseLorentzianCoframeJet.coordinateConnectionMatrix
    affineConnectionMatrix
    PointwiseLorentzianCoframeJet.coframeDerivativeMatrix
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.of_apply]
  apply ContDiffAt.sum
  intro intermediate _
  apply ContDiffAt.mul
  · apply ContDiffAt.sub
    · apply ContDiffAt.sum
      intro coordinate _
      apply ContDiffAt.mul
      · fun_prop
      · exact
          raisedConnectionSmooth coordinate formDirection intermediate
    · fun_prop
  · exact coframeInverseSmooth intermediate internalIn

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanAlgebraicSmoothness
