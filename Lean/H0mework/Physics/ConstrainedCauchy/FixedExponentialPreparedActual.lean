import H0mework.Physics.Holonomic.CoframeHolonomicMatrixExponentialRealization
import H0mework.Physics.ConstrainedCauchy.FixedGlobalOperator

/-!
# Fixed P506/L0 exponential coframe adapter

This parallel prepared actual retains the complete source/action-generated
quadratic prepared carrier except for the coframe realization and its derived
`II+` auxiliary.  The coframe uses the canonical matrix exponential of the
same generated Hessian, while the already-generated Levi--Civita connection
first jet and every non-coframe field are retained exactly.

The existing quadratic prepared alias is deliberately left unchanged.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialPreparedActual

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCoframeHolonomicMatrixExponentialRealization
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineHolonomicField
open StageNineIIPlusRestriction
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

/-- The exact source/current-owned Hessian consumed by the exponential
realization. -/
def fixedP506L0CartanECConstraintExponentialCoframeHessian :
    CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    Source CartanBase

private abbrev Hessian : CoframeHolonomicSecondJet :=
  fixedP506L0CartanECConstraintExponentialCoframeHessian

private abbrev QuadraticPrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

/-- Parallel fixed-lineage prepared actual.  Only the coframe and the
coframe-derived `II+` auxiliary are replaced; in particular the complete
connection field generated from the same Hessian is inherited verbatim. -/
def fixedP506L0CartanECConstraintExponentialPreparedActual :
    StageNineHolonomicConfiguration :=
  { QuadraticPrepared with
    coframe := coframeHolonomicSecondJetMatrixExponentialRealization Hessian
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector
        (coframeHolonomicSecondJetMatrixExponentialRealization Hessian point) }

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintExponentialPreparedActual

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialCoframeHessian_eq_sourceGenerated :
    fixedP506L0CartanECConstraintExponentialCoframeHessian =
      sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource
        fixedP506L0CartanECCauchyTemporalBase :=
  rfl

/-- Exhaustive custody of all nine fields of the parallel prepared actual. -/
theorem fixedP506L0CartanECConstraintExponentialPreparedActual_fieldInventory :
    Output.coframe =
        coframeHolonomicSecondJetMatrixExponentialRealization Hessian ∧
      Output.gravityConnection = QuadraticPrepared.gravityConnection ∧
      Output.gravityAuxiliary = (fun point =>
        physicalIIPlusBivector
          (coframeHolonomicSecondJetMatrixExponentialRealization
            Hessian point)) ∧
      Output.gravitySimplicityMultiplier =
        QuadraticPrepared.gravitySimplicityMultiplier ∧
      Output.gaugeConnection = QuadraticPrepared.gaugeConnection ∧
      Output.gaugeAuxiliary = QuadraticPrepared.gaugeAuxiliary ∧
      Output.scalar = QuadraticPrepared.scalar ∧
      Output.matter = QuadraticPrepared.matter ∧
      Output.conjugateMatter = QuadraticPrepared.conjugateMatter := by
  repeat' apply And.intro
  all_goals rfl

theorem fixedP506L0CartanECConstraintExponentialPreparedActual_smooth :
    Output.Smooth := by
  rcases fixedP506L0CartanECConstraintPreparedActual_smooth with
    ⟨_coframeSmooth, connectionSmooth, _auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  have exponentialSmooth : ContDiff ℝ ∞ Output.coframe := by
    simpa [Output, fixedP506L0CartanECConstraintExponentialPreparedActual]
      using
        coframeHolonomicSecondJetMatrixExponentialRealization_contDiff Hessian
  have auxiliarySmooth : ContDiff ℝ ∞ Output.gravityAuxiliary := by
    simpa [Output, fixedP506L0CartanECConstraintExponentialPreparedActual,
      Function.comp_def]
      using physicalIIPlusBivector_contDiff.comp exponentialSmooth
  exact
    ⟨fun row column =>
        contDiff_pi.mp (contDiff_pi.mp exponentialSmooth row) column,
      connectionSmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp
          (contDiff_pi.mp auxiliarySmooth internalPair) spacetimePair,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

theorem fixedP506L0CartanECConstraintExponentialPreparedActual_nondegenerate :
    Output.Nondegenerate := by
  intro point
  exact
    coframeHolonomicSecondJetMatrixExponentialRealization_det_ne_zero
      Hessian point

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialPreparedActual_coframe_origin :
    Output.coframe 0 = 1 := by
  exact
    coframeHolonomicSecondJetMatrixExponentialRealization_origin Hessian

theorem
    fixedP506L0CartanECConstraintExponentialPreparedActual_coframe_hasFDerivAt_origin :
    HasFDerivAt Output.coframe
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
  simpa [Output, fixedP506L0CartanECConstraintExponentialPreparedActual] using
    coframeHolonomicSecondJetMatrixExponentialRealization_hasFDerivAt_origin
      Hessian

/-- Relative to the fixed identity Cartan base, the exponential coframe and
the inherited LC connection write carry the same generated Hessian. -/
theorem
    fixedP506L0CartanECConstraintExponentialPreparedActual_coframe_secondJet :
    coframeOriginSecondFrechetJet
        (fun point => Output.coframe point - CartanBase.coframe point) =
      Hessian.1 := by
  rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
  change
    coframeOriginSecondFrechetJet
        (fun point =>
          coframeHolonomicSecondJetMatrixExponentialRealization
              Hessian point - 1) =
      Hessian.1
  unfold coframeOriginSecondFrechetJet
  rw [show
    fderiv ℝ
        (fun point =>
          coframeHolonomicSecondJetMatrixExponentialRealization
              Hessian point - 1) =
      fderiv ℝ
        (coframeHolonomicSecondJetMatrixExponentialRealization Hessian) by
    funext point
    exact fderiv_sub_const (𝕜 := ℝ) (x := point) 1]
  exact
    coframeHolonomicSecondJetMatrixExponentialRealization_secondJet Hessian

@[simp] theorem
    fixedP506L0CartanECConstraintExponentialPreparedActual_connection_eq_quadratic :
    Output.gravityConnection = QuadraticPrepared.gravityConnection :=
  rfl

/-- The inherited connection is still the complete affine LC first-jet write
generated by the same source-owned Hessian. -/
theorem
    fixedP506L0CartanECConstraintExponentialPreparedActual_connection_eq_sourceHessianWrite :
    Output.gravityConnection = fun point =>
      CartanBase.gravityConnection point +
        identityECLeviCivitaAffineConnectionIncrement Hessian point :=
  rfl

theorem fixedP506L0CartanECConstraintExponentialPreparedActual_simplicity :
    FormNativeGravitySimplicityEquation Output := by
  intro point
  rfl

/-- The adapter changes no source or source lineage. -/
theorem fixedP506L0CartanECConstraintExponentialPreparedActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506L0CartanECConstraintCauchyGlobalActual_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyExponentialPreparedActual
