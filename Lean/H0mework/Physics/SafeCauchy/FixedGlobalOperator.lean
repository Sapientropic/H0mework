import H0mework.Physics.Cauchy.CoframeHolonomicCauchySafeRealization
import H0mework.Physics.ConstrainedCauchy.FixedGlobalOperator

/-!
# Fixed P506/L0 Cauchy-safe Cartan--EC output

This module installs the source-generated coframe Hessian through the global
Cauchy-safe realization, keeps the already-generated Levi--Civita connection
write, and runs the existing Cartan--EC temporal occurrence.  The resulting
single actual is globally invertible and fixed-coordinate-time
noncharacteristic without consuming either property as constructor data.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCoframeHolonomicCauchySafeRealization
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineIIPlusRestriction
open scoped ComplexOrder ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

/-- The exact source/current-owned Hessian installed by this writer. -/
def fixedP506L0CartanECConstraintCauchySafeCoframeHessian :
    CoframeHolonomicSecondJet :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
    Source CartanBase

private abbrev Hessian : CoframeHolonomicSecondJet :=
  fixedP506L0CartanECConstraintCauchySafeCoframeHessian

private abbrev QuadraticPrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

/-- The source-owned prepared actual with only its coframe realization and
derived `II+` field changed. -/
def fixedP506L0CartanECConstraintCauchySafePreparedActual :
    StageNineHolonomicConfiguration :=
  { QuadraticPrepared with
    coframe := coframeHolonomicSecondJetCauchySafeRealization Hessian
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector
        (coframeHolonomicSecondJetCauchySafeRealization Hessian point) }

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafeCoframeHessian_eq_sourceGenerated :
    fixedP506L0CartanECConstraintCauchySafeCoframeHessian =
      sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        positiveSmoothUnifiedSource
        fixedP506L0CartanECCauchyTemporalBase :=
  rfl

theorem fixedP506L0CartanECConstraintCauchySafePreparedActual_fieldInventory :
    Prepared.coframe =
        coframeHolonomicSecondJetCauchySafeRealization Hessian ∧
      Prepared.gravityConnection = QuadraticPrepared.gravityConnection ∧
      Prepared.gravityAuxiliary = (fun point =>
        physicalIIPlusBivector
          (coframeHolonomicSecondJetCauchySafeRealization Hessian point)) ∧
      Prepared.gravitySimplicityMultiplier =
        QuadraticPrepared.gravitySimplicityMultiplier ∧
      Prepared.gaugeConnection = QuadraticPrepared.gaugeConnection ∧
      Prepared.gaugeAuxiliary = QuadraticPrepared.gaugeAuxiliary ∧
      Prepared.scalar = QuadraticPrepared.scalar ∧
      Prepared.matter = QuadraticPrepared.matter ∧
      Prepared.conjugateMatter = QuadraticPrepared.conjugateMatter := by
  repeat' apply And.intro
  all_goals rfl

theorem fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth :
    Prepared.Smooth := by
  rcases fixedP506L0CartanECConstraintPreparedActual_smooth with
    ⟨_coframeSmooth, connectionSmooth, _auxiliarySmooth, multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth, matterSmooth,
      conjugateMatterSmooth⟩
  have coframeSmooth : ContDiff ℝ ∞ Prepared.coframe := by
    simpa [Prepared, fixedP506L0CartanECConstraintCauchySafePreparedActual]
      using coframeHolonomicSecondJetCauchySafeRealization_contDiff Hessian
  have auxiliarySmooth : ContDiff ℝ ∞ Prepared.gravityAuxiliary := by
    simpa [Prepared, fixedP506L0CartanECConstraintCauchySafePreparedActual,
      Function.comp_def]
      using physicalIIPlusBivector_contDiff.comp coframeSmooth
  exact
    ⟨fun row column =>
        contDiff_pi.mp (contDiff_pi.mp coframeSmooth row) column,
      connectionSmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp
          (contDiff_pi.mp auxiliarySmooth internalPair) spacetimePair,
      multiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

theorem fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate :
    Prepared.Nondegenerate := fun point =>
  coframeHolonomicSecondJetCauchySafeRealization_det_ne_zero Hessian point

theorem
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
    (point : BasePoint) :
    coframeTemporalPrincipalScalar (Prepared.coframe point) ≠ 0 :=
  coframeHolonomicSecondJetCauchySafeRealization_noncharacteristic Hessian point

@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin :
    Prepared.coframe 0 = 1 :=
  coframeHolonomicSecondJetCauchySafeRealization_origin Hessian

theorem
    fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_hasFDerivAt_origin :
    HasFDerivAt Prepared.coframe
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
  simpa [Prepared, fixedP506L0CartanECConstraintCauchySafePreparedActual] using
    coframeHolonomicSecondJetCauchySafeRealization_hasFDerivAt_origin Hessian

theorem
    fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_secondJet :
    coframeOriginSecondFrechetJet
        (fun point => Prepared.coframe point - CartanBase.coframe point) =
      Hessian.1 := by
  rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
  change
    coframeOriginSecondFrechetJet
        (fun point =>
          coframeHolonomicSecondJetCauchySafeRealization Hessian point - 1) =
      Hessian.1
  unfold coframeOriginSecondFrechetJet
  rw [show
    fderiv ℝ
        (fun point =>
          coframeHolonomicSecondJetCauchySafeRealization Hessian point - 1) =
      fderiv ℝ
        (coframeHolonomicSecondJetCauchySafeRealization Hessian) by
    funext point
    exact fderiv_sub_const (𝕜 := ℝ) (x := point) 1]
  exact coframeHolonomicSecondJetCauchySafeRealization_secondJet Hessian

@[simp] theorem
    fixedP506L0CartanECConstraintCauchySafePreparedActual_connection_eq_quadratic :
    Prepared.gravityConnection = QuadraticPrepared.gravityConnection :=
  rfl

theorem fixedP506L0CartanECConstraintCauchySafePreparedActual_simplicity :
    FormNativeGravitySimplicityEquation Prepared := by
  intro point
  rfl

/-- Exact fixed occurrence of the existing source-owned three-leg writer. -/
def fixedP506L0CartanECConstraintCauchySafeOccurrence :
    CartanECCauchyTemporalOccurrence Source Prepared :=
  sourceActionGeneratedCartanECCauchyTemporalOccurrence Source Prepared

/-- The one common actual emitted by restart, temporal connection, and live
reaction writes. -/
def fixedP506L0CartanECConstraintCauchySafeGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    Source Prepared

private abbrev Occurrence : CartanECCauchyTemporalOccurrence Source Prepared :=
  fixedP506L0CartanECConstraintCauchySafeOccurrence

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeGlobalActual

theorem fixedP506L0CartanECConstraintCauchySafeOccurrence_after_eq_actionWrite
    (leg : CartanECCauchyTemporalWriteLeg) :
    Occurrence.after leg =
      cartanECCauchyTemporalActionWrite Source Prepared leg
        (Occurrence.before leg) :=
  Occurrence.after_eq_actionWrite leg

@[simp] theorem fixedP506L0CartanECConstraintCauchySafeOccurrence_final_eq :
    Occurrence.finalActual = Output :=
  rfl

@[simp] theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe :
    Output.coframe = Prepared.coframe :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_coframe
    Source Prepared

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_nondegenerate :
    Output.Nondegenerate := by
  intro point
  rw [fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
  exact fixedP506L0CartanECConstraintCauchySafePreparedActual_nondegenerate point

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_noncharacteristic
    (point : BasePoint) :
    coframeTemporalPrincipalScalar (Output.coframe point) ≠ 0 := by
  rw [fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
  exact
    fixedP506L0CartanECConstraintCauchySafePreparedActual_noncharacteristic
      point

/-- The exact fixed P506/L0 current inherits the globally strict positive
coordinate-time Dirac coefficient from its source-owned coframe write. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_coordinateTimeEvolutionPrincipal_posDef
    (point : BasePoint) :
    (coframeCoordinateDiracEvolutionPrincipal
      (Output.coframe point) 0).PosDef := by
  rw [fixedP506L0CartanECConstraintCauchySafeGlobalActual_coframe]
  change
    (coframeCoordinateDiracEvolutionPrincipal
      (coframeHolonomicSecondJetCauchySafeRealization Hessian point) 0).PosDef
  exact
    coframeHolonomicSecondJetCauchySafeRealization_coordinateTimeEvolutionPrincipal_posDef
      Hessian point

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation Output :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
    Source Prepared

theorem
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_reactionSelfGenerated :
    Output.gravitySimplicityMultiplier =
      formNativeGravityReactionField Output :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_reactionSelfGenerated
    Source Prepared

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_fieldInventory :
    Output.coframe = Prepared.coframe ∧
      Output.gravityConnection =
        (cartanECCauchyTemporalConnectedActual Source Prepared
          ).gravityConnection ∧
      Output.gravityAuxiliary = (fun point =>
        physicalIIPlusBivector (Prepared.coframe point)) ∧
      Output.gravitySimplicityMultiplier =
        formNativeGravityReactionField Output ∧
      Output.gaugeConnection = Prepared.gaugeConnection ∧
      Output.gaugeAuxiliary = Prepared.gaugeAuxiliary ∧
      Output.scalar = Prepared.scalar ∧
      Output.matter = Prepared.matter ∧
      Output.conjugateMatter = Prepared.conjugateMatter := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  exact
    fixedP506L0CartanECConstraintCauchySafeGlobalActual_reactionSelfGenerated

theorem fixedP506L0CartanECConstraintCauchySafeGlobalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506L0CartanECConstraintCauchyGlobalActual_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
