import H0mework.Physics.SynchronizedJoint.GravityTailProfileLocalRegularity
import H0mework.Physics.SafeCauchy.FixedJointGlobalECJetRegularity
import H0mework.Physics.SafeCauchy.FixedJointGlobalSmooth

/-!
# Cauchy-safe gravity-tail input regularity

The synchronized gravity prefix regenerates its four gravity fields from an
exact source/current pair and retains the other five fields. Smoothness is
therefore a generic consequence of whole-current smoothness. The fixed
specializations expose both the post-EC checkpoint and the complete
post-primal/post-adjoint/reaction current used by the living root.

For the complete current, nondegeneracy is first established at the exact
activation contact. This suffices for the origin-local gravity-tail jet
readout without assuming a global determinant normal form for the new affine
coframe.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeECPathGravityTailInputRegularity

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanContorsionTorsionEquiv
open StageNineCoframeFirstJet
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeCartanECSynchronizedCoframeContactLocalActualLift
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailJointPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator
open StageNineDiracDualFormNativeCartanECSynchronizedGravityTailProfileLocalRegularity
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCauchySafeJointGlobalDevelopment
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointCauchySafeScalarTemporalDevelopment
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalECJetRegularity
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalSmooth
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineResidualLinearPlebanskiTorsionReduction
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

local instance safeGravityTailP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286HolonomicSecondJetCarrier.p286ModuleFinite

local instance safeGravityTailP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance safeGravityTailP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

/-- Whole-current smoothness is the only regularity input needed by the
synchronized gravity-base constructor. The coframe, affine connection,
`II+`, and live reaction are regenerated; the other five fields are retained
from that exact current. -/
theorem cartanECSynchronizedGravityTailBase_smooth_of_currentSmooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (currentSmooth : current.Smooth) :
    (cartanECSynchronizedGravityTailBase source current).Smooth := by
  let base := cartanECSynchronizedGravityTailBase source current
  have coframeSmooth : ContDiff ℝ ∞ base.coframe :=
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contDiff
      source current 0
  have connectionSmooth
      (direction internalOut internalIn : LorentzianIndex) :
      ContDiff ℝ ∞ fun point =>
        base.gravityConnection point direction internalOut internalIn := by
    change ContDiff ℝ ∞ fun point =>
      coframeECContactCenteredNormalizedAffineLorentzConnectionField 0
        _ _ point direction internalOut internalIn
    simpa [coframeECContactCenteredNormalizedAffineLorentzConnectionField] using
      normalizedAffineLorentzConnectionField_smooth _ _
        direction internalOut internalIn
  have auxiliarySmooth (internalPair spacetimePair : Fin 6) :
      ContDiff ℝ ∞ fun point =>
        base.gravityAuxiliary point internalPair spacetimePair := by
    have allCoordinates : ContDiff ℝ ∞ fun point =>
        physicalIIPlusBivector (base.coframe point) :=
      physicalIIPlusBivector_contDiff.comp coframeSmooth
    exact contDiff_pi.mp (contDiff_pi.mp allCoordinates internalPair)
      spacetimePair
  have multiplierSmooth (internalPair spacetimePair : Fin 6) :
      ContDiff ℝ ∞ fun point =>
        base.gravitySimplicityMultiplier point internalPair spacetimePair := by
    let prepared :=
      diracDualFormNativeCartanECSynchronizedCoframePreparedActual
        source current 0
    change ContDiff ℝ ∞ fun point =>
      formNativeGravityReactionField prepared point internalPair spacetimePair
    apply formNativeGravityReactionField_component_contDiff
    · exact connectionSmooth
    · exact auxiliarySmooth
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row column
    exact contDiff_pi.mp (contDiff_pi.mp coframeSmooth row) column
  · exact connectionSmooth
  · exact auxiliarySmooth
  · exact multiplierSmooth
  · exact currentSmooth.2.2.2.2.1
  · exact currentSmooth.2.2.2.2.2.1
  · exact currentSmooth.2.2.2.2.2.2.1
  · exact currentSmooth.2.2.2.2.2.2.2.1
  · exact currentSmooth.2.2.2.2.2.2.2.2

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev SafePrepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafePreparedActual

private abbrev SafeBase : StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source SafePrepared

private abbrev ECPath : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalECPathCurrent Source SafeBase

private abbrev ECPathGravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source ECPath

private abbrev Final : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchySafeJointGlobalActual

private abbrev FinalGravityBase : StageNineHolonomicConfiguration :=
  cartanECSynchronizedGravityTailBase Source Final

private abbrev BoundaryInput : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalInput

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

private abbrev GlobalP286 : StageNineHolonomicConfiguration :=
  cauchySafeJointGlobalP286Current Source SafeBase

private abbrev Primal : StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameTimeMatterActual ECPath

private abbrev MatterDual : StageNineHolonomicConfiguration :=
  actionGeneratedGlobalFrameMatterDualActual ECPath

/-- Post-EC specialization retained for consumers that activate before the
primal/adjoint material stages. -/
theorem fixedP506L0CartanECConstraintCauchySafeECPathGravityTailBase_smooth :
    ECPathGravityBase.Smooth :=
  cartanECSynchronizedGravityTailBase_smooth_of_currentSmooth Source ECPath
    fixedP506L0CartanECConstraintCauchySafeJointGlobalECPathCurrent_smooth

/-- The post-primal/post-adjoint/reaction current generates a smooth
synchronized gravity base without replaying the earlier EC current. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_smooth :
    FinalGravityBase.Smooth :=
  cartanECSynchronizedGravityTailBase_smooth_of_currentSmooth Source Final
    fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_smooth

/-- At the exact activation contact, the generated affine coframe reads the
same coframe occurrence as the complete joint current. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_origin :
    FinalGravityBase.coframe 0 = Final.coframe 0 := by
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedCoframeContactLocalActualLift_coframe_contact
      Source Final 0

/-- The complete current's source-owned nondegeneracy transfers to the exact
gravity-tail activation contact. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate_origin :
    Matrix.det (FinalGravityBase.coframe 0) ≠ 0 := by
  rw [fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_origin]
  exact fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_nondegenerate 0

/-- Origin-local `C¹` regularity of the exact coframe-jet coordinate consumed
by the gravity-tail radial writer. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeJetCoordinateCLM_contDiffAt_origin
    (internal coordinate : LorentzianIndex) :
    ContDiffAt ℝ 1 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Final contact internal coordinate) 0 :=
  cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    Source Final
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_smooth
    0
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate_origin
    internal coordinate

private theorem canonicalSlice_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem safePrepared_coframeFirstJet_origin_eq_identity :
    holonomicCoframeFirstJetAt SafePrepared.coframe 0 =
      identityCoframeMatterGeometry := by
  apply coframeJet_eq_of_fields_eq
  · exact fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin
  · funext derivativeDirection internal coordinate
    have coframeSmooth : ContDiff ℝ ∞ SafePrepared.coframe :=
      StageNineCoframeHolonomicRegularity.holonomicCoframe_contDiff
        SafePrepared
        fixedP506L0CartanECConstraintCauchySafePreparedActual_smooth
    change
      fieldDirectionalDerivative
          (fun point => SafePrepared.coframe point internal coordinate)
          0 derivativeDirection = 0
    rw [← fieldDirectionalDerivative_pi_apply
        (fun point => SafePrepared.coframe point internal)
        (contDiff_pi.mp coframeSmooth internal) 0
        derivativeDirection coordinate,
      ← fieldDirectionalDerivative_pi_apply SafePrepared.coframe
        coframeSmooth 0 derivativeDirection internal]
    unfold fieldDirectionalDerivative
    have coframeFDeriv : fderiv ℝ SafePrepared.coframe 0 = 0 :=
      fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_hasFDerivAt_origin.fderiv
    exact congrArg
      (fun derivative : BasePoint →L[ℝ] LorentzianCoframe =>
        derivative (coordinateDirection derivativeDirection) internal
          coordinate)
      coframeFDeriv

private theorem cartanBase_coframeFirstJet_origin_eq_identity :
    holonomicCoframeFirstJetAt CartanBase.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]
  apply coframeJet_eq_of_fields_eq
  · rfl
  · funext derivativeDirection internal coordinate
    simp [holonomicCoframeFirstJetAt, identityCoframeMatterGeometry]

private theorem actionCartanConnectionAt_eq_of_jet_and_fields_at
    (first second : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (jetEqual :
      holonomicCoframeFirstJetAt first.coframe point =
        holonomicCoframeFirstJetAt second.coframe point)
    (coframeEqual : first.coframe point = second.coframe point)
    (matterEqual : first.matter point = second.matter point)
    (conjugateEqual :
      first.conjugateMatter point = second.conjugateMatter point) :
    diracDualFormNativeActionCartanConnectionAt Source first point =
      diracDualFormNativeActionCartanConnectionAt Source second point := by
  have spinEqual :=
    diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      Source first second point coframeEqual matterEqual conjugateEqual
  unfold diracDualFormNativeActionCartanConnectionAt
    diracDualFormNativeActionCartanContorsionAt
    diracDualFormNativeActionCartanTorsionAt
  rw [jetEqual, coframeEqual, spinEqual]

private theorem safeBase_connection_origin_eq_fixedAction :
    SafeBase.gravityConnection 0 = fixedActionCartanConnection := by
  have safeMatterOrigin :
      SafePrepared.matter 0 = CartanBase.matter 0 :=
    (congrFun
      fixedP506L0CartanECConstraintCauchySafePreparedActual_fieldInventory.2.2.2.2.2.2.2.1
      0).trans rfl
  have safeConjugateOrigin :
      SafePrepared.conjugateMatter 0 = CartanBase.conjugateMatter 0 :=
    (congrFun
      fixedP506L0CartanECConstraintCauchySafePreparedActual_fieldInventory.2.2.2.2.2.2.2.2
      0).trans rfl
  have safeCartanAction :
      diracDualFormNativeActionCartanConnectionAt Source SafePrepared 0 =
        diracDualFormNativeActionCartanConnectionAt Source CartanBase 0 := by
    apply actionCartanConnectionAt_eq_of_jet_and_fields_at
    · exact safePrepared_coframeFirstJet_origin_eq_identity.trans
        cartanBase_coframeFirstJet_origin_eq_identity.symm
    · rw [fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin,
        congrFun fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one 0]
    · exact safeMatterOrigin
    · exact safeConjugateOrigin
  have cartanBaseSelfGenerated :
      CartanBase.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt Source CartanBase 0 := by
    exact
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
        Source BoundaryInput 0
  have cartanBaseFixed :=
    base_connection_zeroSlice_eq_fixedAction (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at cartanBaseFixed
  calc
    SafeBase.gravityConnection 0 =
        diracDualFormNativeActionCartanConnectionAt Source SafePrepared 0 :=
      congrFun
        (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection
          Source SafePrepared) 0
    _ = diracDualFormNativeActionCartanConnectionAt Source CartanBase 0 :=
      safeCartanAction
    _ = CartanBase.gravityConnection 0 := cartanBaseSelfGenerated.symm
    _ = fixedActionCartanConnection := cartanBaseFixed

private theorem ecPath_matter_origin_eq_safePrepared :
    ECPath.matter 0 = SafePrepared.matter 0 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      Source SafeBase).matter 0 = SafeBase.matter 0
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source SafeBase).matter 0 = SafeBase.matter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_matter_zeroSlice
      Source SafeBase (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at generated
  exact generated

private theorem ecPath_conjugateMatter_origin_eq_safePrepared :
    ECPath.conjugateMatter 0 = SafePrepared.conjugateMatter 0 := by
  change
    (sourceActionGeneratedDiracDualCompleteJointCauchySafeTemporalDevelopmentOperator
      Source SafeBase).conjugateMatter 0 = SafeBase.conjugateMatter 0
  change
    (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
      Source SafeBase).conjugateMatter 0 = SafeBase.conjugateMatter 0
  have generated :=
    sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_conjugateMatter_zeroSlice
      Source SafeBase (0 : StageNineSpatialPoint)
  rw [canonicalSlice_zero] at generated
  exact generated

private theorem final_coframe_eq_safePrepared :
    Final.coframe = SafePrepared.coframe := by
  calc
    Final.coframe = SafeBase.coframe :=
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_coframe
    _ = SafePrepared.coframe := rfl

private theorem final_matter_origin_eq_safePrepared :
    Final.matter 0 = SafePrepared.matter 0 := by
  calc
    Final.matter 0 = Primal.matter 0 := congrFun
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_fieldInventory.2.2.2.2.2.2.2.1
      0
    _ = ECPath.matter 0 :=
      actionGeneratedGlobalFrameTimeMatterActual_matter_origin ECPath
    _ = SafePrepared.matter 0 := ecPath_matter_origin_eq_safePrepared

private theorem final_conjugateMatter_origin_eq_safePrepared :
    Final.conjugateMatter 0 = SafePrepared.conjugateMatter 0 := by
  calc
    Final.conjugateMatter 0 = MatterDual.conjugateMatter 0 := congrFun
      fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_fieldInventory.2.2.2.2.2.2.2.2
      0
    _ = ECPath.conjugateMatter 0 :=
      (actionGeneratedGlobalFrameMatterDualActual_fieldInventory ECPath
        ).2.2.2.2.2.2.2.2
    _ = SafePrepared.conjugateMatter 0 :=
      ecPath_conjugateMatter_origin_eq_safePrepared

private theorem final_connection_origin_eq_fixedAction :
    Final.gravityConnection 0 = fixedActionCartanConnection := by
  calc
    Final.gravityConnection 0 =
        cauchySafeJointGlobalECConnectionField Source GlobalP286 0 :=
      congrFun
        fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_fieldInventory.2.1
        0
    _ = GlobalP286.gravityConnection 0 :=
      cauchySafeJointGlobalECConnectionField_zero Source GlobalP286
    _ = SafeBase.gravityConnection 0 := rfl
    _ = fixedActionCartanConnection :=
      safeBase_connection_origin_eq_fixedAction

private theorem final_coframeFirstJet_origin_eq_identity :
    holonomicCoframeFirstJetAt Final.coframe 0 =
      identityCoframeMatterGeometry := by
  rw [final_coframe_eq_safePrepared]
  exact safePrepared_coframeFirstJet_origin_eq_identity

/-- The complete post-adjoint current retains the exact origin germ needed
by the synchronized Cartan coframe compiler.  The global primal and adjoint
writes remain present; only their source-generated zero radial increments at
the activation contact are used here. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeFirstJet_origin_eq_identity :
    diracDualFormNativeCartanECSynchronizedCoframeFirstJet Source Final 0 =
      identityCoframeMatterGeometry := by
  apply coframeJet_eq_of_fields_eq
  · unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
    dsimp only
    rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      congrFun final_coframe_eq_safePrepared 0,
      fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin]
    rfl
  · funext derivativeDirection internal coordinate
    unfold diracDualFormNativeCartanECSynchronizedCoframeFirstJet
    dsimp only
    have safeNondegenerate : Matrix.det (SafePrepared.coframe 0) ≠ 0 := by
      rw [fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin]
      norm_num
    have ecSpinEqFinal :
        diracDualFormNativeActionSpinResponseAt Source
            (diracDualFormNativeCartanECSynchronizedECActual Source Final 0) 0 =
          diracDualFormNativeActionSpinResponseAt Source Final 0 := by
      apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      · rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe]
      · rfl
      · rfl
    have ecTorsionEqFinal :
        diracDualFormNativeActionCartanTorsionAt Source
            (diracDualFormNativeCartanECSynchronizedECActual Source Final 0) 0 =
          diracDualFormNativeActionCartanTorsionAt Source Final 0 := by
      unfold diracDualFormNativeActionCartanTorsionAt
      rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
        ecSpinEqFinal]
    have finalSpinEqSafe :
        diracDualFormNativeActionSpinResponseAt Source Final 0 =
          diracDualFormNativeActionSpinResponseAt Source SafePrepared 0 := by
      apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
      · exact congrFun final_coframe_eq_safePrepared 0
      · exact final_matter_origin_eq_safePrepared
      · exact final_conjugateMatter_origin_eq_safePrepared
    have finalTorsionEqSafe :
        diracDualFormNativeActionCartanTorsionAt Source Final 0 =
          diracDualFormNativeActionCartanTorsionAt Source SafePrepared 0 := by
      unfold diracDualFormNativeActionCartanTorsionAt
      rw [congrFun final_coframe_eq_safePrepared 0, finalSpinEqSafe]
    have safeActionFixed :
        diracDualFormNativeActionCartanConnectionAt Source SafePrepared 0 =
          fixedActionCartanConnection := by
      calc
        _ = SafeBase.gravityConnection 0 :=
          (congrFun
            (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection
              Source SafePrepared) 0).symm
        _ = fixedActionCartanConnection :=
          safeBase_connection_origin_eq_fixedAction
    have actualTorsion :=
      diracDualFormNativeActionCartanConnectionAt_actualTorsion
        Source SafePrepared 0 safeNondegenerate
    rw [safeActionFixed, safePrepared_coframeFirstJet_origin_eq_identity]
      at actualTorsion
    have actualTorsionEq :
        actualPointwiseCartanTorsionTwoForm identityCoframeMatterGeometry
            fixedActionCartanConnection =
          diracDualFormNativeActionCartanTorsionAt Source
            (diracDualFormNativeCartanECSynchronizedECActual Source Final 0) 0 :=
      ((actualTorsion.trans finalTorsionEqSafe.symm).trans
        ecTorsionEqFinal.symm)
    rw [sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_connection_contact,
      sourceActionGeneratedDiracDualCoframeECContactLocalActualLift_coframe,
      congrFun final_coframe_eq_safePrepared 0,
      fixedP506L0CartanECConstraintCauchySafePreparedActual_coframe_origin,
      ← actualTorsionEq, final_connection_origin_eq_fixedAction]
    fin_cases derivativeDirection <;> fin_cases internal <;>
      fin_cases coordinate <;>
      simp [identityCoframeMatterGeometry, orderedCartanTorsionComponent,
        actualPointwiseCartanTorsionTwoForm, pointwiseCartanTorsion,
        pointwiseCoframeCovariantDerivative, coframeConnectionAction,
        fixedActionCartanConnection_eq_positiveNormalForm,
        positiveDiracDualCartanContorsionNormalForm,
        lorentzSkewConnectionOfBivectorOneForm,
        loweredLorentzBivectorMatrix,
        orientedLorentzBivectorBasisCoefficient, pairFirst, pairSecond,
        Fin.sum_univ_six, Matrix.one_apply] <;>
      norm_num

/-- The SafeFinal synchronized affine coframe has the global identity normal
form. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_eq_one :
    FinalGravityBase.coframe = fun _ => (1 : LorentzianCoframe) := by
  change
    cartanECSynchronizedCenteredAffineCoframeField 0
        (diracDualFormNativeCartanECSynchronizedCoframeFirstJet
          Source Final 0) = _
  rw [
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeFirstJet_origin_eq_identity]
  funext point
  simp [cartanECSynchronizedCenteredAffineCoframeField]

/-- Consequently the generated SafeFinal gravity base is nondegenerate at
every spacetime point, with no determinant premise. -/
theorem fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate :
    FinalGravityBase.Nondegenerate := by
  intro point
  rw [
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_eq_one]
  norm_num

/-- Global `C¹` gravity-tail coframe-jet regularity consumed by the assembly
writer. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeJetCoordinateCLM_contDiff
    (internal coordinate : LorentzianIndex) :
    ContDiff ℝ 1 (fun contact =>
      cartanECSynchronizedGravityTailCoframeJetCoordinateCLM
        Source Final contact internal coordinate) := by
  rw [contDiff_iff_contDiffAt]
  intro contact
  exact cartanECSynchronizedGravityTailCoframeJetCoordinateCLM_contDiffAt
    Source Final
    fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_smooth
    contact
    (fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate
      contact)
    internal coordinate

#print axioms cartanECSynchronizedGravityTailBase_smooth_of_currentSmooth
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_smooth
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate_origin
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeJetCoordinateCLM_contDiffAt_origin
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeFirstJet_origin_eq_identity
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_coframe_eq_one
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailBase_nondegenerate
#print axioms
  fixedP506L0CartanECConstraintCauchySafeJointFinalGravityTailCoframeJetCoordinateCLM_contDiff

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeECPathGravityTailInputRegularity
end PhysicsCore
end SaturationMonoid
