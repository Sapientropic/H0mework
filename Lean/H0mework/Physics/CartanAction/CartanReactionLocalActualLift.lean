import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift

/-!
# Source/action-generated Cartan gravity reaction field

This module opens a new epoch after the KIN-6 Cartan connection write.  It
recomputes the unique repaired-action gravity reaction from the live
primitive fields

```text
lambda(U) = star_I B(U) - N(F_raw(omega(U)))
```

and installs only that field.  The constructor receives no residual value,
coupling, coefficient, branch choice, equation, stationarity receipt, or
curvature field.  Curvature remains the derived `d omega + omega wedge omega`
readout of the KIN-6 primitive connection.

The resulting `delta B = 0` theorem is producer soundness for this update,
not a new independent constraint.  In particular, it does not transport any
connection-dependent coframe, matter, or stationarity receipt from an older
epoch.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionLocalActualLift

open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCoframeGravityGaugeRegularity
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeLorentzTorsionSpinEquation
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineResidualLinearPlebanskiTorsionReduction
open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Live reaction and installer -/

/-- The unique action-derived reaction read from the KIN-6 actual.  It is a
function of the installed auxiliary field and derived connection curvature;
it is not a source coordinate. -/
def sourceActionGeneratedDiracDualCartanReactionField
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : BasePoint → PhysicalBivector :=
  formNativeGravityReactionField
    (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space)

/-- Install only the live reaction over the KIN-6 actual. -/
def sourceActionGeneratedDiracDualCartanReactionLocalActualLift
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : StageNineHolonomicConfiguration :=
  { sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space with
    gravitySimplicityMultiplier :=
      sourceActionGeneratedDiracDualCartanReactionField source state space }

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_multiplier
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).gravitySimplicityMultiplier =
      sourceActionGeneratedDiracDualCartanReactionField source state space :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_coframe
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).coframe =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).gravityConnection =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).gravityConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_auxiliary
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).gravityAuxiliary =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).gravityAuxiliary :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_matter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).matter =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_conjugateMatter
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).conjugateMatter =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).conjugateMatter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_gaugeConnection
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).gaugeConnection =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_gaugeAuxiliary
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).gaugeAuxiliary =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).gaugeAuxiliary :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_scalar
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).scalar =
      (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
        source state space).scalar :=
  rfl

/-- Updating only `lambda` preserves the derived curvature of the complete
primitive connection field, including its first germ. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_curvature
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    holonomicContravariantGravityCurvature
        (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
          source state space) point =
      holonomicContravariantGravityCurvature
        (sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
          source state space) point :=
  rfl

/-- Compute on KIN-6, install, and recompute gives the same reaction because
the evaluator is definitionally blind to the multiplier it writes. -/
@[simp] theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_reactionField
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
          source state space) =
      sourceActionGeneratedDiracDualCartanReactionField source state space :=
  rfl

/-! ## Regularity from the live fields -/

/-- The reaction is smooth because both terms are recomputed from the smooth
KIN-6 auxiliary and primitive connection fields. -/
theorem sourceActionGeneratedDiracDualCartanReactionField_contDiff
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    ContDiff ℝ ∞
      (sourceActionGeneratedDiracDualCartanReactionField
        source state space) := by
  let base :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space
  have baseSmooth : base.Smooth :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_smooth
      source state space nondegenerate
  have dualAuxiliarySmooth : ContDiff ℝ ∞ fun point =>
      gravityInternalDualEquiv (base.gravityAuxiliary point) :=
    holonomicGravityInternalDualAuxiliary_contDiff base baseSmooth
  have curvatureSmooth : ContDiff ℝ ∞ fun point =>
      holonomicContravariantGravityCurvature base point := by
    apply contDiff_pi'
    intro internalPair
    apply contDiff_pi'
    intro spacetimePair
    exact contDiff_const.mul
      (holonomicGravityCurvature_component_contDiff base baseSmooth
        internalPair spacetimePair)
  exact dualAuxiliarySmooth.sub curvatureSmooth

/-- The KIN-8 actual is smooth without accepting a reaction regularity
certificate as input. -/
theorem sourceActionGeneratedDiracDualCartanReactionLocalActualLift_smooth
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).Smooth := by
  let base :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space
  have baseSmooth : base.Smooth :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_smooth
      source state space nondegenerate
  have reactionSmooth :=
    sourceActionGeneratedDiracDualCartanReactionField_contDiff
      source state space nondegenerate
  rcases baseSmooth with
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth, _multiplierSmooth,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩
  exact
    ⟨coframeSmooth, connectionSmooth, auxiliarySmooth,
      fun internalPair spacetimePair =>
        contDiff_pi.mp (contDiff_pi.mp reactionSmooth internalPair)
          spacetimePair,
      gaugeConnectionSmooth, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩

/-! ## Preserved geometry and action-generated zero fiber -/

theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_nondegenerate
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space).Nondegenerate := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_nondegenerate
      source state space nondegenerate

theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_simplicity
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    FormNativeGravitySimplicityEquation
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space) := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_simplicity
      source state space

theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_lorentzAdmissible
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    GravityConnectionLorentzAdmissible
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space) := by
  exact
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_lorentzAdmissible
      source state space nondegenerate

/-- The multiplier update leaves the KIN-6 connection producer live on the
new actual; W13 is recomputed from the preserved coframe and matter fields. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_connection_selfGenerated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space).gravityConnection point =
      diracDualFormNativeActionCartanConnectionAt source
        (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
          source state space) point := by
  let base :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space
  let installed :=
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space
  calc
    installed.gravityConnection point = base.gravityConnection point := rfl
    _ = diracDualFormNativeActionCartanConnectionAt source base point :=
      sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_connection_selfGenerated
        source state space point
    _ = diracDualFormNativeActionCartanConnectionAt source installed point := by
      unfold diracDualFormNativeActionCartanConnectionAt
        diracDualFormNativeActionCartanContorsionAt
        diracDualFormNativeActionCartanTorsionAt
      rw [diracDualFormNativeActionSpinResponseAt_eq_of_fields_at source
        base installed point rfl rfl rfl]
      rfl

theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_torsionSpinEquation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (nondegenerate : Matrix.det (state.coframe space) ≠ 0) :
    FormNativeIIPlusTorsionSpinEquation source
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space) := by
  intro point
  let base :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift
      source state space
  let installed :=
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift
      source state space
  have responseEqual :
      diracDualFormNativeActionSpinResponseAt source base point =
        diracDualFormNativeActionSpinResponseAt source installed point := by
    apply diracDualFormNativeActionSpinResponseAt_eq_of_fields_at
    · rfl
    · rfl
    · rfl
  have baseEquation :=
    sourceActionGeneratedDiracDualCartanConnectionLocalActualLift_torsionSpinEquation
      source state space nondegenerate point
  change
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm (installed.coframe point)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt installed.coframe point)
            (installed.gravityConnection point))) =
      diracDualFormNativeActionSpinResponseAt source installed point
  rw [← responseEqual]
  change
    internalBivectorDualThreeForm
        (torsionCoframeWedgeThreeForm (base.coframe point)
          (pointwiseCartanTorsion
            (holonomicCoframeFirstJetAt base.coframe point)
            (base.gravityConnection point))) =
      diracDualFormNativeActionSpinResponseAt source base point
  exact baseEquation

/-- Recomputing the action reaction on the installed actual returns the same
field.  This is a dependency fact: the reaction reads `B` and `omega`, while
the installer changes only `lambda`. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_reaction_selfGenerated
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space).gravitySimplicityMultiplier =
      formNativeGravityReactionField
        (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
          source state space) := by
  rfl

/-- Producer soundness of the live reaction write.  Since this equation was
used to define the update, it is not counted again as independent closure. -/
theorem
    sourceActionGeneratedDiracDualCartanReactionLocalActualLift_auxiliaryEquation
    (source : SmoothUnifiedSource)
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) :
    FormNativeGravityAuxiliaryEquation
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space) := by
  exact
    (formNativeGravityAuxiliaryEquation_iff_multiplier_eq_reaction
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift
        source state space)).2
      (sourceActionGeneratedDiracDualCartanReactionLocalActualLift_reaction_selfGenerated
        source state space)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanReactionLocalActualLift
