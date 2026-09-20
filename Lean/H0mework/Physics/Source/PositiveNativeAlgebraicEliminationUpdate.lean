import H0mework.Physics.Gauge.PositiveNativeGravityCurvatureBridge
import H0mework.Physics.ConnectionJets.GeneratedP286AffineConnectionGerm
import H0mework.Physics.GaugeAction.P286VaryingCurvatureAuxiliaryGraph
import H0mework.Physics.Source.PositiveSourceJointShellReachability

/-!
# S9-C3h68b: source-native algebraic-elimination state update

This is the first honest Stage-9 state update built from current source
kinematics.  It first installs the positive source's coframe, actual
first-jet Lorentz connection, and P286 affine connection.  It then derives
both auxiliary fields from the seed configuration's genuine
`dω + ω∧ω` and `dA + [A,A]` curvatures by the unique current constitutive
solvers.

The update has no auxiliary input, coefficient, target curvature, branch, or
shell receipt.  It preserves the gravity multiplier, scalar, matter, and
conjugate-matter fields verbatim, so it is an algebraic-elimination update on
an existing configuration, not a complete source-generated world.

Both auxiliary equations hold by construction.  Nevertheless the actual
source-native gravity curvature bridge places every update image in the old
positive-source gravity-mouth class, whose simplicity/curvature intersection
is empty.  Hence this deterministic, idempotent update is a stable
class-scoped no-go for the uncorrected source-native connection; it does not
prove that the whole joint shell is empty and does not authorize a new field.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceNativeAlgebraicEliminationUpdate

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineEnrichedProofFreeSource
open StageNineGlobalConnection
open StageNineGlobalIntegratedAction
open StageNineGravityAuxiliaryVariation
open StageNineHolonomicField
open StageNineJointShellResidualCarrier
open StageNineP286GaugeAuxiliaryEquation
open StageNineP286VaryingCurvatureAuxiliaryGraph
open StageNinePositiveSourceJointShellReachability
open StageNinePositiveSourceNativeGravityCurvatureBridge
open StageNineSourceGeneratedP286AffineConnectionGerm

noncomputable section

set_option autoImplicit false

/-- The source-native primitive kinematic seed.  The source produces exactly
the coframe and two connections; every other field is retained from the
input configuration. -/
def positiveSourceNativeKinematicSeed
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  installSourceP286AffineConnection positiveSmoothUnifiedSource.legacy
    (installPositiveSourceNativeGravityKinematics configuration)

/-- Algebraic elimination from actual seed curvatures.  The gravity and P286
auxiliaries are outputs of their current equations, not source fields. -/
def positiveSourceNativeAlgebraicEliminationUpdate
    (configuration : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  let seed := positiveSourceNativeKinematicSeed configuration
  { seed with
    gravityAuxiliary := fun point =>
      gravityInternalDualEquiv.symm
        (holonomicGravityCurvature seed point)
    gaugeAuxiliary := fun point =>
      generatedP286GaugeConstitutiveAuxiliary
        positiveSmoothUnifiedSource (seed.coframe point)
        (holonomicGaugeCurvature seed point) }

@[simp] theorem positiveSourceNativeKinematicSeed_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeKinematicSeed configuration).coframe =
      positiveSmoothUnifiedSource.legacy.coframeAt :=
  rfl

@[simp] theorem positiveSourceNativeKinematicSeed_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeKinematicSeed configuration).gravityConnection =
      generatedLorentzConnectionAt positiveSmoothUnifiedSource :=
  rfl

@[simp] theorem positiveSourceNativeKinematicSeed_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeKinematicSeed configuration).gaugeConnection =
      sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy :=
  rfl

@[simp] theorem positiveSourceNativeAlgebraicEliminationUpdate_coframe
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeAlgebraicEliminationUpdate configuration).coframe =
      positiveSmoothUnifiedSource.legacy.coframeAt :=
  rfl

@[simp] theorem positiveSourceNativeAlgebraicEliminationUpdate_gravityConnection
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeAlgebraicEliminationUpdate
      configuration).gravityConnection =
        generatedLorentzConnectionAt positiveSmoothUnifiedSource :=
  rfl

@[simp] theorem positiveSourceNativeAlgebraicEliminationUpdate_gaugeConnection
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeAlgebraicEliminationUpdate
      configuration).gaugeConnection =
        sourceP286AffineConnectionField positiveSmoothUnifiedSource.legacy :=
  rfl

/-- The unresolved primitive responsibilities are preserved, not zero-filled
or hidden in the source. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_preserves_responsibility
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).gravitySimplicityMultiplier =
          configuration.gravitySimplicityMultiplier ∧
      (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).scalar = configuration.scalar ∧
      (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).matter = configuration.matter ∧
      (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).conjugateMatter = configuration.conjugateMatter := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact source identity remains an admission/readout theorem rather than a
field added to the configuration. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_sameSourceProjection
    (configuration : StageNineHolonomicConfiguration) :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      (positiveSourceNativeAlgebraicEliminationUpdate configuration).coframe =
        positiveSmoothUnifiedSource.legacy.coframeAt ∧
      (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).gravityConnection =
          generatedLorentzConnectionAt positiveSmoothUnifiedSource ∧
      (positiveSourceNativeAlgebraicEliminationUpdate
        configuration).gaugeConnection =
          sourceP286AffineConnectionField
            positiveSmoothUnifiedSource.legacy := by
  exact ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven, rfl, rfl, rfl⟩

theorem positiveSourceNativeKinematicSeed_nondegenerate
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeKinematicSeed configuration).Nondegenerate := by
  intro point
  exact canonicalPhysicalSource_globally_nondegenerate point

theorem positiveSourceNativeAlgebraicEliminationUpdate_nondegenerate
    (configuration : StageNineHolonomicConfiguration) :
    (positiveSourceNativeAlgebraicEliminationUpdate
      configuration).Nondegenerate := by
  intro point
  exact canonicalPhysicalSource_globally_nondegenerate point

/-- Installing or eliminating auxiliaries does not change the actual gravity
curvature generated by the source-native primitive connection. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_gravityCurvature_eq_seed
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGravityCurvature
        (positiveSourceNativeAlgebraicEliminationUpdate configuration) point =
      holonomicGravityCurvature
        (positiveSourceNativeKinematicSeed configuration) point :=
  rfl

/-- The gravity auxiliary equation is solved from the actual seed curvature. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation
    (configuration : StageNineHolonomicConfiguration) :
    GravityAuxiliaryEquation
      (positiveSourceNativeAlgebraicEliminationUpdate configuration) := by
  intro point
  change
    holonomicGravityCurvature
        (positiveSourceNativeKinematicSeed configuration) point =
      gravityInternalDualEquiv
        (gravityInternalDualEquiv.symm
          (holonomicGravityCurvature
            (positiveSourceNativeKinematicSeed configuration) point))
  rw [LinearEquiv.apply_symm_apply]

/-- The P286 auxiliary equation is solved from the actual non-Abelian seed
curvature. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_p286AuxiliaryEquation
    (configuration : StageNineHolonomicConfiguration) :
    P286GaugeAuxiliaryEquation positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationUpdate configuration) := by
  intro point
  change
    holonomicGaugeCurvature
        (positiveSourceNativeKinematicSeed configuration) point =
      liftGaugeTwoFormOperator
        (((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) •
          coframeGaugeSpacetimeHodgeLinear
            (positiveSmoothUnifiedSource.legacy.coframeAt point))
        (generatedP286GaugeConstitutiveAuxiliary
          positiveSmoothUnifiedSource
          (positiveSmoothUnifiedSource.legacy.coframeAt point)
          (holonomicGaugeCurvature
            (positiveSourceNativeKinematicSeed configuration) point))
  exact (generatedP286GaugeConstitutiveAuxiliary_solves
    positiveSmoothUnifiedSource
    (positiveSmoothUnifiedSource.legacy.coframeAt point)
    (canonicalPhysicalSource_globally_nondegenerate point)
    (holonomicGaugeCurvature
      (positiveSourceNativeKinematicSeed configuration) point)).symm

theorem positiveSourceNativeAlgebraicEliminationUpdate_auxiliaryEquations
    (configuration : StageNineHolonomicConfiguration) :
    GravityAuxiliaryEquation
        (positiveSourceNativeAlgebraicEliminationUpdate configuration) ∧
      P286GaugeAuxiliaryEquation positiveSmoothUnifiedSource
        (positiveSourceNativeAlgebraicEliminationUpdate configuration) :=
  ⟨positiveSourceNativeAlgebraicEliminationUpdate_gravityAuxiliaryEquation _,
    positiveSourceNativeAlgebraicEliminationUpdate_p286AuxiliaryEquation _⟩

/-- Reapplying the deterministic source seed and the two unique algebraic
solvers makes no further choice. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_idempotent
    (configuration : StageNineHolonomicConfiguration) :
    positiveSourceNativeAlgebraicEliminationUpdate
        (positiveSourceNativeAlgebraicEliminationUpdate configuration) =
      positiveSourceNativeAlgebraicEliminationUpdate configuration := by
  apply StageNineHolonomicConfiguration.ext <;> rfl

/-- The actual holonomic update image belongs to the already declared
positive-source gravity-mouth carrier at the obstruction coordinate. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_preservesGravityMouth
    (configuration : StageNineHolonomicConfiguration) :
    PreservesPositiveSourceGravityMouthAtOrigin
      (positiveSourceNativeAlgebraicEliminationUpdate configuration) := by
  constructor
  · rfl
  · change
      holonomicGravityCurvature
          (installPositiveSourceNativeGravityKinematics configuration)
          0 0 0 =
        positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0
    exact installPositiveSourceNativeGravityKinematics_curvature_eq_source _

/-- Stable class-scoped no-go: source-native primitive kinematics plus unique
actual-curvature auxiliary elimination still cannot inhabit the complete
current joint zero fiber. -/
theorem positiveSourceNativeAlgebraicEliminationUpdate_not_jointZeroFiber
    (configuration : StageNineHolonomicConfiguration) :
    ¬ CurrentJointShellZeroFiber positiveSmoothUnifiedSource
      (positiveSourceNativeAlgebraicEliminationUpdate configuration) :=
  preservesPositiveSourceGravityMouth_not_jointShellZeroFiber _
    (positiveSourceNativeAlgebraicEliminationUpdate_preservesGravityMouth _)

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceNativeAlgebraicEliminationUpdate
