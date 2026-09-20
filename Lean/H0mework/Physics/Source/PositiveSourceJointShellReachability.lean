import H0mework.Physics.Geometry.JointShellZeroFiber
import H0mework.Physics.Source.SimultaneousSourceContainment
import H0mework.Physics.Geometry.GravityAlgebraicShellLocus

/-!
# S9-C3g4: exact-lineage existing-gravity-mouth reachability no-go

The current joint residual zero fiber now has a precise type.  This module
therefore reuses the old origin mismatch only at its legitimate scope.  Its
primary carrier class consists of all pointwise algebraic completions that
preserve the already generated positive-source coframe and Lorentz-curvature
readouts at the origin while leaving the auxiliary and multiplier arbitrary.
That class is explicitly inhabited, but none of its members lies on the
current gravity algebraic shell.

No claim is made that the entire current gravity shell is empty.  The theorem
only says that this explicitly defined existing-gravity mouth cannot be
repaired by selecting auxiliary or multiplier values.  A holonomic joint-zero
no-go is then a conditional corollary for configurations preserving the same
mouth.  Hence this is a reachability diagnostic for one stable pointwise
carrier class, not a Stage-9 producer and not permission to preselect a repair
field.
-/

namespace SaturationMonoid.PhysicsCore.StageNinePositiveSourceJointShellReachability

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineBlockwiseConstitutive
open StageNinePlebanskiMultiplierVariation
open StageNineGravityAuxiliaryVariation
open StageNineJointShellResidualCarrier
open StageNineJointShellZeroFiber
open StageNineSimultaneousSourceContainment
open StageNineGravityAlgebraicShellLocus
open RepresentationArithmeticAtomProjectionDefect
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization

noncomputable section

set_option autoImplicit false

/-- Exact P506/L0 lineage is an admission/reference identity, not a complete
identity for the enriched Stage-9 primitive source.  In particular it does
not select the continuous contact residual or its generated flow. -/
theorem generatedP506L0Lineage_not_injective_on_smoothUnifiedSource :
    ¬ Function.Injective
      (fun source : SmoothUnifiedSource =>
        source.stageEight.generatedP506L0Lineage) := by
  intro injective
  have sameLineage :
      zeroRateSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage :=
    rfl
  have sameSource := injective sameLineage
  exact zeroRate_positive_generatedFlows_distinct
    (congrArg generatedUnitaryFlow sameSource)

/-- All pointwise algebraic completions of the existing positive-source
gravity mouth.  Auxiliary and multiplier remain arbitrary and visible. -/
def positiveSourceGravityAlgebraicCompletion
    (auxiliary multiplier : PhysicalBivector) :
    CurrentGravityAlgebraicPoint where
  coframe := positiveSmoothUnifiedSource.legacy.coframeAt 0
  curvature := positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin
  auxiliary := auxiliary
  multiplier := multiplier

/-- The defined candidate class is inhabited without supplying a shell or
stationarity witness. -/
theorem positiveSourceGravityAlgebraicCompletionClass_nonempty :
    Nonempty { point : CurrentGravityAlgebraicPoint //
      point.coframe = positiveSmoothUnifiedSource.legacy.coframeAt 0 ∧
      point.curvature =
        positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin } :=
  ⟨⟨positiveSourceGravityAlgebraicCompletion 0 0, rfl, rfl⟩⟩

/-- Stable pointwise no-go: no choice of the existing auxiliary or multiplier
fields repairs the positive-source origin mouth. -/
theorem positiveSourceGravityAlgebraicCompletion_not_onShell
    (auxiliary multiplier : PhysicalBivector) :
    ¬ OnCurrentGravityAlgebraicShell
      (positiveSourceGravityAlgebraicCompletion auxiliary multiplier) := by
  rintro ⟨simplicity, curvature⟩
  have auxiliaryEquality :
      auxiliary = physicalIIPlusBivector
        (positiveSmoothUnifiedSource.legacy.coframeAt 0) := by
    simpa [positiveSourceGravityAlgebraicCompletion] using simplicity
  have forbiddenEquality :
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 =
        gravityInternalDualEquiv
          (physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0)) 0 0 := by
    simpa [positiveSourceGravityAlgebraicCompletion, auxiliaryEquality] using
      congrFun (congrFun curvature 0) 0
  exact canonicalPhysicalSource_origin_curvature_ne_gravityDualIIPlus
    forbiddenEquality

/-- Equivalent class-wide statement, independent of a chosen completion. -/
theorem positiveSourceGravityAlgebraicCompletionClass_disjoint_shell
    (point : CurrentGravityAlgebraicPoint)
    (coframe : point.coframe =
      positiveSmoothUnifiedSource.legacy.coframeAt 0)
    (curvature : point.curvature =
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin) :
    ¬ OnCurrentGravityAlgebraicShell point := by
  intro onShell
  have completionEquality : point =
      positiveSourceGravityAlgebraicCompletion point.auxiliary
        point.multiplier := by
    cases point
    simp_all [positiveSourceGravityAlgebraicCompletion]
  rw [completionEquality] at onShell
  exact positiveSourceGravityAlgebraicCompletion_not_onShell _ _ onShell

/-- The stable carrier class that preserves the actual existing positive
source gravity readouts at the origin.  It constrains no downstream field. -/
structure PreservesPositiveSourceGravityMouthAtOrigin
    (configuration : StageNineHolonomicConfiguration) : Prop where
  coframe : configuration.coframe 0 =
    positiveSmoothUnifiedSource.legacy.coframeAt 0
  curvature : holonomicGravityCurvature configuration 0 0 0 =
    positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0

/-- No completion of the other current fields can place the existing positive
source gravity mouth in the joint residual zero fiber. -/
theorem preservesPositiveSourceGravityMouth_not_jointShellZeroFiber
    (configuration : StageNineHolonomicConfiguration)
    (preserves :
      PreservesPositiveSourceGravityMouthAtOrigin configuration) :
    ¬ CurrentJointShellZeroFiber positiveSmoothUnifiedSource configuration := by
  intro zeroFiber
  have equations :=
    (currentJointShellZeroFiber_iff_strongEquation
      positiveSmoothUnifiedSource configuration).mp zeroFiber
  have auxiliaryComponent := congrFun
    (congrFun (equations.gravityAuxiliary 0) 0) 0
  rw [equations.gravitySimplicity 0] at auxiliaryComponent
  have forbiddenEquality :
      positiveSmoothUnifiedSource.legacy.lorentzCurvatureAtOrigin 0 0 =
        gravityInternalDualEquiv
          (physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0)) 0 0 := by
    calc
      _ = holonomicGravityCurvature configuration 0 0 0 :=
        preserves.curvature.symm
      _ = gravityInternalDualEquiv
          (physicalIIPlusBivector (configuration.coframe 0)) 0 0 :=
        auxiliaryComponent
      _ = gravityInternalDualEquiv
          (physicalIIPlusBivector
            (positiveSmoothUnifiedSource.legacy.coframeAt 0)) 0 0 := by
        rw [preserves.coframe]
  exact canonicalPhysicalSource_origin_curvature_ne_gravityDualIIPlus
    forbiddenEquality

/-- The no-go is tied to the exact P506/L0 lineage generated by the positive
source; exact lineage is not stored in the algebraic or holonomic carrier. -/
theorem positiveExactLineage_existingGravityMouth_unreachable :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      (∀ auxiliary multiplier,
        ¬ OnCurrentGravityAlgebraicShell
          (positiveSourceGravityAlgebraicCompletion auxiliary multiplier)) ∧
      ∀ configuration : StageNineHolonomicConfiguration,
        PreservesPositiveSourceGravityMouthAtOrigin configuration →
          ¬ CurrentJointShellZeroFiber positiveSmoothUnifiedSource
            configuration :=
  ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSourceGravityAlgebraicCompletion_not_onShell,
    preservesPositiveSourceGravityMouth_not_jointShellZeroFiber⟩

end

end SaturationMonoid.PhysicsCore.StageNinePositiveSourceJointShellReachability
