import H0mework.Versions.R2.Physics.GravityTail.FixedRootNativeWrite

/-!
# First-assembly generated joint normal form

The unconditional root successor of SafeFinal is evaluated as a new exact
occurrence.  Its source-generated P286 A/F/B step and final constitutive
refresh settle the first three algebraic coordinates before any later
normal-form decision.  No equality of the SafeFinal residual is replayed onto
this revised current.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyGeneratedJointNormalForm

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineTopologicalP286GaugeThreeFormDuality

noncomputable section

private abbrev Source : SmoothUnifiedSource := positiveSmoothUnifiedSource

/-- The revised configuration is eliminated from the exact first-gravity
action trace rather than supplied as a future current. -/
private abbrev TraceFinal : StageNineHolonomicConfiguration :=
  (rootActionAt firstGravityCurrent).generatedTrace.finalConfiguration

def firstAssemblyGeneratedPointwiseJointNormalForm
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualOfActionJet Source point
    (generatedDiracDualFormNativePointwiseActionJet Source TraceFinal point)

theorem root_firstAssembly_classicalJoint_eq_generatedNormalForm
    (point : BasePoint) :
    (rootResidualAt firstAssemblyCurrent).classicalJoint point =
      firstAssemblyGeneratedPointwiseJointNormalForm point := by
  change diracDualFormNativePointwiseJointResidual Source
      firstAssemblyCurrent.configuration point = _
  unfold firstAssemblyGeneratedPointwiseJointNormalForm
  rw [← diracDualFormNativePointwiseJointResidual_eq_actionJetReadout]
  exact congrArg
    (fun configuration =>
      diracDualFormNativePointwiseJointResidual Source configuration point)
    (actionGeneratedTrace_finalConfiguration_eq_targetConfiguration
      (rootActionAt firstGravityCurrent)).symm

theorem root_firstAssembly_classicalJoint_eq_generatedNormalForm_section :
    (rootResidualAt firstAssemblyCurrent).classicalJoint =
      firstAssemblyGeneratedPointwiseJointNormalForm := by
  funext point
  exact root_firstAssembly_classicalJoint_eq_generatedNormalForm point

@[simp] theorem
    firstAssemblyGeneratedPointwiseJointNormalForm_gravityMultiplier_zero
    (point : BasePoint) :
    (firstAssemblyGeneratedPointwiseJointNormalForm point
      ).gravityMultiplier = 0 := by
  rw [← congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.gravityMultiplier
    (root_firstAssembly_classicalJoint_eq_generatedNormalForm point)]
  exact root_firstAssembly_gravityMultiplierResidual_eq_zero point

@[simp] theorem
    firstAssemblyGeneratedPointwiseJointNormalForm_gravityAuxiliary_zero
    (point : BasePoint) :
    (firstAssemblyGeneratedPointwiseJointNormalForm point
      ).gravityAuxiliary = 0 := by
  rw [← congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.gravityAuxiliary
    (root_firstAssembly_classicalJoint_eq_generatedNormalForm point)]
  exact root_firstAssembly_gravityAuxiliaryResidual_eq_zero point

@[simp] theorem
    firstAssemblyGeneratedPointwiseJointNormalForm_p286GaugeAuxiliary_zero
    (point : BasePoint) :
    (firstAssemblyGeneratedPointwiseJointNormalForm point
      ).p286GaugeAuxiliary = 0 := by
  rw [← congrArg
    DiracDualFormNativePointwiseJointResidualCarrier.p286GaugeAuxiliary
    (root_firstAssembly_classicalJoint_eq_generatedNormalForm point)]
  exact root_firstAssembly_p286GaugeAuxiliaryResidual_eq_zero point

/-- The Lorentz-connection Euler coordinate of the same generated occurrence.
It must remain visible even when a downstream attack chooses a different
nonzero coordinate; the three algebraic settlements do not erase it. -/
def firstAssemblyGeneratedLorentzConnectionEvaluatorDefect
    (point : BasePoint) :=
  (firstAssemblyGeneratedPointwiseJointNormalForm point).lorentzConnection

@[simp] theorem
    firstAssemblyGeneratedPointwiseJointNormalForm_lorentzConnection_eq_evaluatorDefect
    (point : BasePoint) :
    (firstAssemblyGeneratedPointwiseJointNormalForm point
      ).lorentzConnection =
        firstAssemblyGeneratedLorentzConnectionEvaluatorDefect point :=
  rfl

/-- The P286 connection Euler coordinate is another exact evaluator mouth
after the three generated algebraic settlements.  A concrete nonzero read is
already sufficient for same-row U7; a positive whole-zero face must also
settle the Lorentz coordinate above. -/
def firstAssemblyGeneratedP286ConnectionEvaluatorDefect
    (point : BasePoint) : P286GaugeThreeForm :=
  (firstAssemblyGeneratedPointwiseJointNormalForm point).p286GaugeConnection

@[simp] theorem
    firstAssemblyGeneratedPointwiseJointNormalForm_p286GaugeConnection_eq_evaluatorDefect
    (point : BasePoint) :
    (firstAssemblyGeneratedPointwiseJointNormalForm point
      ).p286GaugeConnection =
        firstAssemblyGeneratedP286ConnectionEvaluatorDefect point :=
  rfl

/-- Any computed nonzero revised normal form is again a same-row root
obstruction.  The next current remains compiler-owned. -/
def firstAssemblyGeneratedJointNormalFormObstructionAt
    (point : BasePoint)
    (nonzero : firstAssemblyGeneratedPointwiseJointNormalForm point ≠ 0) :
    N.ObstructionAt firstAssemblyCurrent :=
  rootClassicalJointObstructionAt point <| by
    rw [root_firstAssembly_classicalJoint_eq_generatedNormalForm point]
    exact nonzero

#print axioms root_firstAssembly_classicalJoint_eq_generatedNormalForm_section
#print axioms
  firstAssemblyGeneratedPointwiseJointNormalForm_gravityMultiplier_zero
#print axioms
  firstAssemblyGeneratedPointwiseJointNormalForm_gravityAuxiliary_zero
#print axioms
  firstAssemblyGeneratedPointwiseJointNormalForm_p286GaugeAuxiliary_zero

end
end StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyFirstAssemblyGeneratedJointNormalForm
end PhysicsCore
end SaturationMonoid
