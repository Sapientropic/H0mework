import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovation.ColumnGram
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.GradedInnovationConsumer

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
namespace PaidSourceContentEnvironment.GradedInnovation.Integrated

open SourceOperationEffects SourceOperationScalarInventoryLift

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
attribute [local instance] baseGroups familyGroups
variable (read : J.Orbit →ₗ[ℤ] K) (sourceFrame : JointMeasured.Frame (K := K))

def nextJointValue (ordinal : Nat) :
    PairValue (L.Value (W K) (site read sourceFrame ordinal).1) .joint :=
  let same := next_joint_is_actual read sourceFrame ordinal
  cast (type_eq_of_heq same) ((site read sourceFrame (ordinal+1)).2.1.1.activeEnvironment .joint PUnit.unit)

private theorem next_joint_value (ordinal : Nat) :
    let packet := site read sourceFrame ordinal
    nextJointValue read sourceFrame ordinal =
      WB.oldPaid packet.2.1.1 packet.2.2.1+Native.nativeValue (factory read) packet := by
  have same := next_joint_is_actual read sourceFrame ordinal
  exact eq_of_heq ((cast_heq (type_eq_of_heq same)
    ((site read sourceFrame (ordinal+1)).2.1.1.activeEnvironment .joint PUnit.unit)).trans same)

/-- The actual next joint environment writes the residual from the action-derived Gram system. -/
theorem actual_next_from_column_actions (ordinal : Nat) :
    let packet := site read sourceFrame ordinal
    let output := featureValue packet.1 (nextJointValue read sourceFrame ordinal)
    let environment := Native.environmentTransport packet.2.2.2.down
      (Request.input (R.actualMaterial packet.2.1.1 packet.2.2.1)).environment
    let feature := featureEnvironment packet.1 environment
    let total := fun target name => (feature target name).1+(feature target name).2
    let decoded := J.decode (total .joint PUnit.unit)
    let frame := A.epoch packet.2.1.1
    let occurrence := S.actualOccurrence packet.2.1.1
    output.1+output.2 =
      (PaidSourceMacroHistory.programme.eval (JointMeasured.oldEnvironment decoded),
        columnActionInnovation read packet.1 frame occurrence ((JointMeasured.inputTerm read).eval decoded)) := by
  intro packet output environment feature total decoded frame occurrence
  have measured := congrArg (fun value : PairValue (L.Value (W K) packet.1) .joint =>
    let joint := featureValue packet.1 value
    joint.1+joint.2) (next_joint_value read sourceFrame ordinal)
  have readback := actual_innovation_from_column_actions read packet.1 frame occurrence
    ((JointMeasured.inputTerm read).eval decoded)
  have generated := congrArg (Prod.mk (PaidSourceMacroHistory.programme.eval (JointMeasured.oldEnvironment decoded)))
    readback
  have nativeWrite := born_fresh_vector read sourceFrame ordinal
  have actionWrite := nativeWrite.trans generated
  have literalWrite := measured.trans actionWrite
  exact literalWrite

end PaidSourceContentEnvironment.GradedInnovation.Integrated
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
