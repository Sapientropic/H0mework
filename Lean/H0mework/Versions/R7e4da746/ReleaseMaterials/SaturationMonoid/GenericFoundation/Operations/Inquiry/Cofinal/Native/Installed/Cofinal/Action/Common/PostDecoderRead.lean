import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Common.RootConsumer.Semantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCofinalCommonAction.PostDecoder
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations
namespace SA
export ActualCofinalSourceAction (sourceBorn sourceWordAction actual_next_packet packetTransport)
end SA
namespace RM
export ActualCofinalResidualModelSplice (packetWordTransport packetLanguageWord)
end RM
variable {Sorts:Type u} {W X:Sorts→Type u} [∀ target,AddCommGroup (W target)] {s:Sorts}
local instance readerGroups (grade:Nat) (target:Sorts) : AddCommGroup (T.Value W grade target) := T.groups W grade target

private theorem packet_read
 {first second:A.AdmissionPacket (W:=W) (X:=X) (s:=s)} (same:first=second)
 (word:Formal ℤ (T.Value W first.1) X s) :
 HEq (evaluation (R:=ℤ) second.2.1.1.activeEnvironment (RM.packetWordTransport same word))
  (evaluation (R:=ℤ) first.2.1.1.activeEnvironment word) := by
 cases same
 rfl

private theorem language_read {Y Z:Sorts→Type u} (same:Y=Z)
 (packet:A.AdmissionPacket (W:=W) (X:=Y) (s:=s))
 (word:Formal ℤ (T.Value W packet.1) Y s) :
 HEq (evaluation (R:=ℤ) (SA.packetTransport same packet).2.1.1.activeEnvironment
   (RM.packetLanguageWord same packet word))
  (evaluation (R:=ℤ) packet.2.1.1.activeEnvironment word) := by
 cases same
 rfl

variable (factory:T.Factory W X s) (initial:T.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg:T.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s)) (language:cfg.LowVar=X)

/-- The actual next site's decoded observer reads the same full acted source word. -/
theorem next_action_read (ordinal:Nat) (word:T.Words factory initial cfg language ordinal) :
 HEq (evaluation (R:=ℤ) (site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
   (siteAction factory initial cfg language ordinal word))
  (evaluation (R:=ℤ) (SA.sourceBorn factory (site factory initial cfg language ordinal)).2.1.1.activeEnvironment
   (SA.sourceWordAction (site factory initial cfg language ordinal) word)) := by
 change HEq
  (evaluation (R:=ℤ) (site factory initial cfg language (ordinal+1)).2.1.1.activeEnvironment
   (RM.packetWordTransport (SA.actual_next_packet factory initial cfg language ordinal).symm
    (RM.packetLanguageWord (site factory initial cfg language ordinal).2.2.2.down
     (SA.sourceBorn factory (site factory initial cfg language ordinal))
     (SA.sourceWordAction (site factory initial cfg language ordinal) word))))
  (evaluation (R:=ℤ) (SA.sourceBorn factory (site factory initial cfg language ordinal)).2.1.1.activeEnvironment
   (SA.sourceWordAction (site factory initial cfg language ordinal) word))
 exact (packet_read (SA.actual_next_packet factory initial cfg language ordinal).symm _).trans
  (language_read (site factory initial cfg language ordinal).2.2.2.down
   (SA.sourceBorn factory (site factory initial cfg language ordinal)) _)

private theorem material_input_transport
 {Value Var:Sorts→Type u} [∀ target,AddCommGroup (Value target)]
 (first second:AnyAuthoritativeRootCurrent.{u}) (same:first=second)
 (material:ActualCanonicalBornSource.MaterialAtCurrent (Value:=Value) (Var:=Var) (s:=s) first) :
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
   (Eq.mp (congrArg (ActualCanonicalBornSource.MaterialAtCurrent (Value:=Value) (Var:=Var) (s:=s)) same) material)).environment =
 (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input material).environment := by
 cases same
 rfl

attribute [local irreducible] ActualCofinalInstalledRaw.currentAtStop
 ActualCofinalInstalledRaw.AS.admissionPresentation

/-- The existing updated cofinal observer is the literal active Env of its complete packet. -/
theorem updated_environment_current (ordinal:Nat) :
 ActualCofinalNativeTower.updatedEnvironment factory initial cfg language ordinal =
 (site factory initial cfg language ordinal).2.1.1.activeEnvironment := by
 have transported :
  (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
   (ActualCofinalInstalledRaw.materialAtStop factory initial cfg language ordinal)).environment =
  (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
   (ActualNativeRelationTransport.paid (site factory initial cfg language ordinal).2.1.1)).environment :=
  material_input_transport (Value:=T.NativeValue factory initial cfg language ordinal) (Var:=X) (s:=s)
   (ActualCofinalInstalledRaw.SO.current (site factory initial cfg language ordinal).2.1.1
    (site factory initial cfg language ordinal).2.2.1)
   (ActualCofinalInstalledRaw.currentAtStop factory initial cfg language ordinal)
   (ActualCofinalInstalledRaw.actual_current factory initial cfg language ordinal).symm
   (ActualNativeRelationTransport.paid (site factory initial cfg language ordinal).2.1.1)
 exact transported.trans
  (SourceFamilyActualCurrentMaterialRootedEffect.paid_updated_environment
   (site factory initial cfg language ordinal).2.1.1)

end ActualCofinalCommonAction.PostDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
