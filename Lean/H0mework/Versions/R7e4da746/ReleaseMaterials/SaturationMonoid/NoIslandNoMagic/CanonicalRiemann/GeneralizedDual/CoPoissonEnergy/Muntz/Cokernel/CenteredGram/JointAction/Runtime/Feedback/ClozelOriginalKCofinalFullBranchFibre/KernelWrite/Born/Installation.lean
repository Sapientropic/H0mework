import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.ExactCurrent

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw actualOccurrence)
end S
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (optionalSourceRoot epoch)
end A
namespace Acted
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted
 (component programme material)
end Acted
namespace Common
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Faces.Lower
 (component combined)
end Common
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory (component stockLaw)
end I
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (root visit)
end SO

section Installation
variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
local instance bornGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

private def rootComponentInstallation (grade : Nat)
 (frame : A.M.Frame (Value:=L.Value W grade) (Var:=X) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()))
 (component : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource)
 (hasComponent : (cfg.datum (A.epoch frame)).component=some component) :
 SourceNativeProjectionLaw.InstallationAt component (SO.root frame cfg).source.base.projectionLaw := by
 have head : SourceNativeProjectionLaw.InstallationAt component
   (S.baseRoot frame cfg).source.base.projectionLaw := by
  change SourceNativeProjectionLaw.InstallationAt component
   (A.optionalSourceRoot (S.base frame).root (cfg.datum (A.epoch frame)).component).source.base.projectionLaw
  rw [hasComponent]
  exact SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base component
 exact head.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame cfg).source.base
   (S.queryLaw (A.epoch frame) cfg)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame cfg).source.base
   (S.resultLaw (A.epoch frame) cfg)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame cfg).source.base
   (S.consumerLaw (A.epoch frame) cfg)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame cfg).source.base
   (S.compilationLaw (A.epoch frame) cfg))

private def stockOldInstallation (grade : Nat)
 (frame : A.M.Frame (Value:=L.Value W grade) (Var:=X) (sort:=()))
 (baseCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()))
 (component : SourceNativeProjectionLaw (S.base frame).root.source.base.restructuringSource.toLedgerSource)
 (hasComponent : (baseCfg.datum (A.epoch frame)).component=some component) :
 SourceNativeProjectionLaw.InstallationAt component
  (SO.root frame (AS.stockCfg baseCfg)).source.base.projectionLaw := by
 have head : SourceNativeProjectionLaw.InstallationAt component (I.component (A.epoch frame) baseCfg) := by
  unfold I.component
  rw [hasComponent]
  exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
   {(S.base frame).root.source.base with projectionLaw:=component} (I.stockLaw (A.epoch frame) baseCfg)
 exact head.trans (rootComponentInstallation grade frame (AS.stockCfg baseCfg)
  (I.component (A.epoch frame) baseCfg) rfl)

variable (code : Expr (PairValue W) X ())
variable (factory : SF.Factory W X ())
variable (generated : factory=AI.withActualInput code (SF.defaultFactory W X ()))
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
variable (sourceFrame : A.M.Frame
 (Value:=L.Value W (AS.nativeAfterAdmission factory packet).1)
 (Var:=X) (sort:=()))

/-- This embeds the original fixed Joint component through the actual programme's existing cofaces. -/
def actualJointInstallation :
 let native:=AS.nativeAfterAdmission factory packet
 SourceNativeProjectionLaw.InstallationAt
  (Acted.component native.2.1.2 (A.epoch sourceFrame))
  (SO.root sourceFrame (AS.stockCfg native.2.2.1)).source.base.projectionLaw := by
 subst factory
 dsimp only
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  let factory:=AI.withActualInput code (SF.defaultFactory W X ())
  let priorCfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
    (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()) :=
    ⟨X,datum,inventory,pairInventory⟩
  let seed:=AS.nextSeed factory grade data priorCfg rfl
  let baseCfg:=AS.nextBase factory grade data priorCfg rfl
  let mother:=(S.base sourceFrame).root
  let oldRoot:=A.optionalSourceRoot mother (some (Acted.component seed (A.epoch sourceFrame)))
  let oldLaw:=Common.combined (A.epoch sourceFrame) (Acted.programme seed)
  let oldComponent : SourceNativeProjectionLaw.InstallationAt
    (Acted.component seed (A.epoch sourceFrame)) oldLaw :=
   (SourceNativeProjectionLaw.InstallationAt.componentCoface mother.source.base
    (Acted.component seed (A.epoch sourceFrame))).trans
   (SourceNativeProjectionLaw.InstallationAt.inheritedCoface oldRoot.source.base
    (Common.component (A.epoch sourceFrame) (Acted.programme seed)))
  exact oldComponent.trans (stockOldInstallation _ sourceFrame baseCfg oldLaw rfl)


abbrev native := AS.nativeAfterAdmission factory packet
abbrev sourceOutcome := (Acted.component (native factory packet).2.1.2 (A.epoch sourceFrame)).outcomeAt
 PUnit.unit (S.actualOccurrence sourceFrame)
def actualRootOutcome := (SO.root sourceFrame (AS.stockCfg (native factory packet).2.2.1)).source.base.projectionLaw.outcomeAt
 ((actualJointInstallation code factory generated packet sourceFrame).embed PUnit.unit) (S.actualOccurrence sourceFrame)
theorem actual_root_inventory : HEq (actualRootOutcome code factory generated packet sourceFrame)
 (sourceOutcome factory packet sourceFrame) :=
 (actualJointInstallation code factory generated packet sourceFrame).outcome_heq (S.actualOccurrence sourceFrame) PUnit.unit

def actualTypedOutcome : type_of% (sourceOutcome factory packet sourceFrame) :=
 cast (type_eq_of_heq (actual_root_inventory code factory generated packet sourceFrame)) (actualRootOutcome code factory generated packet sourceFrame)
theorem actual_typed_outcome : actualTypedOutcome code factory generated packet sourceFrame=sourceOutcome factory packet sourceFrame :=
 eq_of_heq ((cast_heq_iff_heq _ _ _).mpr (actual_root_inventory code factory generated packet sourceFrame))

/-- Read the original material from the actual closed inventory's fixed inherited coordinate. -/
def actualRootRead : type_of% (Acted.material (native factory packet).2.1.2
 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame)) :=
 match actualTypedOutcome code factory generated packet sourceFrame with
 | .inl present => present.2
 | .inr absent => PEmpty.elim absent

theorem actual_root_read : actualRootRead code factory generated packet sourceFrame=
 Acted.material (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame) := by
 unfold actualRootRead
 rw [actual_typed_outcome]
 rfl

def actualRaw := (actualRootRead code factory generated packet sourceFrame).1.1.2.2
def actualPhase := (actualRootRead code factory generated packet sourceFrame).1.2.2.2.1
def actualQuery := (actualRootRead code factory generated packet sourceFrame).1.2.2.2.2.1
def actualWritten := (actualRootRead code factory generated packet sourceFrame).1.2.2.2.2.2

theorem actual_raw : actualRaw code factory generated packet sourceFrame=
 PR.raw (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame) :=
 congrArg (fun material => material.1.1.2.2) (actual_root_read code factory generated packet sourceFrame)

theorem actual_phase : actualPhase code factory generated packet sourceFrame=
 J.disposition (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame) :=
 congrArg (fun material => material.1.2.2.2.1) (actual_root_read code factory generated packet sourceFrame)

theorem actual_query : actualQuery code factory generated packet sourceFrame=
 J.queryRaw (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame)
  (J.disposition (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame)) :=
 congrArg (fun material => material.1.2.2.2.2.1) (actual_root_read code factory generated packet sourceFrame)

theorem actual_written : actualWritten code factory generated packet sourceFrame=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.completeWrittenInventory
  (native factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame) :=
 congrArg (fun material => material.1.2.2.2.2.2) (actual_root_read code factory generated packet sourceFrame)

end Installation

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
