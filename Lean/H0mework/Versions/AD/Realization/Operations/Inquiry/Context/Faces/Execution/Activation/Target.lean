import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inquiry
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Target.Coface

/-! An actual residual first step generates the original complete admission
target. Its next epoch source adds the same uniform calculation families
before emission and inherits every original admission field and receipt. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects DebtActivationWorld
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry
  (sourceAction residual_action targetAt)
end J
namespace C
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (World JointV originalOccurrence)
end C

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
namespace Shared
variable (configuration : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def request := frame.request
def programme := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.programme
  frame.old frame.registered frame.packetAt frame.depth
def firstStep := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source.firstStep
  frame.old frame.registered frame.packetAt frame.environment frame.depth

theorem first_action : J.sourceAction (answeredState frame configuration) (request frame) (programme frame) = .inr (firstStep frame) :=
  J.residual_action frame.old frame.registered frame.packetAt frame.environment frame.depth

def nextBorn : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) where
  N := C.World frame.registered
  V := C.JointV frame.registered frame.packetAt
  old := answeredState frame configuration
  registered := request frame
  packetAt := programme frame
  environment := fun {_current} occurrence =>
    match (datum frame configuration).nextEnvironmentRead with
    | none => frame.environment (C.originalOccurrence frame.registered frame.packetAt occurrence)
    | some read => read ((resultFace frame configuration).rootRead.2.2.1)
  depth := 0
  inventory := configuration.nextInventory frame
  pairInventory := configuration.nextPairInventory frame

def oldInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (nextBorn frame configuration).currentState.root.source.base
  (SourceOperationInquiry.Context.Installation.component (epoch (nextBorn frame configuration)))).trans
  (baseInstallation (nextBorn frame configuration) configuration) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (baseRoot (nextBorn frame configuration) configuration).source.base
    (queryLaw (epoch (nextBorn frame configuration)) configuration)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (queryRoot (nextBorn frame configuration) configuration).source.base
    (resultLaw (epoch (nextBorn frame configuration)) configuration)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (resultRoot (nextBorn frame configuration) configuration).source.base
    (consumerLaw (epoch (nextBorn frame configuration)) configuration)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerRoot (nextBorn frame configuration) configuration).source.base
    (compilationLaw (epoch (nextBorn frame configuration)) configuration))

def originalTarget (event : ExactTemporalCausalRootEventAt (root frame configuration).toAuthoritativeRoot.toLedgerRoot (visit frame configuration)) :=
  J.targetAt (answeredState frame configuration) (query frame configuration) (request frame) (programme frame)
    (authority frame configuration) (firstStep frame) (first_action frame configuration) event

def targetAt (event : ExactTemporalCausalRootEventAt (root frame configuration).toAuthoritativeRoot.toLedgerRoot (visit frame configuration)) :
    SourceNativeDebtAdmissionActualActionTargetAt
      (N := C.World frame.registered) (V := C.JointV frame.registered frame.packetAt)
      (root frame configuration) (visit frame configuration) event
      (frame.currentState.entryAt PUnit.unit) (authority frame configuration) :=
  let born := nextBorn frame configuration
  let original := originalTarget frame configuration event
  let material := targetCoface original (SourceOperationInquiry.Context.Installation.component (epoch born))
  let configured := optionalTargetCoface material (datum born configuration).component
  let withQuery := targetCoface configured (queryLaw (epoch born) configuration)
  let withResult := targetCoface withQuery (resultLaw (epoch born) configuration)
  let withConsumer := targetCoface withResult (consumerLaw (epoch born) configuration)
  targetCoface withConsumer (compilationLaw (epoch born) configuration)


theorem target_root (event : ExactTemporalCausalRootEventAt (root frame configuration).toAuthoritativeRoot.toLedgerRoot (visit frame configuration)) :
    (targetAt frame configuration event).targetRoot = root (nextBorn frame configuration) configuration := rfl

theorem target_next (event : ExactTemporalCausalRootEventAt (root frame configuration).toAuthoritativeRoot.toLedgerRoot (visit frame configuration)) :
    (targetAt frame configuration event).targetAnswerAndNext.nextCurrent =
      ⟨_, (root (nextBorn frame configuration) configuration).toAuthoritativeRoot,
        visit (nextBorn frame configuration) configuration⟩ := by
  change (root (nextBorn frame configuration) configuration).generatedNextCurrentAt
      (.finite (root (nextBorn frame configuration) configuration).toAuthoritativeRoot.toRoot.initialVisit) = _
  apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
  rfl

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt (root frame configuration) (visit frame configuration)
    (frame.currentState.entryAt PUnit.unit) (authority frame configuration) where
  targetAt := targetAt frame configuration

end Shared

abbrev request := Shared.request frame
abbrev programme := Shared.programme frame
abbrev firstStep := Shared.firstStep frame
abbrev first_action := Shared.first_action frame originalProgramme
abbrev nextBorn := Shared.nextBorn frame originalProgramme
abbrev oldInstallation := Shared.oldInstallation frame originalProgramme
abbrev originalTarget := Shared.originalTarget frame originalProgramme
abbrev targetAt := Shared.targetAt frame originalProgramme
abbrev birthProgram := Shared.birthProgram frame originalProgramme

end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
