import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
namespace Calculation.Common
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch optionalSourceRoot)
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base datum actualOccurrence root visit query baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw frames)
end S
end E
namespace Direct
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : E.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev nativeRaw := (cfg.datum frame).reader actual
def directRaw : SourceOperationInquiry.Context.Raw
 (PhysicalValue:=PairValue W) (PhysicalVar:=cfg.LowVar) (sort:=s) :=
 nativeRaw frame cfg actual
def component : SourceNativeProjectionLaw (E.S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit
 ActiveAt:=fun _ {_current} _ => PUnit
 InactiveAt:=fun _ {_current} _ => PEmpty
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} _ _ => SourceOperationInquiry.Context.Raw
  (PhysicalValue:=PairValue W) (PhysicalVar:=cfg.LowVar) (sort:=s)
 project:=fun _ {_current} supplied _ => directRaw frame cfg supplied
def combined := (E.optionalSourceRoot (E.S.base frame).root (cfg.datum frame).component).source.base.withProjectionCoface
 (component frame cfg) |>.projectionLaw
def configuration := {cfg with datum:=fun sourceFrame => {(cfg.datum sourceFrame) with
 component:=some (combined sourceFrame cfg)}}

theorem reader_literal : ((configuration cfg).datum frame).reader actual=(cfg.datum frame).reader actual := rfl
theorem decoder_literal : ((configuration cfg).datum frame).nextEnvironmentRead=(cfg.datum frame).nextEnvironmentRead := rfl
theorem dependent_decoder_literal : ((configuration cfg).datum frame).nextEnvironmentReadAt=(cfg.datum frame).nextEnvironmentReadAt := rfl

def componentEmbedding := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (E.optionalSourceRoot (E.S.base frame).root (cfg.datum frame).component).source.base (component frame cfg)
def installation := (componentEmbedding (E.epoch frame) cfg).trans
 (SourceNativeProjectionLaw.InstallationAt.componentCoface (E.S.base frame).root.source.base
  (combined (E.epoch frame) cfg)) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.S.baseRoot frame (configuration cfg)).source.base
  (E.S.queryLaw (E.epoch frame) (configuration cfg))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.S.queryRoot frame (configuration cfg)).source.base
  (E.S.resultLaw (E.epoch frame) (configuration cfg))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.S.resultRoot frame (configuration cfg)).source.base
  (E.S.consumerLaw (E.epoch frame) (configuration cfg))) |>.trans
 (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (E.S.consumerRoot frame (configuration cfg)).source.base
  (E.S.compilationLaw (E.epoch frame) (configuration cfg)))

def face : SourceNativeRootSemanticFaceAt (E.S.root frame (configuration cfg)) (E.S.visit frame (configuration cfg)) where
 projection:=(installation frame cfg).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl
theorem direct_source : (face frame cfg).rootRead=directRaw (E.epoch frame) cfg (E.S.actualOccurrence frame) := rfl

def restriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=PairValue W) (PhysicalVar:=cfg.LowVar) (sort:=s)
 (Registry.presentation frame (configuration cfg)).erase where
 projection:=(face frame cfg).projection
 active:=(face frame cfg).active
 classifier_eq:=(face frame cfg).classifier_eq
 payload_eq:=rfl
end Direct
end Calculation.Common
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
