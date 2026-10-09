import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Bootstrap.Runtime
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch optionalSourceRoot)
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base datum actualOccurrence root visit query baseRoot queryRoot resultRoot consumerRoot queryLaw resultLaw consumerLaw compilationLaw)
end S
end E
namespace Lower
variable {S : Type u} {W X : S → Type u} [∀ slot,AddCommGroup (W slot)] {s : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=W) (Var:=X) (sort:=s))
variable (cfg : E.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (actual : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
abbrev nativeRaw := (cfg.datum frame).reader actual
def liftedRaw : SourceOperationInquiry.Context.Raw
 (PhysicalValue:=PairValue (PairValue W)) (PhysicalVar:=cfg.LowVar) (sort:=s) :=
 ⟨pairEnvironment (nativeRaw frame cfg actual).environment 0,liftExpr (nativeRaw frame cfg actual).expression⟩
def component : SourceNativeProjectionLaw (E.S.base frame).root.source.base.restructuringSource.toLedgerSource where
 Projection:=PUnit
 ActiveAt:=fun _ {_current} _ => PUnit
 InactiveAt:=fun _ {_current} _ => PEmpty
 classify:=fun _ {_current} _ => .inl PUnit.unit
 PayloadAt:=fun _ {_current} _ _ => SourceOperationInquiry.Context.Raw
  (PhysicalValue:=PairValue (PairValue W)) (PhysicalVar:=cfg.LowVar) (sort:=s)
 project:=fun _ {_current} supplied _ => liftedRaw frame cfg supplied
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
theorem lifted_source : (face frame cfg).rootRead=liftedRaw (E.epoch frame) cfg (E.S.actualOccurrence frame) := rfl

def restriction : SourceOperationInquiry.Context.RawRestrictionAt
 (PhysicalValue:=PairValue (PairValue W)) (PhysicalVar:=cfg.LowVar) (sort:=s)
 (⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered,
  ⟨RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt,
   (E.S.root frame (configuration cfg)).toAuthoritativeRoot,E.S.visit frame (configuration cfg)⟩⟩ : AnyAuthoritativeRootCurrent.{u}) where
 projection:=(face frame cfg).projection
 active:=(face frame cfg).active
 classifier_eq:=(face frame cfg).classifier_eq
 payload_eq:=rfl


theorem lifted_eval : (liftedRaw frame cfg actual).expression.eval (liftedRaw frame cfg actual).environment=
 ((nativeRaw frame cfg actual).expression.eval (nativeRaw frame cfg actual).environment,0) := by
 rw [liftedRaw,eval_liftExpr,Expr.effect_zero]
theorem source_eval : (face frame cfg).rootRead.expression.eval (face frame cfg).rootRead.environment=
 ((E.S.query frame cfg).raw.expression.eval (E.S.query frame cfg).raw.environment,0) :=
 lifted_eval (E.epoch frame) cfg (E.S.actualOccurrence frame)
def liftedTrace := execution (liftedRaw frame cfg actual).environment (liftedRaw frame cfg actual).expression

theorem source_fee : (liftedTrace frame cfg actual).length=remaining (nativeRaw frame cfg actual).expression :=
 (execution_length _ _).trans (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.DebtReplay.Math.lift_fee _)
end Lower
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
