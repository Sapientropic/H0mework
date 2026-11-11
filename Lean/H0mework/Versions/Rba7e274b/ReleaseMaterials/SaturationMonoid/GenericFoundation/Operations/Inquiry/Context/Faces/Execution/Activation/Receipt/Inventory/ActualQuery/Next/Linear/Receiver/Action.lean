import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Next.Linear.Receiver.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace FullSourceReceiverLinearAction
-- Read the existing actual source literal action and material; no graph or final equation is supplied.
section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))
variable (action : PairValue (PairValue Value) s →+ PairValue (PairValue Value) s)

theorem actual_source_linear :
 (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw =
 .linear action (liftExpr (currentFullRaw frame cfg (S.actualOccurrence (Next.receiver frame cfg))).expression) :=
 congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (PairValue Value)) (Var := cfg.LowVar) (sort := s) => raw.expression)
  (reader_actual_source frame cfg action (S.actualOccurrence (Next.receiver frame cfg)))

theorem actual_source_eval (environment : Env (PairValue (PairValue Value)) cfg.LowVar) :
 (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw.eval environment =
 action ((liftExpr (currentFullRaw frame cfg (S.actualOccurrence (Next.receiver frame cfg))).expression).eval environment) :=
 congrArg (fun expression : Expr (PairValue (PairValue Value)) cfg.LowVar s => expression.eval environment)
  (actual_source_linear frame cfg action)

theorem actual_source_effect (environment increment : Env (PairValue (PairValue Value)) cfg.LowVar) :
 (R.actualMaterial (Next.receiver frame cfg) (programme frame cfg action)).raw.effect environment increment =
 action ((liftExpr (currentFullRaw frame cfg (S.actualOccurrence (Next.receiver frame cfg))).expression).effect environment increment) :=
 congrArg (fun expression : Expr (PairValue (PairValue Value)) cfg.LowVar s => expression.effect environment increment)
  (actual_source_linear frame cfg action)

end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {Nw : WorldRelationNetwork.{u}} {Voc : Vocabulary.{u}} {lower : SourceNativeLedgerRootClosure Nw Voc}
variable {current : Voc.Current} {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (material : RootGeneratedDebtActivationJointSource.Native.ResidualRequest.MaterialAt
 (Value := Value) (Var := Var) (sort := s) occurrence)
variable {Output : Type v} [AddCommGroup Output]

theorem read_material_update (read : Value s →+ Output) :
 read (material.raw.eval (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input material).environment) =
 read (material.raw.eval material.environment) + read (material.raw.effect material.environment material.increment) :=
 (congrArg read.toFun (Expr.eval_update material.raw material.environment material.increment)).trans (map_add read _ _)

end

end FullSourceReceiverLinearAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
