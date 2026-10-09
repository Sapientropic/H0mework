import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Difference.Inquiry.Installation
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Difference.Inquiry.Input

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (prior:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev installedCfg:=FullSource.configuration binding n prior
abbrev originalState:=Q.answeredState (currentFrame binding n prior) (installedCfg binding n prior)
abbrev calculationState:=Sealed.state (originalState binding n prior) (reader binding n prior)
 (Q.query (currentFrame binding n prior) (installedCfg binding n prior))
abbrev calculationInput:=Sealed.input (originalState binding n prior) (reader binding n prior)
 (Q.query (currentFrame binding n prior) (installedCfg binding n prior))
abbrev calculationQuery:=(calculationInput binding n prior).query

def fullMaterialInstallation:=
 (FullSource.installation binding n prior (currentFrame binding n prior)).trans
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.oldInstallation
  (originalState binding n prior) (reader binding n prior)) |>.trans
 (Sealed.installation (originalState binding n prior) (reader binding n prior)
  (Q.query (currentFrame binding n prior) (installedCfg binding n prior)))

def fullMaterialFace:SourceNativeRootSemanticFaceAt (calculationState binding n prior).root
 (calculationState binding n prior).visit where
 projection:=(fullMaterialInstallation binding n prior).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl

def updatedEnvironment:Env (PairValue (Lower.Value W (n+1+1))) X:=
 SourceGeneratedInquiryReceiptAction.afterEnvironment (currentFrame binding n prior) (installedCfg binding n prior)

def storedResult
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence (currentFrame binding n prior)
  (current:=(originalState binding n prior).visit.current)):=
 (calculationState binding n prior).root.toAuthoritativeRoot.source.projectionLaw.project
  ((fullMaterialInstallation binding n prior).embed PUnit.unit) supplied PUnit.unit

def material
 (supplied:SourceOperationInquiry.Context.Installation.Occurrence (currentFrame binding n prior)
  (current:=(originalState binding n prior).visit.current)):
 Req.MaterialAt (lower:=(calculationState binding n prior).root.toAuthoritativeRoot.toLedgerRoot)
  (Value:=PairValue (Lower.Value W (n+1+1))) (Var:=X) (sort:=s) supplied:=
 { environment:=(reader binding n prior supplied).environment
   increment:=updatedEnvironment binding n prior-(reader binding n prior supplied).environment
   raw:=(reader binding n prior supplied).expression
   state:=(storedResult binding n prior supplied).1.2.1
   owner:=Q.entryAt (currentFrame binding n prior) supplied }
abbrev actualMaterial:=material binding n prior (Q.actualOccurrence (currentFrame binding n prior))
def registered:RootGeneratedDebtActivationJointSource.RegisteredAt
 (Value:=PairValue (Lower.Value W (n+1+1))) (Var:=X) (sort:=s)
 (calculationState binding n prior).root.toAuthoritativeRoot.toLedgerRoot (calculationState binding n prior).visit.current:=
 RootGeneratedDebtActivationJointSource.register
 (fun supplied=>Req.input (material binding n prior supplied))
def packetAt (candidate:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current
 (currentFrame binding n prior).registered):=
 (RootGeneratedDebtActivationJointSource.Successor.read?
  (calculationState binding n prior).root.toAuthoritativeRoot.toLedgerRoot candidate).get (by rfl)

private theorem not_settled
 (settled:SourceOperationExecutionDebt.Settlement
  (RootGeneratedDebtActivationJointSource.initialEvent (registered binding n prior)).state):False:=by
 have zero:=(RootGeneratedDebtActivationJointSource.Idle.law
  (registered binding n prior).input.environment (registered binding n prior).input.expression).settlement_budget_zero settled
 have positive:=Req.budget (actualMaterial binding n prior)
 change remaining (Req.expression (actualMaterial binding n prior))=0 at zero
 omega

def firstStep:=match _selected:RootGeneratedDebtActivationJointSource.mathAction
 (RootGeneratedDebtActivationJointSource.initialEvent (registered binding n prior)) with
 | .inl settled=>False.elim (not_settled binding n prior settled)
 | .inr paid=>paid

theorem first_action:RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction
 (calculationState binding n prior) (registered binding n prior) (packetAt binding n prior)=
 .inr (firstStep binding n prior):=by
 apply (RootGeneratedDebtActivationJointSource.Successor.Inquiry.sourceAction_eq
  (calculationState binding n prior) (registered binding n prior) (packetAt binding n prior)).trans
 unfold firstStep
 cases selected:RootGeneratedDebtActivationJointSource.mathAction
  (RootGeneratedDebtActivationJointSource.initialEvent (registered binding n prior)) with
 | inl settled=>exact False.elim (not_settled binding n prior settled)
 | inr paid=>rfl

def birthProgram:=RootGeneratedDebtActivationJointSource.Successor.Inquiry.birthProgram
 (calculationState binding n prior) (calculationQuery binding n prior) (registered binding n prior)
 (packetAt binding n prior)
 ((calculationState binding n prior).authorityAt (calculationQuery binding n prior))
 (firstStep binding n prior) (first_action binding n prior)
def sourceEvent:=(calculationState binding n prior).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (calculationState binding n prior).visit
def generatedAction:=(birthProgram binding n prior).generate (sourceEvent binding n prior)

theorem full_calculation_consumed:(calculationState binding n prior).compileInquiry (calculationQuery binding n prior)=
 .answered (Sealed.resultFace (originalState binding n prior) (reader binding n prior)
  (Q.query (currentFrame binding n prior) (installedCfg binding n prior)))
 (Sealed.consumer (originalState binding n prior) (reader binding n prior)
  (Q.query (currentFrame binding n prior) (installedCfg binding n prior)) (calculationQuery binding n prior)):=
 Sealed.compiles _ _ _

theorem original_compilation:type_of% (C.original_compilation_preserved
 (originalState binding n prior) (reader binding n prior)
 (Q.query (currentFrame binding n prior) (installedCfg binding n prior))):=
 C.original_compilation_preserved _ _ _

theorem inverse:type_of% (Req.residual_value (R:=ℤ) (actualMaterial binding n prior)):=
 Req.residual_value (actualMaterial binding n prior)
theorem effect:type_of% (Req.updated_value (R:=ℤ) (actualMaterial binding n prior)):=
 Req.updated_value (actualMaterial binding n prior)

end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
