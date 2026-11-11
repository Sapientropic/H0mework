import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
 (withCalculation codeAt actual_source_code actual_updated_total next_action_code next_actual_updated_total cofinal_source_code native_after_admission_code born_after_native_code)
end CF
namespace CM
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory reader reader_pair reader_paid_environment actual_action_isLeft)
end CM
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
end A
namespace I
export SourceOperationInquiry.Context.Installation (rawAt nextRawAt materialAt)
end I
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue)
end WB
namespace SF
export OriginalKSourceFeedbackSuccessorAction.Mother.SF (Seed cfg)
end SF
variable {W X : Unit → Type} [∀ target, AddCommGroup (W target)]
local instance cofinalSourceGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value W grade target) := L.groups W grade target
variable (sourceCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())

/-- The existing current-material query reader supplies the full actual before/increment pair before the literal source AST is installed. -/
def sourceCofinalFactory := CF.withCalculation (CM.queryFactory factory)
 sourceCode

variable (grade : Nat) (seed : SF.Seed W X () grade)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=L.Value W grade) (Var:=X) (sort:=()))
abbrev sourceCofinalCfg := SF.cfg (sourceCofinalFactory sourceCode factory) grade seed

/-- This actual calculation consumes the datum's original common-material reader environment, not an unrelated calculationReader with an equal value. -/
theorem source_cofinal_reader_environment :
 (R.actualMaterial frame (sourceCofinalCfg sourceCode factory grade seed)).environment=
 (CM.reader (A.epoch frame) (S.actualOccurrence frame)).environment := rfl

/-- The actual current material generates both source environment feet with its complete action difference. -/
theorem source_cofinal_full_environment :
 (R.actualMaterial frame (sourceCofinalCfg sourceCode factory grade seed)).environment=
 pairEnvironment (I.rawAt (A.epoch frame) (S.actualOccurrence frame)).environment
  ((I.nextRawAt (A.epoch frame) (S.actualOccurrence frame)).environment-
   (I.rawAt (A.epoch frame) (S.actualOccurrence frame)).environment) := rfl

/-- The source literal code is installed before the actual material evaluation. -/
theorem source_cofinal_actual_code :
 (R.actualMaterial frame (sourceCofinalCfg sourceCode factory grade seed)).raw=
 CF.codeAt sourceCode grade :=
 CF.actual_source_code (CM.queryFactory factory) _ grade seed frame

/-- The source action and actual material update generate the native total which the existing writer consumes. -/
theorem source_cofinal_actual_updated_total
 (write : PairValue (L.Value W grade) ()→
  Env (PairValue (L.Value W grade)) X) :
 WB.oldPaid frame (sourceCofinalCfg sourceCode factory grade seed)+WB.nativeValue frame (sourceCofinalCfg sourceCode factory grade seed) write=
 (CF.codeAt sourceCode grade).eval
  (N.input (R.actualMaterial frame (sourceCofinalCfg sourceCode factory grade seed))).environment :=
 CF.actual_updated_total (CM.queryFactory factory) _ grade seed frame write

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
