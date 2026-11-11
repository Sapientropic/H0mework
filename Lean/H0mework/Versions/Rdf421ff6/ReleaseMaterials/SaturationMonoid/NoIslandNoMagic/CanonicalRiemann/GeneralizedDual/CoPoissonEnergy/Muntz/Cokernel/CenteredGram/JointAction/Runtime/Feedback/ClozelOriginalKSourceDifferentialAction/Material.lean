import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Consumer
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Installation.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace I
export SourceOperationInquiry.Context.Installation (materialAt rawAt nextRawAt Occurrence)
end I
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
variable {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
variable (oldRaw nextRaw : O.Raw (Value:=Value) (Var:=Var) (sort:=()))

def sourceRawIncrement := nextRaw.environment-oldRaw.environment
def sourceRawDeltaWord : Formal ℤ Value Var () :=
 Finsupp.single nextRaw.expression 1-Finsupp.single oldRaw.expression 1
def sourceRawDeltaTerm := SourceOperationInquiry.Context.Faces.Execution.expression (sourceRawDeltaWord oldRaw nextRaw)
def sourceRawPairEnvironment := pairEnvironment oldRaw.environment (sourceRawIncrement oldRaw nextRaw)

def sourceRawSyntaxInjection : PairValue Value ()→+PairValue Value () :=
 (0 : PairValue Value ()→+Value ()).prod
 ((AddMonoidHom.fst _ _)+(AddMonoidHom.snd _ _))

/-- Source words are generated before any value equation, retaining their actual environmental change. -/
def sourceRawDifferentialCode : Expr (PairValue Value) Var () :=
 .add (liftExpr oldRaw.expression)
  (.linear (s:=()) (t:=()) sourceRawSyntaxInjection
   (liftExpr (sourceRawDeltaTerm oldRaw nextRaw)))

variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : I.Occurrence frame (current:=current))

/-- This raw pair is read from the same supplied source material, whose paid owner and traces are retained. -/
def sourceMaterialRaw := I.materialAt frame supplied

def sourceMaterialCode := sourceRawDifferentialCode (sourceMaterialRaw frame supplied).raw
 (sourceMaterialRaw frame supplied).nextRaw

def sourceMaterialEnvironment := sourceRawPairEnvironment (sourceMaterialRaw frame supplied).raw
 (sourceMaterialRaw frame supplied).nextRaw

/-- The authoritative source projection, not a scalar recognition, supplies both AST and environment feet. -/
theorem source_material_projection :
 sourceMaterialCode frame supplied=sourceRawDifferentialCode (I.rawAt frame supplied) (I.nextRawAt frame supplied) ∧
 sourceMaterialEnvironment frame supplied=pairEnvironment (I.rawAt frame supplied).environment
 ((I.nextRawAt frame supplied).environment-(I.rawAt frame supplied).environment) := ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
