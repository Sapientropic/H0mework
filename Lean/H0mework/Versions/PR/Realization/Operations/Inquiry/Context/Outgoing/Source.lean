import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Source
import H0mework.Realization.Operations.Execution.Relations.History.Events
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Closure

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Outgoing
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (query next resultAt actualOccurrence)
end Shared
end A
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable (configuration : A.Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort))
abbrev successor := A.Shared.next frame configuration
abbrev currentRaw := (A.Shared.query frame configuration).raw
abbrev nextRaw := (A.Shared.query (successor frame configuration) configuration).raw
abbrev increment := (nextRaw frame configuration).environment-(currentRaw frame configuration).environment

def currentWord : Formal ℤ (PairValue PhysicalValue) configuration.LowVar sort :=
 Finsupp.single (currentRaw frame configuration).expression 1
def nextWord : Formal ℤ (PairValue PhysicalValue) configuration.LowVar sort :=
 Finsupp.single (nextRaw frame configuration).expression 1
def deltaWord := nextWord frame configuration-currentWord frame configuration
def deltaTerm := Faces.Execution.expression (deltaWord frame configuration)
def correction := evaluation (R:=ℤ) (nextRaw frame configuration).environment (deltaWord frame configuration)
def scalarValue := (deltaTerm frame configuration).eval (nextRaw frame configuration).environment
def deltaScalarTrace := execution (nextRaw frame configuration).environment (deltaTerm frame configuration)
def pairEnvironment := SourceOperationScalarInventoryLift.pairEnvironment (currentRaw frame configuration).environment
 (increment frame configuration)
def pairTerm := liftExpr (deltaTerm frame configuration)
def pairValue := (pairTerm frame configuration).eval (pairEnvironment frame configuration)
def deltaPairTrace := execution (pairEnvironment frame configuration) (pairTerm frame configuration)
def nextSyntaxTrace := execution (nextRaw frame configuration).environment (nextRaw frame configuration).expression
abbrev mainResult := A.Shared.resultAt frame configuration (A.Shared.actualOccurrence frame)
abbrev mainTrace := (mainResult frame configuration).2.1.2

def mainExposure := SourceOperationPaidRelations.exposure (mainTrace frame configuration)
def nextSyntaxExposure := SourceOperationPaidRelations.exposure (nextSyntaxTrace frame configuration)
def scalarExposure := SourceOperationPaidRelations.exposure (deltaScalarTrace frame configuration)
def pairExposure := SourceOperationPaidRelations.exposure (deltaPairTrace frame configuration)
def scalarStock := SourceHistoryCommon.seed (scalarExposure frame configuration) (nextSyntaxExposure frame configuration)
abbrev pairStock := pairExposure frame configuration

def material := (currentRaw frame configuration,nextRaw frame configuration,deltaWord frame configuration,
 deltaTerm frame configuration,deltaScalarTrace frame configuration,deltaPairTrace frame configuration,
 nextSyntaxTrace frame configuration,mainResult frame configuration,
 scalarStock frame configuration,pairStock frame configuration)

end SourceOperationInquiry.Context.Outgoing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
