import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage
open RootInquiryCompletion SourceOperationEffects
variable {S : Type u} {A X : S → Type u} [∀ s,AddCommGroup (A s)] {s : S}
variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=A) (Var:=X) (sort:=s))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=A) (PhysicalVar:=X) (sort:=s))
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (runtime actual_node presentation frames_erase_injective frames)
end Shared
abbrev Word := Nat →₀ ℤ
def embed : Word →ₗ[ℤ] SourceOperationInquiry.Carrier (Shared.runtime initial configuration) :=
 Finsupp.lmapDomain ℤ ℤ (Shared.runtime initial configuration).stateAt
abbrev shift : Word →ₗ[ℤ] Word := Finsupp.lmapDomain ℤ ℤ Nat.succ
abbrev source := SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.rawSource initial configuration
def observed : Word →ₗ[ℤ] Env A X := Finsupp.linearCombination ℤ fun stage =>
 SourceOperationInquiry.Context.readEnv (Shared.runtime initial configuration) (source initial configuration)
   ((Shared.runtime initial configuration).stateAt stage)
def effect : Word →ₗ[ℤ] Env A X := Finsupp.linearCombination ℤ fun stage =>
 SourceOperationInquiry.Context.increment (Shared.runtime initial configuration) (source initial configuration)
   ((Shared.runtime initial configuration).stateAt stage)
def observationFibre := SourceOperationLogic.fibreDecomposition (observed initial configuration)
def effectFibre := SourceOperationLogic.fibreDecomposition (effect initial configuration)
def retained (word : Word) := (observationFibre initial configuration word,
  effectFibre initial configuration word,embed initial configuration word,
  SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration word))
end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
