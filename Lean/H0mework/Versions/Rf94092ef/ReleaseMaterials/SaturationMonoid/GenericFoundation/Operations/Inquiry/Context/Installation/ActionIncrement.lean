import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Installation.Source

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Installation

open SourceOperationEffects RootInquiryCompletion

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : C.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable {current : J.Current frame.registered} (occurrence : Occurrence frame (current := current))

/-- The actual mathematical action selects the original paid environment increment. -/
def executedEnvironmentIncrement : Env PhysicalValue PhysicalVar :=
  match RootGeneratedDebtActivationJointSource.mathAction current.2 with
  | .inl _ => (materialAt frame occurrence).paid.increment
  | .inr _ => 0

theorem next_raw_environment_from_executed_increment :
    (materialAt frame occurrence).nextRaw.environment =
      (materialAt frame occurrence).raw.environment+executedEnvironmentIncrement frame occurrence := by
  have original : (residualAt frame occurrence).environment = (rawAt frame occurrence).environment := by
    rcases occurrence with ⟨support,event⟩
    cases event
    rfl
  cases paid : RootGeneratedDebtActivationJointSource.mathAction current.2 with
  | inl action =>
    simp only [materialAt,nextRawAt,executedEnvironmentIncrement,paid]
    change (residualAt frame occurrence).environment+(residualAt frame occurrence).increment =
      (rawAt frame occurrence).environment+(residualAt frame occurrence).increment
    rw [original]
  | inr retained =>
    simp only [materialAt,nextRawAt,executedEnvironmentIncrement,paid,add_zero]

theorem executed_increment_eq_difference :
    executedEnvironmentIncrement frame occurrence =
      (materialAt frame occurrence).nextRaw.environment-(materialAt frame occurrence).raw.environment := by
  rw [next_raw_environment_from_executed_increment frame occurrence,add_sub_cancel_left]

end SourceOperationInquiry.Context.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
