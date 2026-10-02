import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Math

/-! The next request reads this same general root's actual complete native
image. No identity-scope reconstruction or erased-root comparison is used. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
open SourceOperationEffects RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

def nextProgram : Program (targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot where
  emit := fun current => (read? (targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot current).get (by rfl)

theorem next_math_action (depth : Nat) :
    (mathAnswerFace old program registered depth).rootRead.action =
      mathAction (mathCurrent old program registered depth).2 := rfl

theorem next_math_step (depth : Nat) :
    (mathCurrent old program registered (depth + 1)).2.state =
      mathTarget (mathCurrent old program registered depth).2 :=
  (native program registered (mathCurrent old program registered depth)).next_state

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
