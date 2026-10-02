import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerOperands

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open MotherInquiryAnswerOperands
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
universe u

def uniqueMember {A : Type u} [Subsingleton A] : Option A :=
  if exists_ : Nonempty A then some exists_.some else none

theorem uniqueMember_recovers {A : Type u} [Subsingleton A] (value : A) :
    uniqueMember = some value := by
  unfold uniqueMember
  rw [dif_pos ⟨value⟩]
  exact congrArg some (Subsingleton.elim _ _)

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (obstruction : N.ObstructionAt (Support root visit))

instance failureSubsingleton : Subsingleton (ActualExpressibilityFailure (Theory root) obstruction) where
  allEq first last := by
    cases first with
    | mk notExpressible noRealization =>
      cases last with
      | mk otherNot otherRealization =>
        have firstEq : notExpressible = otherNot := Subsingleton.elim _ _
        have secondEq : noRealization = otherRealization := Subsingleton.elim _ _
        cases firstEq
        cases secondEq
        rfl

/-- The complete original failure contains the two empty source fibres.
Both are determined by the already formed full law surface. -/
def formFailure : Option (ActualExpressibilityFailure (Theory root) obstruction) := uniqueMember

theorem formFailure_recovers (failure : ActualExpressibilityFailure (Theory root) obstruction) :
    formFailure root visit obstruction = some failure := uniqueMember_recovers failure

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
