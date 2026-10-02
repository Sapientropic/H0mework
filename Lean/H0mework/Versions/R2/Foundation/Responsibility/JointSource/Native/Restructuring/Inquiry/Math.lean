import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Consumer

/-! The admitted born row follows this root's complete ledger into its math
inquiry. Both answer and compilation read their before-emitter source tokens. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
open SourceOperationEffects DebtActivationWorld RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)

def mathCurrent (depth : Nat) := (finiteVisit old program registered (depth + 1)).current
def mathVisit (depth : Nat) := temporalVisit old program registered (depth + 1)
def mathEntry (depth : Nat) := mathSource registered (mathCurrent old program registered depth)

private def authorityAt : (depth : Nat) → SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot old program registered) (temporalVisit old program registered depth)
    (mathSource registered (finiteVisit old program registered depth).current)
  | 0 => .generatedFromInitialRow (targetRoot old program registered) _
      (initialBornRow old program registered)
  | depth + 1 => by
      have next := (authorityAt depth).next (by rfl)
      have entryEq : (targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
            (mathSource registered (finiteVisit old program registered depth).current) =
          mathSource registered (finiteVisit old program registered (depth + 1)).current :=
        patch_destination_math program registered (finiteVisit old program registered depth).current
      exact entryEq ▸ next

def mathAuthority (depth : Nat) : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot old program registered) (mathVisit old program registered depth)
    (mathEntry old program registered depth) := authorityAt old program registered (depth + 1)

def mathAnswerFace (depth : Nat) : SourceNativeRootSemanticFaceAt
    (targetRoot old program registered) (mathVisit old program registered depth) where
  projection := (Assembly.oldInstallation old program registered).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def mathConsumer (depth : Nat) : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old program registered).emitted
      (mathCurrent old program registered depth)))
    (mathEntry old program registered depth) (mathAnswerFace old program registered depth) where
  projection := (Assembly.consumerInstallation old program registered).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def mathCompilation (depth : Nat) : SourceNativeInquiryCompilationProgramAt
    (targetRoot old program registered) (mathVisit old program registered depth)
    (Assembly.U7 old registered) (Assembly.calculus old registered)
    (TheoryState.rootSemantic (World registered)) PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old program registered).emitted
      (mathCurrent old program registered depth)))
    (mathEntry old program registered depth) (mathAuthority old program registered depth) where
  compile := fun _ => .answered (mathAnswerFace old program registered depth)
    (mathConsumer old program registered depth)

def mathState (depth : Nat) : RootInquiryStateAt (World registered) (JointV program registered) where
  root := targetRoot old program registered
  visit := mathVisit old program registered depth
  U7 := Assembly.U7 old registered
  calculus := Assembly.calculus old registered
  Query := PUnit
  entryAt := fun _ => mathEntry old program registered depth
  authorityAt := fun _ => mathAuthority old program registered depth
  compilationProgramAt := fun query => by cases query; exact mathCompilation old program registered depth
  compilationFaceAt := fun query => by
    cases query
    exact { projection := (Assembly.compilationInstallation old program registered).embed PUnit.unit
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

theorem math_compiles (depth : Nat) :
    (mathState old program registered depth).compileInquiry PUnit.unit =
      .answered (mathAnswerFace old program registered depth) (mathConsumer old program registered depth) := rfl

theorem math_root (depth : Nat) : (mathState old program registered depth).root =
    (initialRuntime old program registered).current.root := rfl

theorem math_visit (depth : Nat) : (mathState old program registered depth).visit =
    ((process old program registered).stateAt (ULift.up (depth + 1))).visit := rfl

theorem math_read (depth : Nat) : (mathAnswerFace old program registered depth).rootRead =
    mathReadout registered (mathCurrent old program registered depth) := rfl

variable (query : old.Query)
variable (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt old.root old.visit registered.input.owner)
variable (paid : GeneratedStepAt (Idle.law registered.input.environment registered.input.expression)
  (initialEvent registered).state)
variable (action : sourceAction old program registered = .inr paid)
variable (event : ExactTemporalCausalRootEventAt old.root.toAuthoritativeRoot.toLedgerRoot old.visit)

theorem generated_math_visit :
    ((birthProgram old query program registered authority paid action).generate event).target.targetVisit =
      (mathState old program registered 0).visit := rfl

theorem generated_math_next :
    ((birthProgram old query program registered authority paid action).generate event).target.targetAnswerAndNext.nextCurrent =
      ⟨JointV program registered, (mathState old program registered 0).root.toAuthoritativeRoot,
        (mathState old program registered 0).visit⟩ :=
  generated_first_next old program registered query authority paid action event

theorem generated_math_authority :
    mathAuthority old program registered 0 =
      (show (targetRoot old program registered).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
          (mathSource registered (initial old registered)) = mathEntry old program registered 0 from
        patch_destination_math program registered (initial old registered)) ▸
        (((birthProgram old query program registered authority paid action).generate event).target.bornAuthority.next (by rfl)) := by
  rfl

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
