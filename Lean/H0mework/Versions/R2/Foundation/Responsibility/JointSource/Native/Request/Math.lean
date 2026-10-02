import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Source

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request

open SourceOperationEffects RootInquiryCompletion

noncomputable section

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)]
  {sort : Sorts} {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (program : Program old.root.toAuthoritativeRoot.toLedgerRoot)
variable (registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
  old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current)
variable (scope : IdentityScope program)

def finiteVisit : Nat → RootVisit (targetRoot old program registered scope).toAuthoritativeRoot.toRoot
  | 0 => (targetRoot old program registered scope).toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (finiteVisit depth).next rfl

def temporalVisit (depth : Nat) :
    SourceNativeTemporalVisitAt (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot :=
  .finite (finiteVisit old program registered scope depth)

def mathCurrent (depth : Nat) := (finiteVisit old program registered scope (depth + 1)).current
def mathVisit (depth : Nat) := temporalVisit old program registered scope (depth + 1)
def mathEntry (depth : Nat) := mathSource registered (mathCurrent old program registered scope depth)

private def initialRow :
    ((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (temporalVisit old program registered scope 0)).GeneratedEntryRowAt
      (mathSource registered (finiteVisit old program registered scope 0).current) :=
  (((targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (temporalVisit old program registered scope 0)).canonicalGeneratedEntryRow?
      (mathSource registered (finiteVisit old program registered scope 0).current)).get (by rfl)

private def authorityAt (depth : Nat) : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot old program registered scope) (temporalVisit old program registered scope depth)
    (mathSource registered (finiteVisit old program registered scope depth).current) := by
  cases depth with
  | zero =>
      exact .generatedFromInitialRow (targetRoot old program registered scope) _
        (initialRow old program registered scope)
  | succ depth =>
      have next := (authorityAt depth).next (by rfl)
      have entryEq :
          (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (by rfl)
            (mathSource registered (finiteVisit old program registered scope depth).current) =
            mathSource registered (finiteVisit old program registered scope (depth + 1)).current :=
        patch_destination_math program registered (finiteVisit old program registered scope depth).current
      exact entryEq ▸ next

def mathAuthority (depth : Nat) : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (targetRoot old program registered scope) (mathVisit old program registered scope depth)
    (mathEntry old program registered scope depth) := authorityAt old program registered scope (depth + 1)

def mathAnswerFace (depth : Nat) : SourceNativeRootSemanticFaceAt
    (targetRoot old program registered scope) (mathVisit old program registered scope depth) where
  projection := (oldInstallation old program registered scope).embed (.inr PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def mathConsumer (depth : Nat) : SourceNativeInquiryAnswerConsumerAt PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old program registered scope).emitted
      (mathCurrent old program registered scope depth)))
    (mathEntry old program registered scope depth) (mathAnswerFace old program registered scope depth) where
  projection := (consumerInstallation old program registered scope).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def mathCompilation (depth : Nat) : SourceNativeInquiryCompilationProgramAt
    (targetRoot old program registered scope) (mathVisit old program registered scope depth)
    (U7 old registered) (calculus old registered) (TheoryState.rootSemantic (NewN old registered)) PUnit.unit
    (ULift.up.{u + 1, u} ((targetRoot old program registered scope).emitted
      (mathCurrent old program registered scope depth)))
    (mathEntry old program registered scope depth) (mathAuthority old program registered scope depth) where
  compile := fun _ => .answered (mathAnswerFace old program registered scope depth)
    (mathConsumer old program registered scope depth)

def mathState (depth : Nat) : RootInquiryStateAt (NewN old registered) (NewV old program registered) where
  root := targetRoot old program registered scope
  visit := mathVisit old program registered scope depth
  U7 := U7 old registered
  calculus := calculus old registered
  Query := PUnit
  entryAt := fun _ => mathEntry old program registered scope depth
  authorityAt := fun _ => mathAuthority old program registered scope depth
  compilationProgramAt := fun query => by cases query; exact mathCompilation old program registered scope depth
  compilationFaceAt := fun query => by
    cases query
    exact { projection := (compilationInstallation old program registered scope).embed PUnit.unit
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

def mathPresentation (depth : Nat) : RootInquiryStatePresentation where
  N := NewN old registered
  V := NewV old program registered
  state := .create (mathState old program registered scope depth)

theorem math_compiles (depth : Nat) :
    (mathState old program registered scope depth).compileInquiry PUnit.unit =
      .answered (mathAnswerFace old program registered scope depth) (mathConsumer old program registered scope depth) := rfl

/-- The next request reads this source's own canonical complete image. -/
def nextProgram : Program (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot where
  emit := fun current => (read? (targetRoot old program registered scope).toAuthoritativeRoot.toLedgerRoot current).get (by rfl)

include scope in
private theorem nextOpen_subsingleton (support : (NewN old registered).Support)
    (responsibility : (NewN old registered).Responsibility) :
    Subsingleton ((NewN old registered).OpenAt support responsibility) := by
  rcases support with ⟨oldSupport, state⟩
  cases responsibility with
  | inl original => exact scope.openAt_subsingleton oldSupport original
  | inr debt =>
      cases state with
      | none => exact ⟨fun impossible => nomatch impossible⟩
      | some state =>
          constructor
          rintro ⟨⟨left⟩⟩ ⟨⟨right⟩⟩
          rfl

/-- Identity authority for another request is paid by the current source's
actual certificate, not reinstalled as a target assumption. -/
def nextScope : IdentityScope (nextProgram old program registered scope) where
  defaultAnchor := scope.defaultAnchor
  openAt_subsingleton := nextOpen_subsingleton old program registered scope
  certify := fun current =>
    Eq.mp (congrArg (SourceNativeLedgerRestructuringCertificationAt
      (targetRoot old program registered scope).source.base.restructuringSource.compiler.restructuringLaw)
      ((nextProgram old program registered scope).emit current).generated_eq)
      ((targetRoot old program registered scope).source.base.restructuringSource.compiler.certifyRestructuring
        ((targetRoot old program registered scope).emitted current))

end
end RootGeneratedDebtActivationJointSource.Native.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
