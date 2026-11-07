import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Recorded
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.LegacyScope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}

/-- These are original occurrence distinctions, never failed comparisons
of displayed task values. The source row and complete old GS remain readable. -/
def IdentityResidual (origin : ReviewSource.Native.OriginAt input) : Type :=
  match origin with
  | .source code => ReviewSource.Native.Link.DistinctDeclaration code depth count
  | .outstanding source => ReviewSource.Native.Link.Legacy.CompletionDeclaration source depth count

inductive RecordedResult (task : ReviewSource.Material.OriginalTask input depth count)
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (scope : ReviewSource.Native.RecordedAt input depth count prefixLimit renewalLimit current) : Type
  | paid (terminal : ReviewSource.Native.OriginalScopePaid input depth count prefixLimit renewalLimit current (.recorded scope))
  | residual (identity : IdentityResidual (depth := depth) (count := count) scope.origin)

private def resolveOrigin (origin : ReviewSource.Native.OriginAt input) :
    (task : ReviewSource.Material.OriginalTask input depth count) →
    (current : Physical.Cursor Party Good Port Technology Instrument) →
    (scope : ReviewSource.Native.RecordedAt input depth count prefixLimit renewalLimit current) →
    scope.origin = origin →
    (∀ index : ReviewSource.Material.Slot input depth count task,
      (ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index).isSome = true) →
    RecordedResult task current scope := by
  cases origin with
  | source code =>
      intro task current scope same paid
      cases ReviewSource.Native.Link.recognize code depth count task with
      | same identity =>
          exact .paid (ReviewSource.Native.Link.the_already_recorded_source_scope_consumes_its_actual_material_payments
            code depth count prefixLimit renewalLimit identity current scope same paid)
      | distinct residual =>
          apply RecordedResult.residual
          rw [same]
          exact residual
  | outstanding source =>
      intro task current scope same paid
      cases ReviewSource.Native.Link.Legacy.recognize source depth count task with
      | planning identity =>
          exact .paid (ReviewSource.Native.Link.Legacy.PlanningIdentity.the_already_recorded_legacy_scope_consumes_its_actual_material_payments
            source depth count prefixLimit renewalLimit current identity scope same paid)
      | completion residual =>
          apply RecordedResult.residual
          rw [same]
          exact residual

/-- Only an already recorded installed scope is accepted. No Input inversion,
new admission or caller-supplied completed native state occurs here. -/
def resolveRecorded (task : ReviewSource.Material.OriginalTask input depth count)
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (scope : ReviewSource.Native.RecordedAt input depth count prefixLimit renewalLimit current)
    (paid : ∀ index : ReviewSource.Material.Slot input depth count task,
      (ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index).isSome = true) :
    RecordedResult task current scope :=
  resolveOrigin scope.origin task current scope rfl paid

theorem the_first_source_occurrence_has_no_native_identity_residual
    (code : SourceCode Party Good Port Technology Instrument)
    (task : ReviewSource.Material.OriginalTask code.input depth count)
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (scope : ReviewSource.Native.RecordedAt code.input depth count prefixLimit renewalLimit current)
    (sameCreator : scope.origin = .source code)
    (first : ReviewSource.Native.Link.declarationOrdinal code depth count = 1)
    (paid : ∀ index : ReviewSource.Material.Slot code.input depth count task,
      (ReviewSource.Material.payment? code.input depth count prefixLimit renewalLimit task current index).isSome = true) :
    ∃ terminal, resolveRecorded task current scope paid = .paid terminal := by
  cases actual : resolveRecorded task current scope paid with
  | paid terminal => exact ⟨terminal, rfl⟩
  | residual issue =>
      have original : ReviewSource.Native.Link.DistinctDeclaration code depth count :=
        Eq.mp (congrArg (IdentityResidual (depth := depth) (count := count)) sameCreator) issue
      exact False.elim (original.notBirth (original.originalOrdinal.trans first))

#print axioms resolveRecorded
#print axioms the_first_source_occurrence_has_no_native_identity_residual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native
