import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Payment

/-! The source compiler admits its own mathematical row. Its canonical whole
successors transport that sealed row through the complete actual history. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))

abbrev root := livingRoot old origin reader
abbrev visit (count : Nat) := temporalVisit old origin reader count
abbrev initialEntry := mathEntry old origin reader (initial old origin reader)

def initialRow : ((root old origin reader).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (visit old origin reader 0)).GeneratedEntryRowAt (initialEntry old origin reader) :=
  (((root old origin reader).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
    (visit old origin reader 0)).canonicalGeneratedEntryRow? (initialEntry old origin reader)).get (by
    have found : (sourceNativeFiniteLedgerPatchGeneratedEntry? _ _ _ _
      ((root old origin reader).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (visit old origin reader 0).current)
      ((root old origin reader).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
        (visit old origin reader 0)).currentPatch (initialEntry old origin reader)).isSome = true :=
      image_math_row_found old origin reader (initial old origin reader)
    unfold SourceNativeTemporalVisitGeneratedEvolutionAt.canonicalGeneratedEntryRow?
    split
    · rename_i missing
      rw [missing] at found
      contradiction
    · rfl)

abbrev AdmissionAt (count : Nat) := Σ entry : OpenResponsibilityAt (World old origin reader)
    ((root old origin reader).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      ((root old origin reader).emitted (visit old origin reader count).current)),
  SourceNativeLivingTemporalCausalEntryAuthorityAt (root old origin reader) (visit old origin reader count) entry

def admission : (count : Nat) → AdmissionAt old origin reader count
  | 0 => ⟨initialEntry old origin reader,
      .generatedFromInitialRow (root old origin reader) _ (initialRow old origin reader)⟩
  | count+1 =>
      let prior := admission count
      let next := next_eq old origin reader (visit old origin reader count).current
      ⟨(root old origin reader).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext next prior.1,
        prior.2.next next⟩

abbrev entry (count : Nat) := (admission old origin reader count).1
abbrev authority (count : Nat) := (admission old origin reader count).2
abbrev runtime (count : Nat) := Completion.runtime old origin reader count

theorem actual_current (count : Nat) : (runtime old origin reader count).current.visit = visit old origin reader count := by
  change temporalVisit old origin reader (runtime old origin reader count).state.down = _
  exact congrArg (temporalVisit old origin reader) (Completion.runtime_depth old origin reader count)

abbrev endpoint := Calculation.targetRuntime old origin reader
abbrev endpointEntry := entry old origin reader (endpoint old origin reader).state.down
abbrev endpointAuthority := authority old origin reader (endpoint old origin reader).state.down

theorem whole_next (count : Nat) : type_of% (tick_ledger old origin reader (runtime old origin reader count)) ∧
    type_of% (tick_math old origin reader (runtime old origin reader count)) :=
  ⟨tick_ledger old origin reader _, tick_math old origin reader _⟩

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
