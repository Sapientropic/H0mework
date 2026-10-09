import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.Installation
/-! Independent temporal consumers reconstruct the whole original visit,
canonical material and next from the installed low source payload. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Calculation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (parent : SourceNativeLivingRootClosure N V)
variable (origin : SourceNativeTemporalVisitAt parent.toAuthoritativeRoot.toLedgerRoot)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : parent.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin.current →
  O.Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (count : Nat)

abbrev recovered := decode parent.toAuthoritativeRoot.toLedgerRoot (face parent origin U7 calculus reader count).rootRead

theorem current_preserved : (recovered parent origin U7 calculus reader count).current = origin.current := rfl

theorem complete_past_preserved : parent.toAuthoritativeRoot.toLedgerRoot.generatedTemporalPriorPatchesAt
    (recovered parent origin U7 calculus reader count).history =
    parent.toAuthoritativeRoot.toLedgerRoot.generatedTemporalPriorPatchesAt origin.history :=
  congrArg (fun history : SourceNativeTemporalReachableAt parent.toAuthoritativeRoot.toLedgerRoot origin.current =>
    parent.toAuthoritativeRoot.toLedgerRoot.generatedTemporalPriorPatchesAt history)
    (HistoryAt.decode_encode parent.toAuthoritativeRoot.toLedgerRoot origin.history)

theorem canonical_material_preserved : HEq
    (parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (recovered parent origin U7 calculus reader count))
    (parent.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit origin) := by
  unfold recovered
  rw [readback parent origin U7 calculus reader count]

theorem parent_next_preserved : parent.generatedNextCurrentAt (recovered parent origin U7 calculus reader count) =
    parent.generatedNextCurrentAt origin :=
  congrArg parent.generatedNextCurrentAt (readback parent origin U7 calculus reader count)

theorem distinct_material (other : SourceNativeTemporalVisitAt parent.toAuthoritativeRoot.toLedgerRoot)
    (distinct : origin ≠ other) :
    (face parent origin U7 calculus reader count).rootRead ≠ encode parent.toAuthoritativeRoot.toLedgerRoot other := by
  intro same
  exact distinct (encode_injective parent.toAuthoritativeRoot.toLedgerRoot same)

end SourceTemporalMaterial.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
