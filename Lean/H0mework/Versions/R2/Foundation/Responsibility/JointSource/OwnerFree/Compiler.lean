import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Source
import H0mework.Foundation.Ledger.ProofRelevantRestructuring

/-! One canonical mathematical row and the original complete old inventory are
compiled from the actual whole step. The remainder is source-generated and
requires neither a finite old ledger nor an old owner. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree
open SourceOperationEffects DebtActivationWorld DebtActivationLedger
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : SourceNativeAuthoritativeRootClosure N V) (origin : V.Current)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin →
  Raw (Value := Value) (Var := Var) (sort := sort))

inductive RowAt : {state : Current old origin reader} →
    (occurrence : (source old origin reader).toRootSource.actual.OccurrenceAt state) →
    {targetSupport : (World old origin reader).Support} →
    OpenResponsibilityAt (World old origin reader) ((source old origin reader).toRootSource.account.supportOf occurrence) →
    OpenResponsibilityAt (World old origin reader) targetSupport → Type u
  | destination (state : Current old origin reader)
      (entry : OpenResponsibilityAt (World old origin reader) (supportAt old origin reader state)) :
      RowAt (emitted old origin reader state) entry ((whole old origin reader state).destination entry).1
  | origin (state : Current old origin reader)
      (entry : OpenResponsibilityAt (World old origin reader) (supportAt old origin reader (nextState old origin reader state))) :
      RowAt (emitted old origin reader state) ((whole old origin reader state).origin entry).1 entry

inductive RemainderAt : {state : Current old origin reader} →
    (occurrence : (source old origin reader).toRootSource.actual.OccurrenceAt state) → (World old origin reader).Support → Type u
  | generated (state : Current old origin reader) : RemainderAt (emitted old origin reader state)
      (supportAt old origin reader (nextState old origin reader state))

def remainderSource : LedgerTransportedRemainderSourceAt (source old origin reader) (RowAt old origin reader) where
  OccurrenceAt := RemainderAt old origin reader
  emit? := by
    classical
    intro state occurrence targetSupport
    rcases occurrence with ⟨support, event⟩
    cases event
    exact if same : supportAt old origin reader (nextState old origin reader state) = targetSupport
      then some (same ▸ RemainderAt.generated state) else none
  compileEvolution := by
    intro state occurrence targetSupport event
    cases event
    exact whole old origin reader state
  compileExact := by
    intro state occurrence targetSupport event
    cases event
    exact { destination := fun entry => .destination state entry, origin := fun entry => .origin state entry }

def rowSource : LedgerWriteRowSourceAt (source old origin reader) (RowAt old origin reader) where
  IncidenceOccurrenceAt := RowAt old origin reader
  compileEvolution := by
    intro state occurrence targetSupport sourceEntry targetEntry event
    cases event with
    | destination entry => exact ((whole old origin reader state).destination entry).2
    | origin entry => exact ((whole old origin reader state).origin entry).2
  compileExact := fun event => event
  transportedRemainderSource := remainderSource old origin reader

def rows (state : Current old origin reader) : FiniteGeneratedLedgerWriteRowsAt
    (rowSource old origin reader) (emitted old origin reader state)
    ⟨supportAt old origin reader (nextState old origin reader state)⟩ where
  size := 1
  sourceEntryAt := fun _ => mathEntry old origin reader state
  targetEntryAt := fun _ => ((whole old origin reader state).destination (mathEntry old origin reader state)).1
  rowAt := fun _ => (rowSource old origin reader).generate (.destination state (mathEntry old origin reader state))

def coverage (state : Current old origin reader) : LedgerTransportedRemainderCoverageAt (rows old origin reader state) where
  destinationIndex := by
    rintro ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => exact none
    | inr debt =>
        rcases opened with ⟨⟨same⟩⟩
        cases same
        exact some ⟨⟨0, by change 0 < 1; decide⟩, rfl⟩
  originIndex := fun _ => none

def remainder (state : Current old origin reader) : GeneratedLedgerTransportedRemainderAt
    (rowSource old origin reader) (emitted old origin reader state)
    ⟨supportAt old origin reader (nextState old origin reader state)⟩ :=
  (rowSource old origin reader).generateTransportedRemainder
    (emitted old origin reader state) ⟨supportAt old origin reader (nextState old origin reader state)⟩
    (.generated state) (by simp [rowSource, remainderSource, emitted])

def patch (state : Current old origin reader) : FiniteGeneratedLedgerWritePatchAt
    (rowSource old origin reader) (emitted old origin reader state)
    ⟨supportAt old origin reader (nextState old origin reader state)⟩ :=
  .transportedRemainder (rows old origin reader state) (coverage old origin reader state) (remainder old origin reader state)

theorem patch_fold (state : Current old origin reader) :
    (patch old origin reader state).toLedgerWriteEvolution = whole old origin reader state := by
  have destinations : (patch old origin reader state).toLedgerWriteEvolution.destination =
      (whole old origin reader state).destination := by
    funext entry
    rcases entry with ⟨responsibility, opened⟩
    cases responsibility with
    | inl _ => rfl
    | inr debt => rcases opened with ⟨⟨same⟩⟩; cases same; rfl
  have origins : (patch old origin reader state).toLedgerWriteEvolution.origin = (whole old origin reader state).origin := rfl
  cases first : (patch old origin reader state).toLedgerWriteEvolution
  cases second : whole old origin reader state
  simp only [first, second] at destinations origins
  cases destinations
  cases origins
  rfl

def restructuringLaw := RootGeneratedProofRelevantRestructuring.law (World old origin reader)
  (supportAt old origin reader (initial old origin reader)) (source old origin reader)

def wholeCertificate (state : Current old origin reader) : ExactLedgerRestructuringCertificationAt
    (restructuringLaw old origin reader) (emitted old origin reader state) (whole old origin reader state) :=
  .ofInjective
    (by
      intro left right same
      rw [← whole_destination_origin old origin reader state left, ← whole_destination_origin old origin reader state right]
      exact congrArg (fun entry => ((whole old origin reader state).destination entry).1) same)
    (by
      intro left right same
      rw [← whole_origin_destination old origin reader state left, ← whole_origin_destination old origin reader state right]
      exact congrArg (fun entry => ((whole old origin reader state).origin entry).1) same)

def patchCertificate (state : Current old origin reader) : ExactLedgerRestructuringCertificationAt
    (restructuringLaw old origin reader) (emitted old origin reader state) (patch old origin reader state).toLedgerWriteEvolution :=
  (patch_fold old origin reader state).symm ▸ wholeCertificate old origin reader state

/-- The compiler and its patch are emitted together from the same action. -/
private def imageFromAction (state : Current old origin reader)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕ GeneratedStepAt (law old origin reader) state)
    (actual_eq : action old origin reader state = selected) : Σ generated : SourceNativeLedgerEvolutionAt
    (source old origin reader) (emitted old origin reader state),
    SourceNativeFiniteLedgerPatchAt (source old origin reader) (RowAt old origin reader)
      (rowSource old origin reader) (LedgerTerminalRowSourceAt.empty (source old origin reader)) generated ×
      PLift (generated.CommutesWith (emitted old origin reader)) ×
      SourceNativeLedgerRestructuringCertificationAt (restructuringLaw old origin reader) generated := by
  cases selected with
  | inl settled =>
      let actual : Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
          (emitted old origin reader state) ⟨supportAt old origin reader state⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution :=
        Eq.mp (congrArg (fun targetState =>
          Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
            (emitted old origin reader state) ⟨supportAt old origin reader targetState⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution)
          (show nextState old origin reader state = state from by
            unfold nextState targetOf
            rw [actual_eq]))
          (⟨patch old origin reader state, patchCertificate old origin reader state⟩ :
            Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
              (emitted old origin reader state) ⟨supportAt old origin reader (nextState old origin reader state)⟩,
            ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
              (emitted old origin reader state) actualPatch.toLedgerWriteEvolution)
      let actualPatch := actual.1
      refine ⟨.continuedTransport settled ?_ (emitted old origin reader state) actualPatch.toLedgerWriteEvolution, ⟨actualPatch, rfl⟩, ⟨rfl⟩, actual.2⟩
      change (match action old origin reader state with
        | .inl settled => EvolutionAt.continuedTransport (V := vocabulary old origin reader) settled
        | .inr paid => EvolutionAt.nativeWrite (V := vocabulary old origin reader) paid) = _
      rw [actual_eq]
  | inr paid =>
      let actual : Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
          (emitted old origin reader state) ⟨supportAt old origin reader paid.1⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution :=
        Eq.mp (congrArg (fun targetState =>
          Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
            (emitted old origin reader state) ⟨supportAt old origin reader targetState⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution)
          (show nextState old origin reader state = paid.1 from by
            unfold nextState targetOf
            rw [actual_eq]))
          (⟨patch old origin reader state, patchCertificate old origin reader state⟩ :
            Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
              (emitted old origin reader state) ⟨supportAt old origin reader (nextState old origin reader state)⟩,
            ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
              (emitted old origin reader state) actualPatch.toLedgerWriteEvolution)
      let actualPatch := actual.1
      refine ⟨.nativeWrite paid ?_ (emitted old origin reader paid.1) actualPatch.toLedgerWriteEvolution, ⟨actualPatch, rfl⟩, ⟨rfl⟩, actual.2⟩
      change (match action old origin reader state with
        | .inl settled => EvolutionAt.continuedTransport (V := vocabulary old origin reader) settled
        | .inr paid => EvolutionAt.nativeWrite (V := vocabulary old origin reader) paid) = _
      rw [actual_eq]

def image (state : Current old origin reader) : Σ generated : SourceNativeLedgerEvolutionAt
    (source old origin reader) (emitted old origin reader state),
    SourceNativeFiniteLedgerPatchAt (source old origin reader) (RowAt old origin reader)
      (rowSource old origin reader) (LedgerTerminalRowSourceAt.empty (source old origin reader)) generated ×
      PLift (generated.CommutesWith (emitted old origin reader)) ×
      SourceNativeLedgerRestructuringCertificationAt (restructuringLaw old origin reader) generated :=
  imageFromAction old origin reader state (action old origin reader state) rfl

private theorem transportedMathRow (state target : Current old origin reader)
    (same : nextState old origin reader state = target) :
    ((Eq.mp (congrArg (fun targetState =>
        Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
          (emitted old origin reader state) ⟨supportAt old origin reader targetState⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution) same)
      (⟨patch old origin reader state, patchCertificate old origin reader state⟩ :
        Σ actualPatch : FiniteGeneratedLedgerWritePatchAt (rowSource old origin reader)
          (emitted old origin reader state) ⟨supportAt old origin reader (nextState old origin reader state)⟩,
          ExactLedgerRestructuringCertificationAt (restructuringLaw old origin reader)
            (emitted old origin reader state) actualPatch.toLedgerWriteEvolution)).1.canonicalGeneratedSourceRow?
        (mathEntry old origin reader state)).isSome = true := by
  cases same
  rfl

private theorem imageFromAction_math_row_found (state : Current old origin reader)
    (selected : SourceOperationExecutionDebt.Settlement state ⊕
      DebtActivationWorld.GeneratedStepAt (law old origin reader) state)
    (selected_eq : action old origin reader state = selected) :
    (sourceNativeFiniteLedgerPatchGeneratedEntry? _ _ _ _
      (imageFromAction old origin reader state selected selected_eq).1
      (imageFromAction old origin reader state selected selected_eq).2.1
      (mathEntry old origin reader state)).isSome = true := by
  cases selected with
  | inl settled =>
    dsimp only [imageFromAction]
    exact transportedMathRow old origin reader state state (by
      unfold nextState targetOf
      rw [selected_eq])
  | inr paid =>
    dsimp only [imageFromAction]
    exact transportedMathRow old origin reader state paid.1 (by
      unfold nextState targetOf
      rw [selected_eq])

theorem image_math_row_found (state : Current old origin reader) :
    (sourceNativeFiniteLedgerPatchGeneratedEntry? _ _ _ _
      (image old origin reader state).1 (image old origin reader state).2.1
      (mathEntry old origin reader state)).isSome = true := by
  exact imageFromAction_math_row_found old origin reader state (action old origin reader state) rfl

def compiler : SourceNativeLedgerCompiler (source old origin reader) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := RowAt old origin reader
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun row => ((rowSource old origin reader).compileEvolution row).toDebtLineage.lineage_eq
  writeRowSource := rowSource old origin reader
  terminalRowSource := LedgerTerminalRowSourceAt.empty (source old origin reader)
  compile := by
    intro state occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact (image old origin reader state).1
  compilePatch := by
    intro state occurrence
    rcases occurrence with ⟨support, event⟩
    cases event
    exact (image old origin reader state).2.1

def ledgerRoot : SourceNativeLedgerRootClosure (World old origin reader) (vocabulary old origin reader) where
  source := { source := source old origin reader, ledgerCompiler := compiler old origin reader }
  emitted := emitted old origin reader
  compiler_commutes := fun state => (image old origin reader state).2.2.1.down

end RootGeneratedDebtActivationJointSource.OwnerFree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
