import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Frame

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherNetworkOrigin FiniteGeneratedLedgerWritePatchAt
noncomputable section

private theorem whole_ext {N : WorldRelationNetwork.{0}} {source target : CompleteLiveLedgerAt N}
    {left right : LedgerWriteEvolutionAt N source target}
    (destination : ∀ a, left.destination a = right.destination a)
    (origin : ∀ b, left.origin b = right.origin b) : left = right := by
  have hd := funext destination
  have ho := funext origin
  cases left
  cases right
  cases hd
  cases ho
  rfl

namespace NormalWriteFrame
variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G}
    {old : Transitions original} {formed : Transitions generated}
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    {point : Point original} {current : W.Current}
    {event : generated.law.EventAt current (n.support point.2.1)}
    (frame : NormalWriteFrame n rows output point current event)

theorem writePatch_fold {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt rows point.2 target) :
    (frame.writePatch patch).toLedgerWriteEvolution = n.wholeLedgerEquiv point.2.1 target.support patch.toLedgerWriteEvolution := by
  cases patch with
  | identityRemainder rows coverage =>
      apply whole_ext
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger point.2.1).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (point.2.1), LedgerEntryEvolutionAt N entry out) →
            (Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G (n.ledger point.2.1 entry) out) :=
          fun value => ⟨n.ledger (point.2.1) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_destination (identityRemainderEvolution rows coverage) entry).symm
        change (identityRemainderEvolution (frame.finiteRows rows) (frame.identityCoverage coverage)).destination (n.ledger point.2.1 entry) = mapResult ((identityRemainderEvolution rows coverage).destination entry)
        cases selected : coverage.destinationIndex entry with
        | none =>
            have newSelected : (frame.identityCoverage coverage).destinationIndex (n.ledger (point.2.1) entry) = none :=
              (mapSelection_at (n.ledger (point.2.1)) rows.sourceEntryAt coverage.destinationIndex entry).trans
                (by rw [selected]; rfl)
            have left := identity_destination_none (frame.finiteRows rows) (frame.identityCoverage coverage)
              (n.ledger (point.2.1) entry) newSelected
            have right := congrArg mapResult (identity_destination_none rows coverage entry selected)
            exact left.trans right.symm
        | some chosen =>
            rcases chosen with ⟨index, entryEq⟩
            cases entryEq
            have newSelected : (frame.identityCoverage coverage).destinationIndex (n.ledger (point.2.1) (rows.sourceEntryAt index)) =
                some ⟨index, rfl⟩ := (mapSelection_at (n.ledger (point.2.1)) rows.sourceEntryAt
                  coverage.destinationIndex (rows.sourceEntryAt index)).trans (by rw [selected]; rfl)
            have left := identity_destination_some (frame.finiteRows rows) (frame.identityCoverage coverage)
              (n.ledger (point.2.1) (rows.sourceEntryAt index)) ⟨index, rfl⟩ newSelected
            have right := congrArg mapResult (identity_destination_some rows coverage (rows.sourceEntryAt index) ⟨index, rfl⟩ selected)
            have middle := congrArg (fun row => (⟨n.ledger (point.2.1) (rows.targetEntryAt index), row⟩ :
                Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G (n.ledger (point.2.1) (rows.sourceEntryAt index)) out))
              (frame.row_evolution _ _ (rows.rowAt index))
            exact left.trans (middle.trans right.symm)
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger point.2.1).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (point.2.1), LedgerEntryEvolutionAt N out entry) →
            (Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger point.2.1 entry)) :=
          fun value => ⟨n.ledger (point.2.1) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_origin (identityRemainderEvolution rows coverage) entry).symm
        change (identityRemainderEvolution (frame.finiteRows rows) (frame.identityCoverage coverage)).origin (n.ledger point.2.1 entry) = mapResult ((identityRemainderEvolution rows coverage).origin entry)
        cases selected : coverage.originIndex entry with
        | none =>
            have newSelected : (frame.identityCoverage coverage).originIndex (n.ledger (point.2.1) entry) = none :=
              (mapSelection_at (n.ledger (point.2.1)) rows.targetEntryAt coverage.originIndex entry).trans
                (by rw [selected]; rfl)
            have left := identity_origin_none (frame.finiteRows rows) (frame.identityCoverage coverage)
              (n.ledger (point.2.1) entry) newSelected
            have right := congrArg mapResult (identity_origin_none rows coverage entry selected)
            exact left.trans right.symm
        | some chosen =>
            rcases chosen with ⟨index, entryEq⟩
            cases entryEq
            have newSelected : (frame.identityCoverage coverage).originIndex (n.ledger (point.2.1) (rows.targetEntryAt index)) =
                some ⟨index, rfl⟩ := (mapSelection_at (n.ledger (point.2.1)) rows.targetEntryAt
                  coverage.originIndex (rows.targetEntryAt index)).trans (by rw [selected]; rfl)
            have left := identity_origin_some (frame.finiteRows rows) (frame.identityCoverage coverage)
              (n.ledger (point.2.1) (rows.targetEntryAt index)) ⟨index, rfl⟩ newSelected
            have right := congrArg mapResult (identity_origin_some rows coverage (rows.targetEntryAt index) ⟨index, rfl⟩ selected)
            have middle := congrArg (fun row => (⟨n.ledger (point.2.1) (rows.sourceEntryAt index), row⟩ :
                Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger (point.2.1) (rows.targetEntryAt index))))
              (frame.row_evolution _ _ (rows.rowAt index))
            exact left.trans (middle.trans right.symm)
  | complete rows coverage =>
      apply whole_ext
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger point.2.1).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (target.support), LedgerEntryEvolutionAt N entry out) →
            (Σ out : OpenResponsibilityAt G (n.support (target.support)), LedgerEntryEvolutionAt G (n.ledger point.2.1 entry) out) :=
          fun value => ⟨n.ledger (target.support) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_destination (completeEvolution rows coverage) entry).symm
        change (completeEvolution (frame.finiteRows rows) (frame.completeCoverage coverage)).destination (n.ledger point.2.1 entry) = mapResult ((completeEvolution rows coverage).destination entry)
        have entryEq := coverage.destination_sound entry
        generalize indexEq : coverage.destinationIndex entry = index at entryEq
        cases entryEq
        have newIndex : (frame.completeCoverage coverage).destinationIndex (n.ledger (point.2.1) (rows.sourceEntryAt index)) = index :=
          (congrArg coverage.destinationIndex ((n.ledger (point.2.1)).symm_apply_apply (rows.sourceEntryAt index))).trans indexEq
        have left := complete_destination_at (frame.finiteRows rows) (frame.completeCoverage coverage)
          (n.ledger (point.2.1) (rows.sourceEntryAt index)) index newIndex rfl
        have right := congrArg mapResult (complete_destination_at rows coverage (rows.sourceEntryAt index) index indexEq rfl)
        have middle := congrArg (fun row => (⟨n.ledger (target.support) (rows.targetEntryAt index), row⟩ :
            Σ out : OpenResponsibilityAt G (n.support (target.support)), LedgerEntryEvolutionAt G (n.ledger (point.2.1) (rows.sourceEntryAt index)) out))
          (frame.row_evolution _ _ (rows.rowAt index))
        exact left.trans (middle.trans right.symm)
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger target.support).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (point.2.1), LedgerEntryEvolutionAt N out entry) →
            (Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger target.support entry)) :=
          fun value => ⟨n.ledger (point.2.1) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_origin (completeEvolution rows coverage) entry).symm
        change (completeEvolution (frame.finiteRows rows) (frame.completeCoverage coverage)).origin (n.ledger target.support entry) = mapResult ((completeEvolution rows coverage).origin entry)
        have entryEq := coverage.origin_sound entry
        generalize indexEq : coverage.originIndex entry = index at entryEq
        cases entryEq
        have newIndex : (frame.completeCoverage coverage).originIndex (n.ledger (target.support) (rows.targetEntryAt index)) = index :=
          (congrArg coverage.originIndex ((n.ledger (target.support)).symm_apply_apply (rows.targetEntryAt index))).trans indexEq
        have left := complete_origin_at (frame.finiteRows rows) (frame.completeCoverage coverage)
          (n.ledger (target.support) (rows.targetEntryAt index)) index newIndex rfl
        have right := congrArg mapResult (complete_origin_at rows coverage (rows.targetEntryAt index) index indexEq rfl)
        have middle := congrArg (fun row => (⟨n.ledger (point.2.1) (rows.sourceEntryAt index), row⟩ :
            Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger (target.support) (rows.targetEntryAt index))))
          (frame.row_evolution _ _ (rows.rowAt index))
        exact left.trans (middle.trans right.symm)
  | transportedRemainder rows coverage remainder =>
      apply whole_ext
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger point.2.1).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (target.support), LedgerEntryEvolutionAt N entry out) →
            (Σ out : OpenResponsibilityAt G (n.support (target.support)), LedgerEntryEvolutionAt G (n.ledger point.2.1 entry) out) :=
          fun value => ⟨n.ledger (target.support) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_destination (transportedRemainderEvolution rows coverage remainder) entry).symm
        change (transportedRemainderEvolution (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)).destination (n.ledger point.2.1 entry) = mapResult ((transportedRemainderEvolution rows coverage remainder).destination entry)
        cases selected : coverage.destinationIndex entry with
        | none =>
            have newSelected : (frame.remainderCoverage coverage).destinationIndex (n.ledger (point.2.1) entry) = none :=
              (mapSelection_at (n.ledger (point.2.1)) rows.sourceEntryAt coverage.destinationIndex entry).trans
                (by rw [selected]; rfl)
            have left := remainder_destination_none (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)
              (n.ledger (point.2.1) entry) newSelected
            have right := congrArg mapResult (remainder_destination_none rows coverage remainder entry selected)
            have middle := (congrArg (fun whole => whole.destination (n.ledger (point.2.1) entry))
              (frame.remainder_evolution remainder)).trans (n.whole_destination remainder.evolution entry)
            exact left.trans (middle.trans right.symm)
        | some chosen =>
            rcases chosen with ⟨index, entryEq⟩
            cases entryEq
            have newSelected : (frame.remainderCoverage coverage).destinationIndex (n.ledger (point.2.1) (rows.sourceEntryAt index)) =
                some ⟨index, rfl⟩ := (mapSelection_at (n.ledger (point.2.1)) rows.sourceEntryAt
                  coverage.destinationIndex (rows.sourceEntryAt index)).trans (by rw [selected]; rfl)
            have left := remainder_destination_some (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)
              (n.ledger (point.2.1) (rows.sourceEntryAt index)) ⟨index, rfl⟩ newSelected
            have right := congrArg mapResult (remainder_destination_some rows coverage remainder (rows.sourceEntryAt index) ⟨index, rfl⟩ selected)
            have middle := congrArg (fun row => (⟨n.ledger (target.support) (rows.targetEntryAt index), row⟩ :
                Σ out : OpenResponsibilityAt G (n.support (target.support)), LedgerEntryEvolutionAt G (n.ledger (point.2.1) (rows.sourceEntryAt index)) out))
              (frame.row_evolution _ _ (rows.rowAt index))
            exact left.trans (middle.trans right.symm)
      · intro entry
        obtain ⟨entry, rfl⟩ := (n.ledger target.support).surjective entry
        let mapResult : (Σ out : OpenResponsibilityAt N (point.2.1), LedgerEntryEvolutionAt N out entry) →
            (Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger target.support entry)) :=
          fun value => ⟨n.ledger (point.2.1) value.1, n.mapRow value.2⟩
        refine Eq.trans ?_ (n.whole_origin (transportedRemainderEvolution rows coverage remainder) entry).symm
        change (transportedRemainderEvolution (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)).origin (n.ledger target.support entry) = mapResult ((transportedRemainderEvolution rows coverage remainder).origin entry)
        cases selected : coverage.originIndex entry with
        | none =>
            have newSelected : (frame.remainderCoverage coverage).originIndex (n.ledger (target.support) entry) = none :=
              (mapSelection_at (n.ledger (target.support)) rows.targetEntryAt coverage.originIndex entry).trans
                (by rw [selected]; rfl)
            have left := remainder_origin_none (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)
              (n.ledger (target.support) entry) newSelected
            have right := congrArg mapResult (remainder_origin_none rows coverage remainder entry selected)
            have middle := (congrArg (fun whole => whole.origin (n.ledger (target.support) entry))
              (frame.remainder_evolution remainder)).trans (n.whole_origin remainder.evolution entry)
            exact left.trans (middle.trans right.symm)
        | some chosen =>
            rcases chosen with ⟨index, entryEq⟩
            cases entryEq
            have newSelected : (frame.remainderCoverage coverage).originIndex (n.ledger (target.support) (rows.targetEntryAt index)) =
                some ⟨index, rfl⟩ := (mapSelection_at (n.ledger (target.support)) rows.targetEntryAt
                  coverage.originIndex (rows.targetEntryAt index)).trans (by rw [selected]; rfl)
            have left := remainder_origin_some (frame.finiteRows rows) (frame.remainderCoverage coverage) (frame.remainder remainder)
              (n.ledger (target.support) (rows.targetEntryAt index)) ⟨index, rfl⟩ newSelected
            have right := congrArg mapResult (remainder_origin_some rows coverage remainder (rows.targetEntryAt index) ⟨index, rfl⟩ selected)
            have middle := congrArg (fun row => (⟨n.ledger (point.2.1) (rows.sourceEntryAt index), row⟩ :
                Σ out : OpenResponsibilityAt G (n.support (point.2.1)), LedgerEntryEvolutionAt G out (n.ledger (target.support) (rows.targetEntryAt index))))
              (frame.row_evolution _ _ (rows.rowAt index))
            exact left.trans (middle.trans right.symm)


end NormalWriteFrame
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
