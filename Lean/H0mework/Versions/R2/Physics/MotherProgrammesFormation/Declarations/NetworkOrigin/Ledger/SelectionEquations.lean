import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.FiniteRows
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.TerminalRows

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open FiniteGeneratedLedgerWritePatchAt
noncomputable section

private theorem sigma_cast {A B : Type} (R : A → B → Type) {a a' : A}
    (same : a = a') (b : B) (value : R a b) :
    Eq.mp (congrArg (fun a => Σ b, R a b) same) ⟨b, value⟩ =
      (⟨b, Eq.mp (congrArg (fun a => R a b) same) value⟩ : Σ b, R a' b) := by
  cases same
  rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
  {source : SourceNativeSource N V}
  {Exact : {c : V.Current} → (event : source.toRootSource.actual.OccurrenceAt c) →
    {t : N.Support} → OpenResponsibilityAt N (source.toRootSource.account.supportOf event) →
      OpenResponsibilityAt N t → Type}
  {rowSource : LedgerWriteRowSourceAt source Exact}
  {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}

theorem identity_destination_none
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event ⟨source.toRootSource.account.supportOf event⟩)
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (selected : coverage.destinationIndex entry = none) :
    (identityRemainderEvolution rows coverage).destination entry = ⟨entry, .carried rfl HEq.rfl⟩ := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N entry out) from match coverage.destinationIndex entry with
    | none => ⟨entry, .carried rfl HEq.rfl⟩
    | some chosen => chosen.property ▸ ⟨rows.targetEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem identity_destination_some
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event ⟨source.toRootSource.account.supportOf event⟩)
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (indexed : {index : Fin rows.size // rows.sourceEntryAt index = entry})
    (selected : coverage.destinationIndex entry = some indexed) :
    (identityRemainderEvolution rows coverage).destination entry = indexed.property ▸ ⟨rows.targetEntryAt indexed.val, (rows.rowAt indexed.val).evolution⟩ := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N entry out) from match coverage.destinationIndex entry with
    | none => ⟨entry, .carried rfl HEq.rfl⟩
    | some chosen => chosen.property ▸ ⟨rows.targetEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem identity_origin_none
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event ⟨source.toRootSource.account.supportOf event⟩)
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (selected : coverage.originIndex entry = none) :
    (identityRemainderEvolution rows coverage).origin entry = ⟨entry, .carried rfl HEq.rfl⟩ := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N out entry) from match coverage.originIndex entry with
    | none => ⟨entry, .carried rfl HEq.rfl⟩
    | some chosen => chosen.property ▸ ⟨rows.sourceEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem identity_origin_some
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event ⟨source.toRootSource.account.supportOf event⟩)
    (coverage : LedgerIdentityRemainderCoverageAt rows)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (indexed : {index : Fin rows.size // rows.targetEntryAt index = entry})
    (selected : coverage.originIndex entry = some indexed) :
    (identityRemainderEvolution rows coverage).origin entry = indexed.property ▸ ⟨rows.sourceEntryAt indexed.val, (rows.rowAt indexed.val).evolution⟩ := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N out entry) from match coverage.originIndex entry with
    | none => ⟨entry, .carried rfl HEq.rfl⟩
    | some chosen => chosen.property ▸ ⟨rows.sourceEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem remainder_destination_none {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (remainder : GeneratedLedgerTransportedRemainderAt rowSource event target)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (selected : coverage.destinationIndex entry = none) :
    (transportedRemainderEvolution rows coverage remainder).destination entry = remainder.evolution.destination entry := by
  change (show (Σ out : target.Entry, LedgerEntryEvolutionAt N entry out) from match coverage.destinationIndex entry with
    | none => remainder.evolution.destination entry
    | some chosen => chosen.property ▸ ⟨rows.targetEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem remainder_destination_some {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (remainder : GeneratedLedgerTransportedRemainderAt rowSource event target)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event))
    (indexed : {index : Fin rows.size // rows.sourceEntryAt index = entry})
    (selected : coverage.destinationIndex entry = some indexed) :
    (transportedRemainderEvolution rows coverage remainder).destination entry = indexed.property ▸ ⟨rows.targetEntryAt indexed.val, (rows.rowAt indexed.val).evolution⟩ := by
  change (show (Σ out : target.Entry, LedgerEntryEvolutionAt N entry out) from match coverage.destinationIndex entry with
    | none => remainder.evolution.destination entry
    | some chosen => chosen.property ▸ ⟨rows.targetEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem remainder_origin_none {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (remainder : GeneratedLedgerTransportedRemainderAt rowSource event target)
    (entry : OpenResponsibilityAt N (target.support))
    (selected : coverage.originIndex entry = none) :
    (transportedRemainderEvolution rows coverage remainder).origin entry = remainder.evolution.origin entry := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N out entry) from match coverage.originIndex entry with
    | none => remainder.evolution.origin entry
    | some chosen => chosen.property ▸ ⟨rows.sourceEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem remainder_origin_some {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerTransportedRemainderCoverageAt rows)
    (remainder : GeneratedLedgerTransportedRemainderAt rowSource event target)
    (entry : OpenResponsibilityAt N (target.support))
    (indexed : {index : Fin rows.size // rows.targetEntryAt index = entry})
    (selected : coverage.originIndex entry = some indexed) :
    (transportedRemainderEvolution rows coverage remainder).origin entry = indexed.property ▸ ⟨rows.sourceEntryAt indexed.val, (rows.rowAt indexed.val).evolution⟩ := by
  change (show (Σ out : OpenResponsibilityAt N (source.toRootSource.account.supportOf event), LedgerEntryEvolutionAt N out entry) from match coverage.originIndex entry with
    | none => remainder.evolution.origin entry
    | some chosen => chosen.property ▸ ⟨rows.sourceEntryAt chosen.val, (rows.rowAt chosen.val).evolution⟩) = _
  rw [selected]

theorem complete_destination_at {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerCompleteFiniteCoverageAt rows)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event)) (index : Fin rows.size)
    (index_eq : coverage.destinationIndex entry = index)
    (entry_eq : rows.sourceEntryAt index = entry) :
    (completeEvolution rows coverage).destination entry =
      Eq.mp (congrArg (fun a => Σ b : target.Entry, LedgerEntryEvolutionAt N a b) entry_eq)
        ⟨rows.targetEntryAt index, (rows.rowAt index).evolution⟩ := by
  cases index_eq
  exact (sigma_cast (fun a b => LedgerEntryEvolutionAt N a b) entry_eq
    (rows.targetEntryAt (coverage.destinationIndex entry))
    (rows.rowAt (coverage.destinationIndex entry)).evolution).symm

theorem complete_origin_at {target : CompleteLiveLedgerAt N}
    (rows : FiniteGeneratedLedgerWriteRowsAt rowSource event target)
    (coverage : LedgerCompleteFiniteCoverageAt rows)
    (entry : OpenResponsibilityAt N (target.support)) (index : Fin rows.size)
    (index_eq : coverage.originIndex entry = index)
    (entry_eq : rows.targetEntryAt index = entry) :
    (completeEvolution rows coverage).origin entry =
      Eq.mp (congrArg (fun b => Σ a : OpenResponsibilityAt N (source.toRootSource.account.supportOf event),
        LedgerEntryEvolutionAt N a b) entry_eq) ⟨rows.sourceEntryAt index, (rows.rowAt index).evolution⟩ := by
  cases index_eq
  exact (sigma_cast (fun b a => LedgerEntryEvolutionAt N a b) entry_eq
    (rows.sourceEntryAt (coverage.originIndex entry))
    (rows.rowAt (coverage.originIndex entry)).evolution).symm

theorem terminal_discharge_at {rowSource : LedgerTerminalRowSourceAt source}
    (patch : FiniteGeneratedLedgerTerminalPatchAt rowSource event)
    (entry : OpenResponsibilityAt N (source.toRootSource.account.supportOf event)) (index : Fin patch.size)
    (index_eq : patch.entryIndex entry = index) (entry_eq : patch.entryAt index = entry) :
    patch.toLedgerTerminalEvolution.discharge entry = entry_eq ▸ (patch.rowAt index).terminal := by
  cases index_eq
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNetworkOrigin
