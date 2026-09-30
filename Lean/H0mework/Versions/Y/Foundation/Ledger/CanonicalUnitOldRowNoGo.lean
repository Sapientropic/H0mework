import H0mework.Versions.X.Arithmetic.UnitArithmetic.Root

/-!
# Exact old-row representation boundary

At the original unit root's actual `current → next current` transition, every
legal complete-ledger evolution is the same value.  This local theorem rules
out changing the old whole-ledger disposition by editing only a patch event or
compiler while retaining the literal old world and source.  It does not say a
domain residual is false or that a revised law has failed U7/U8.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalUnitArithmeticRoot

private theorem native_write_subsingleton (current : Current) :
    Subsingleton (NativeWriteAt current) := by
  constructor
  intro left right
  rcases left with ⟨leftTrace, leftTraceEq, leftTarget, leftActionEq,
    leftTargetEq, leftNe, leftWhole, leftWholeEq⟩
  rcases right with ⟨rightTrace, rightTraceEq, rightTarget, rightActionEq,
    rightTargetEq, rightNe, rightWhole, rightWholeEq⟩
  cases leftTraceEq
  cases rightTraceEq
  cases leftTargetEq
  cases rightTargetEq
  cases leftWholeEq
  cases rightWholeEq
  rfl

private theorem transfer_subsingleton (current : Current) :
    Subsingleton (N.DispositionAt current .transfer) := by
  constructor
  intro left right
  cases left with
  | transfer leftWrite =>
    cases right with
    | transfer rightWrite =>
      have h := (native_write_subsingleton current).elim leftWrite rightWrite
      cases h
      rfl

/-- Carry contradicts the actual support update, maintenance contradicts the
zero old budget, and the remaining transfer has a unique native receipt. -/
theorem old_row_evolution_unique (current : Current)
    (left right : LedgerEntryEvolutionAt N
      (rootLedgerEntry current) (rootLedgerEntry (next current))) :
    left = right := by
  cases left with
  | carried supportEq _ =>
    change current = next current at supportEq
    exact False.elim ((nativeWriteAt current).target_ne_source supportEq.symm)
  | maintained _ _ _ _ _ debit =>
    exact False.elim ((rootLedgerEntry_no_strict_payment current) debit)
  | transferred leftReceipt _ _ _ =>
    cases right with
    | carried supportEq _ =>
      change current = next current at supportEq
      exact False.elim ((nativeWriteAt current).target_ne_source supportEq.symm)
    | maintained _ _ _ _ _ debit =>
      exact False.elim ((rootLedgerEntry_no_strict_payment current) debit)
    | transferred rightReceipt _ _ _ =>
      have receiptEq := (transfer_subsingleton current).elim
        leftReceipt rightReceipt
      cases receiptEq
      rfl

private theorem old_row_evolution_subsingleton (current : Current)
    (source : OpenResponsibilityAt N current)
    (target : OpenResponsibilityAt N (next current)) :
    Subsingleton (LedgerEntryEvolutionAt N source target) := by
  cases rootLedgerEntry_unique current source
  cases rootLedgerEntry_unique (next current) target
  exact ⟨old_row_evolution_unique current⟩

/-- Every possible complete evolution of the original single live row at the
actual next support is equal, independently of the patch event encoding. -/
theorem old_whole_evolution_subsingleton (current : Current) :
    Subsingleton (LedgerWriteEvolutionAt N
      ⟨current⟩ ⟨next current⟩) := by
  constructor
  intro left right
  cases left with
  | mk leftDestination leftOrigin =>
    cases right with
    | mk rightDestination rightOrigin =>
      have destinationEq : leftDestination = rightDestination := by
        funext sourceEntry
        rcases leftDestination sourceEntry with ⟨leftTarget, leftEvolution⟩
        rcases rightDestination sourceEntry with ⟨rightTarget, rightEvolution⟩
        have targetEq := (rootEntry_subsingleton (next current)).elim
          leftTarget rightTarget
        cases targetEq
        have evolutionEq :=
          (old_row_evolution_subsingleton current sourceEntry leftTarget).elim
            leftEvolution rightEvolution
        cases evolutionEq
        rfl
      have originEq : leftOrigin = rightOrigin := by
        funext targetEntry
        rcases leftOrigin targetEntry with ⟨leftSource, leftEvolution⟩
        rcases rightOrigin targetEntry with ⟨rightSource, rightEvolution⟩
        have sourceEq := (rootEntry_subsingleton current).elim
          leftSource rightSource
        cases sourceEq
        have evolutionEq :=
          (old_row_evolution_subsingleton current leftSource targetEntry).elim
            leftEvolution rightEvolution
        cases evolutionEq
        rfl
      cases destinationEq
      cases originEq
      rfl

/-- The literal old whole-ledger result cannot faithfully store even a binary
distinction produced by a later dependent calculation at this occurrence. -/
theorem no_faithful_binary_writeback (current : Current) :
    ¬ ∃ encode : Bool → LedgerWriteEvolutionAt N
        ⟨current⟩ ⟨next current⟩,
      Function.Injective encode := by
  rintro ⟨encode, injective⟩
  have equal := (old_whole_evolution_subsingleton current).elim
    (encode false) (encode true)
  exact Bool.false_ne_true (injective equal)

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.CanonicalUnitArithmeticRoot
