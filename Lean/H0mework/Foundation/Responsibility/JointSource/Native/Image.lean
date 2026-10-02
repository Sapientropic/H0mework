import H0mework.Foundation.Responsibility.JointSource.Compiler

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}

/-- A complete native patch read from the old compiler, including the exact
row occurrences and the compiler's original coverage selectors. -/
structure CompleteImageAt (lower : SourceNativeLedgerRootClosure N V) (current : V.Current) : Type (u + 1) where
  private mk ::
  write : V.NativeWriteAt current
  structural_eq : lower.source.source.toRootSource.actual.compile (lower.emitted current) = .nativeWrite write
  targetOccurrence : lower.source.source.toRootSource.actual.OccurrenceAt (V.nativeTarget write)
  evolution : LedgerWriteEvolutionAt N
    ⟨lower.source.source.toRootSource.account.supportOf (lower.emitted current)⟩
    ⟨lower.source.source.toRootSource.account.supportOf targetOccurrence⟩
  generated_eq : lower.generatedLedgerAt current = .nativeWrite write structural_eq targetOccurrence evolution
  rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
    (lower.emitted current) ⟨lower.source.source.toRootSource.account.supportOf targetOccurrence⟩
  coverage : LedgerCompleteFiniteCoverageAt rows
  fold_eq : (FiniteGeneratedLedgerWritePatchAt.complete rows coverage).toLedgerWriteEvolution = evolution

private def completeRows? {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {target : CompleteLiveLedgerAt N}
    (patch : FiniteGeneratedLedgerWritePatchAt lower.source.ledgerCompiler.writeRowSource
      (lower.emitted current) target) :
    Option (Σ rows : FiniteGeneratedLedgerWriteRowsAt lower.source.ledgerCompiler.writeRowSource
        (lower.emitted current) target,
      Σ coverage : LedgerCompleteFiniteCoverageAt rows,
        PLift ((FiniteGeneratedLedgerWritePatchAt.complete rows coverage).toLedgerWriteEvolution =
          patch.toLedgerWriteEvolution)) :=
  match patch with
  | .complete rows coverage => some ⟨rows, coverage, ⟨rfl⟩⟩
  | .identityRemainder _ _ => none
  | .transportedRemainder _ _ _ => none

def read? (lower : SourceNativeLedgerRootClosure N V) (current : V.Current) :
    Option (CompleteImageAt lower current) := by
  cases generatedEq : lower.generatedLedgerAt current with
  | nativeWrite write structuralEq targetOccurrence evolution =>
      have selected := lower.generatedPatchAt current
      change SourceNativeFiniteLedgerPatchAt lower.source.source lower.source.ledgerCompiler.ExactTransitionAt
        lower.source.ledgerCompiler.writeRowSource lower.source.ledgerCompiler.terminalRowSource
        (lower.generatedLedgerAt current) at selected
      rw [generatedEq] at selected
      rcases selected with ⟨patch, foldEq⟩
      cases completeRows? patch with
      | none => exact none
      | some data => exact some ⟨write, structuralEq, targetOccurrence, evolution,
          generatedEq, data.1, data.2.1, data.2.2.down.trans foldEq⟩
  | relationWrite _ _ _ _ => exact none
  | continuedTransport _ _ _ _ => exact none
  | borromeanRedirect _ _ _ _ => exact none
  | faithfulTerminal _ _ _ => exact none

/-- A native source program returns receipts from its own actual compiler.
The installer receives no target equation or replacement coverage. -/
structure Program (lower : SourceNativeLedgerRootClosure N V) : Type (u + 1) where
  emit : (current : V.Current) → CompleteImageAt lower current

namespace CompleteImageAt

variable {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}

theorem target_emitted (image : CompleteImageAt lower current) :
    image.targetOccurrence = lower.emitted (V.nativeTarget image.write) := by
  have same := lower.compiler_commutes current
  change (lower.generatedLedgerAt current).CommutesWith lower.emitted at same
  rw [image.generated_eq] at same
  exact same

end CompleteImageAt

end RootGeneratedDebtActivationJointSource.Native
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
