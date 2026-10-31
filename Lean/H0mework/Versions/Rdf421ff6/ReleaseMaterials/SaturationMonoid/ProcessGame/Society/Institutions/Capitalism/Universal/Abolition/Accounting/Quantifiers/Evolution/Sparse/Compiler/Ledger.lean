import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Patch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

private theorem source_choice (current : code.Current) (origin : code.Fibre) :
    (source code).toRootSource.actual.compile (represented code current origin) =
        if active : code.writes current = true then EvolutionAt.nativeWrite (V := V code) ⟨active⟩
      else .continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ := rfl

def terminalRowSource : LedgerTerminalRowSourceAt (source code) where
  IncidenceOccurrenceAt := fun _ _ => PEmpty
  compile := fun impossible => nomatch impossible

def sourcePacket {current : code.Current} (occurrence : (source code).toRootSource.actual.OccurrenceAt current) :
    Σ image : SourceNativeLedgerEvolutionAt (source code) occurrence,
      SourceNativeFiniteLedgerPatchAt (source code) (ExactTransitionAt code) (rowSource code) (terminalRowSource code) image := by
  rcases occurrence with ⟨oldSupport,event⟩
  cases event with
  | emitted origin =>
    if active : code.writes current = true then
      exact ⟨.nativeWrite ⟨active⟩ (by change (if write : code.writes current = true then _ else _) = _; exact dif_pos active)
      (represented code (code.next current) origin) (patch code current origin).toLedgerWriteEvolution,⟨patch code current origin,rfl⟩⟩
    else
      exact ⟨.continuedTransport ⟨Bool.eq_false_of_not_eq_true active⟩ (by change (if write : code.writes current = true then _ else _) = _; exact dif_neg active)
      (represented code (code.next current) origin) (patch code current origin).toLedgerWriteEvolution,⟨patch code current origin,rfl⟩⟩

def ledgerCompiler : SourceNativeLedgerCompiler (source code) where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt code
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun exact => exact.evolution.toDebtLineage.lineage_eq
  writeRowSource := rowSource code
  terminalRowSource := terminalRowSource code
  compile := fun occurrence => (sourcePacket code occurrence).1
  compilePatch := fun occurrence => (sourcePacket code occurrence).2

def ledgerSource : SourceNativeLedgerSource N (V code) where
  source := source code
  ledgerCompiler := ledgerCompiler code

def ledgerRoot : SourceNativeLedgerRootClosure N (V code) where
  source := ledgerSource code
  emitted := emitted code
  compiler_commutes := by
    intro current
    change ((ledgerCompiler code).compile (emitted code current)).CommutesWith _
    dsimp only [ledgerCompiler,sourcePacket,emitted,represented]
    split <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
