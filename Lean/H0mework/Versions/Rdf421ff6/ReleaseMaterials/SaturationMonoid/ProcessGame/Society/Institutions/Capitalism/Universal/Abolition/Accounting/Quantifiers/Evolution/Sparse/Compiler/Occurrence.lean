import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Root
import H0mework.Versions.R2.Foundation.Cofinal.TemporalAnswer

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

def successor (current : code.Current) : SourceNativeLedgerGeneratedSuccessorAt (emitted code current)
    ((livingRoot code).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current) := by
  change SourceNativeLedgerGeneratedSuccessorAt (emitted code current) ((ledgerCompiler code).compile (emitted code current))
  dsimp only [ledgerCompiler,sourcePacket,emitted,represented]
  split <;> exact PUnit.unit

theorem next_eq (current : code.Current) :
    ((livingRoot code).toAuthoritativeRoot.toRoot.evolutionAt current).nextCurrent? = some (code.next current) := by
  change ((source code).toRootSource.actual.compile (emitted code current)).nextCurrent? = _
  change (if write : code.writes current = true then
    EvolutionAt.nativeWrite (V := V code) ⟨write⟩ else
    EvolutionAt.continuedTransport ⟨Bool.eq_false_of_not_eq_true write⟩).nextCurrent? = _
  split <;> rfl

theorem successor_current (current : code.Current) : (successor code current).targetCurrent = code.next current :=
  Option.some.inj ((successor code current).next_eq.symm.trans (next_eq code current))

def generatedRow (visit : SourceNativeTemporalVisitAt (livingRoot code).toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N (code.support visit.current)) :
    ((livingRoot code).toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit).GeneratedEntryRowAt entry := by
  let compiler := ledgerCompiler code
  let occurrence := emitted code visit.current
  let selected := sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource
    (compiler.compile occurrence) (compiler.compilePatch occurrence) entry
  have present : selected.isSome = true := by
    let check (packet : Σ image : SourceNativeLedgerEvolutionAt _ occurrence,
        SourceNativeFiniteLedgerPatchAt _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource image) : Bool :=
      (sourceNativeFiniteLedgerPatchGeneratedEntry? _ compiler.ExactTransitionAt compiler.writeRowSource compiler.terminalRowSource packet.1 packet.2 entry).isSome
    change check (sourcePacket code occurrence) = true
    dsimp only [occurrence,sourcePacket,emitted,represented]
    split <;> rfl
  exact SourceNativeTemporalVisitGeneratedEvolutionAt.GeneratedEntryRowAt.ofSourceRow (selected.get present)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
