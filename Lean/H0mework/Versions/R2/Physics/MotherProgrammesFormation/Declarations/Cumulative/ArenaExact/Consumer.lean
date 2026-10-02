import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.JointFormation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- All complete source-owned programmes and their actual generators share
one sufficient rank; no event family is restricted to its selected members. -/
theorem every_programme (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank, ∃ G : WorldRelationNetwork.{0}, ∃ W : ConstructiveRoot.Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
      ∃ _terminalPresentation : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
        formWritePrograms material = some ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩ ∧
        (∀ point : Point original,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) ∧
        (∀ context : WriteContext original,
          ∀ row : GeneratedLedgerWriteRowAt compiler.writeRowSource context.2.1 context.2.2.2.1 context.2.2.2.2,
          (completeRowSeal p q r context).symm (completeRowSeal p q r context row) = row ∧
          (rowOutputEquiv p q context).symm ((completeRowSeal p q r context row).evolution, (completeRowSeal p q r context row).exact) =
            (row.evolution, row.exact)) ∧
        (∀ (point : Point original) (target : CompleteLiveLedgerAt N),
          Option.map (completeRemainder p q r point target) (compiler.writeRowSource.generateTransportedRemainder? point.2 target) =
            rows.generateTransportedRemainder? (pointEquiv p point).2 ⟨n.support target.support⟩) ∧
        (∀ (point : Point original) (target : CompleteLiveLedgerAt N)
          (rest : GeneratedLedgerTransportedRemainderAt compiler.writeRowSource point.2 target),
          (remainderOutputEquiv p q (point, target.support)).symm
            ⟨(completeRemainder p q r point target rest).evolution, (completeRemainder p q r point target rest).exact⟩ =
              ⟨rest.evolution, rest.exact⟩) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let AllAddresses := SourceWriteTotal compiler ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let encode : SourceWriteTotal compiler ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let sourceCode : MotherNativeSourceOrigin.Total original ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => encode (.inl (.inl (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨parent, G, W, generated, n, v, formedSource, ⟨p⟩⟩ :=
    MotherArenaSource.every_jointly_embedded_source N V original sourceCode
  obtain ⟨material, compiled, terminal, operations, rows, t, q, r, formed, compilation⟩ :=
    programmes_on_source p compiler parent formedSource encode
  exact ⟨rank, material, G, W, generated, compiled, terminal, operations, rows, n, v, p, t, q, r, formed, compilation,
    fun context row => ⟨(completeRowSeal p q r context).symm_apply_apply row, completeRow_payload p q r context row⟩,
    completeRemainder_generate p q r, completeRemainder_payload p q r,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
