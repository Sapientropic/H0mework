import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteGenerated
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The complete programmes are formed at the already selected rank, on
the literal source output. This permits a later root to pay all its operands
once, without changing the source midway through compilation. -/
theorem programmes_on_source {rank : Ordinal.{0}}
    {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (compiler : SourceNativeLedgerCompiler original)
    (parent : MotherArenaHigher.Material rank)
    (sourceFormed : MotherArenaSource.formSource parent = some ⟨G, W, generated⟩)
    (encode : SourceWriteTotal compiler ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ compiled : CompilationSection generated, ∃ terminal : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated, ∃ rows : LedgerWriteRowSourceAt generated operations.exactTransitionAt,
      ∃ _terminalPresentation : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) terminal,
      ∃ q : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
      ∃ _r : WritePresentation (sourceWrite p q compiler.writeRowSource) rows,
        formWritePrograms material = some ⟨⟨G, W, generated⟩, compiled, terminal, operations, rows⟩ ∧
        (∀ point : Point original,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) := by
  let terminalCode : TerminalTotal compiler.terminalRowSource ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => encode (.inl (.inl (.inr value))),
      fun _ _ same => Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (encode.injective same)))⟩
  let transitionCode : TransitionTotal (Transitions.ofCompiler compiler) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => encode (.inl (.inr value)),
      fun _ _ same => Sum.inr.inj (Sum.inl.inj (encode.injective same))⟩
  let writeCode : WriteTotal (operations := Transitions.ofCompiler compiler) compiler.writeRowSource ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  obtain ⟨compiledMaterial, compiled, compiledFormed, recover⟩ :=
    MotherArenaCompiler.compilation_on_source p compiler parent sourceFormed
  obtain ⟨terminalMaterial, terminal, terminalFormed, ⟨t⟩⟩ :=
    MotherArenaPrograms.every_terminal_program compiledMaterial ⟨G, W, generated⟩ compiled compiledFormed
      (transportedTerminal p compiler.terminalRowSource)
      ((terminalTotalEquiv p compiler.terminalRowSource).symm.toEmbedding.trans terminalCode)
  obtain ⟨transitionMaterial, operations, transitionsFormed, ⟨q⟩⟩ :=
    every_transition_program terminalMaterial ⟨G, W, generated⟩ compiled terminal terminalFormed
      (transportedTransitions p (Transitions.ofCompiler compiler))
      ((transitionTotalEquiv p (Transitions.ofCompiler compiler)).symm.toEmbedding.trans transitionCode)
  obtain ⟨material, rows, formed, ⟨r⟩⟩ := every_write_program transitionMaterial
    ⟨⟨G, W, generated⟩, compiled, terminal, operations⟩ transitionsFormed (sourceWrite p q compiler.writeRowSource)
    ((totalEquiv p q compiler.writeRowSource).symm.toEmbedding.trans writeCode)
  exact ⟨material, compiled, terminal, operations, rows, t, q, r, formed, recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
