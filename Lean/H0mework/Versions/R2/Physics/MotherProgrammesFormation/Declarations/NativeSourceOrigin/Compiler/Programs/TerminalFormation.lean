import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.TerminalCoverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.TerminalTransport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

abbrev TerminalTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) := Sigma (RowEvents rows) ⊕ Sigma (SettlementEvents rows)

def TerminalEncoding.ofTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {rows : LedgerTerminalRowSourceAt source} (encode : TerminalTotal rows ↪ B) : TerminalEncoding rows where
  row := ⟨fun event => encode (.inl event), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  settlement := ⟨fun event => encode (.inr event), fun _ _ same => Sum.inr.inj (encode.injective same)⟩

theorem every_terminal_program (parent : M) (value : SourceValue) (compiled : CompilationSection value.2.2)
    (formed : formCompilation parent = some ⟨value, compiled⟩) (rows : LedgerTerminalRowSourceAt value.2.2)
    (encode : TerminalTotal rows ↪ B) :
    ∃ material : M, ∃ generated : LedgerTerminalRowSourceAt value.2.2,
      formTerminalSource material = some ⟨value, compiled, generated⟩ ∧ Nonempty (TerminalPresentation rows generated) := by
  let coordinates := coordinatesOfCompilation parent value compiled formed
  let ledgerCoordinates := ledgerCoordinatesOfCompilation parent value compiled formed
  let code := TerminalEncoding.ofTotal encode
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective
    (TerminalEncoding.reader coordinates ledgerCoordinates rows code)
  let checked := TerminalEncoding.checked coordinates ledgerCoordinates rows code hm
  exact ⟨MotherHigherLawValue.pack (parent, material), terminalRows coordinates ledgerCoordinates material checked,
    terminal_source_formed parent material value compiled formed checked,
    ⟨TerminalEncoding.presentation coordinates ledgerCoordinates rows code hm⟩⟩

def terminalTotalEquiv {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated) (rows : LedgerTerminalRowSourceAt original) :
    TerminalTotal rows ≃ TerminalTotal (transportedTerminal p rows) :=
  Equiv.sumCongr (Equiv.sigmaCongr (rowContextEquiv p) (terminalEventEquiv p rows))
    (Equiv.sigmaCongr (pointEquiv p) (settlementEventEquiv p rows))

abbrev SourceTerminalTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :=
  MotherNativeSourceOrigin.Total source ⊕ TerminalTotal compiler.terminalRowSource

/-- One joint original total is used only in coverage. The complete original
compile section and terminal/settlement source are formed together. -/
theorem formed_terminal_recovers_original_programs (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceTerminalTotal compiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ rows : LedgerTerminalRowSourceAt generated,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
      ∃ _q : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) rows,
        formTerminalSource material = some ⟨⟨G, W, generated⟩, compiled, rows⟩ ∧
        ∀ point : Point original,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2 := by
  let sourceCode : MotherNativeSourceOrigin.Total original ↪ B :=
    ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let eventCode : TerminalTotal compiler.terminalRowSource ↪ B :=
    ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  obtain ⟨parent, G, W, generated, compiled, n, v, p, formed, recover⟩ :=
    formed_compilation_recovers_original_values N V original sourceCode compiler
  let generatedCode := (terminalTotalEquiv p compiler.terminalRowSource).symm.toEmbedding.trans eventCode
  obtain ⟨material, rows, rowsFormed, ⟨q⟩⟩ := every_terminal_program parent ⟨G, W, generated⟩ compiled formed
    (transportedTerminal p compiler.terminalRowSource) generatedCode
  exact ⟨material, G, W, generated, compiled, rows, n, v, p, q, rowsFormed, recover⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
