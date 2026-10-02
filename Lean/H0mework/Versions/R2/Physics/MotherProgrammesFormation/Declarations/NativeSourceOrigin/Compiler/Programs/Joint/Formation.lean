import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Source

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)
    {rows : LedgerWriteRowSourceAt original old.exactTransitionAt}
    {output : LedgerWriteRowSourceAt generated formed.exactTransitionAt}
    (r : WritePresentation (sourceWrite p q rows) output)

def completeRowEvent (context : WriteContext original) :
    WriteEvents rows context ≃ WriteEvents output (writeContextEquiv p context) :=
  (rowEventEquiv p q rows context).trans (r.row (writeContextEquiv p context))

def completeRemainderEvent (context : RemainderContext original) :
    RemainderEvents rows context ≃ RemainderEvents output (remainderContextEquiv p context) :=
  (remainderEventEquiv p q rows context).trans (r.remainder (remainderContextEquiv p context))

theorem complete_row_compilation (context : WriteContext original) (event : WriteEvents rows context) :
    (rowOutputEquiv p q context).symm
      (output.compileEvolution (completeRowEvent p q r context event), output.compileExact (completeRowEvent p q r context event)) =
        (rows.compileEvolution event, rows.compileExact event) := by
  have same := congrArg₂ (fun evolution exactValue => (evolution, exactValue))
    (r.row_evolution (writeContextEquiv p context) (rowEventEquiv p q rows context event))
    (r.row_exact (writeContextEquiv p context) (rowEventEquiv p q rows context event))
  exact (congrArg (rowOutputEquiv p q context).symm (same.trans (row_compile p q rows context event))).trans
    ((rowOutputEquiv p q context).symm_apply_apply (rows.compileEvolution event, rows.compileExact event))

theorem complete_remainder_compilation (context : RemainderContext original) (event : RemainderEvents rows context) :
    (remainderOutputEquiv p q context).symm
      ⟨output.transportedRemainderSource.compileEvolution (completeRemainderEvent p q r context event),
        output.transportedRemainderSource.compileExact (completeRemainderEvent p q r context event)⟩ =
      ⟨rows.transportedRemainderSource.compileEvolution event, rows.transportedRemainderSource.compileExact event⟩ :=
  (congrArg (remainderOutputEquiv p q context).symm
    ((r.remainder_compile (remainderContextEquiv p context) (remainderEventEquiv p q rows context event)).trans
      (remainder_compile p q rows context event))).trans
    ((remainderOutputEquiv p q context).symm_apply_apply
      ⟨rows.transportedRemainderSource.compileEvolution event, rows.transportedRemainderSource.compileExact event⟩)

theorem complete_remainder_emit (context : RemainderContext original) :
    Option.map (completeRemainderEvent p q r context) (rows.transportedRemainderSource.emit? context.1.2 context.2) =
      output.transportedRemainderSource.emit? (remainderContextEquiv p context).1.2 (remainderContextEquiv p context).2 := by
  change Option.map ((r.remainder _) ∘ (remainderEventEquiv p q rows context)) _ = _
  rw [← Option.map_map, remainder_emit, r.remainder_emit]

abbrev SourceWriteTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) := SourceTransitionTotal compiler ⊕
      WriteTotal (operations := Transitions.ofCompiler compiler) compiler.writeRowSource

/-- One mother material recovers the complete original compiler programmes
on the same formed source; the original compiler is confined to coverage. -/
theorem formed_source_recovers_original_programmes (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceWriteTotal compiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
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
          ∀ event : WriteEvents (operations := Transitions.ofCompiler compiler) compiler.writeRowSource context,
          (rowOutputEquiv p q context).symm
            (rows.compileEvolution (completeRowEvent p q r context event), rows.compileExact (completeRowEvent p q r context event)) =
              (compiler.writeRowSource.compileEvolution event, compiler.writeRowSource.compileExact event)) ∧
        (∀ context : RemainderContext original,
          ∀ event : RemainderEvents (operations := Transitions.ofCompiler compiler) compiler.writeRowSource context,
          (remainderOutputEquiv p q context).symm
            ⟨rows.transportedRemainderSource.compileEvolution (completeRemainderEvent p q r context event),
              rows.transportedRemainderSource.compileExact (completeRemainderEvent p q r context event)⟩ =
            ⟨compiler.writeRowSource.transportedRemainderSource.compileEvolution event,
              compiler.writeRowSource.transportedRemainderSource.compileExact event⟩) ∧
        (∀ context : RemainderContext original,
          Option.map (completeRemainderEvent p q r context)
            (compiler.writeRowSource.transportedRemainderSource.emit? context.1.2 context.2) =
              rows.transportedRemainderSource.emit? (remainderContextEquiv p context).1.2 (remainderContextEquiv p context).2) := by
  let parentCode : SourceTransitionTotal compiler ↪ B :=
    ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let programmeCode : WriteTotal (operations := Transitions.ofCompiler compiler) compiler.writeRowSource ↪ B :=
    ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  obtain ⟨parent, G, W, generated, compiled, terminal, operations, n, v, p, terminalPresentation, q, parentFormed, compilation, _projection⟩ :=
    formed_transitions_recover_original_operations N V original compiler parentCode
  let code := (totalEquiv p q compiler.writeRowSource).symm.toEmbedding.trans programmeCode
  obtain ⟨material, rows, formed, ⟨r⟩⟩ := every_write_program parent
    ⟨⟨G, W, generated⟩, compiled, terminal, operations⟩ parentFormed (sourceWrite p q compiler.writeRowSource) code
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, terminalPresentation, q, r, formed, compilation,
    complete_row_compilation p q r, complete_remainder_compilation p q r, complete_remainder_emit p q r⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
