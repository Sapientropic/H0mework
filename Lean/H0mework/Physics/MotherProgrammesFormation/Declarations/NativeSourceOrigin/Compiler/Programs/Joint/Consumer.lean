import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Formation

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

def completeRowSeal (context : WriteContext original) :
    GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2 ≃
      GeneratedLedgerWriteRowAt output (writeContextEquiv p context).2.1
        (writeContextEquiv p context).2.2.2.1 (writeContextEquiv p context).2.2.2.2 :=
  (writeSealEquiv rows context).trans
    ((completeRowEvent p q r context).trans (writeSealEquiv output (writeContextEquiv p context)).symm)

theorem completeRow_payload (context : WriteContext original)
    (row : GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (rowOutputEquiv p q context).symm ((completeRowSeal p q r context row).evolution, (completeRowSeal p q r context row).exact) =
      (row.evolution, row.exact) :=
  (complete_row_compilation p q r context row.event).trans
    (congrArg₂ (fun evolution exactValue => (evolution, exactValue)) row.evolution_eq row.exact_eq)

def completeRemainder (point : Point original) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    GeneratedLedgerTransportedRemainderAt output (pointEquiv p point).2 ⟨n.support target.support⟩ :=
  output.generateTransportedRemainder (pointEquiv p point).2 ⟨n.support target.support⟩
    (completeRemainderEvent p q r (point, target.support) value.event)
    ((complete_remainder_emit p q r (point, target.support)).symm.trans
      (congrArg (Option.map (completeRemainderEvent p q r (point, target.support))) value.selected))

theorem completeRemainder_event (point : Point original) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    (completeRemainder p q r point target value).event = completeRemainderEvent p q r (point, target.support) value.event := rfl

theorem completeRemainder_payload (point : Point original) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt rows point.2 target) :
    (remainderOutputEquiv p q (point, target.support)).symm
      ⟨(completeRemainder p q r point target value).evolution, (completeRemainder p q r point target value).exact⟩ =
        ⟨value.evolution, value.exact⟩ :=
  complete_remainder_compilation p q r (point, target.support) value.event

theorem completeRemainder_generate (point : Point original) (target : CompleteLiveLedgerAt N) :
    Option.map (completeRemainder p q r point target) (rows.generateTransportedRemainder? point.2 target) =
      output.generateTransportedRemainder? (pointEquiv p point).2 ⟨n.support target.support⟩ := by
  cases selected : rows.generateTransportedRemainder? point.2 target with
  | some value => exact (remainder_generated (completeRemainder p q r point target value)).symm
  | none =>
      have absent : rows.transportedRemainderSource.emit? point.2 target.support = none := by
        by_cases emitted : rows.transportedRemainderSource.emit? point.2 target.support = none
        · exact emitted
        · obtain ⟨event, eventEq⟩ := Option.ne_none_iff_exists'.mp emitted
          have produced := remainder_generated (rows.generateTransportedRemainder point.2 target event eventEq)
          rw [selected] at produced
          cases produced
      have transported : output.transportedRemainderSource.emit? (pointEquiv p point).2 (n.support target.support) = none :=
        (complete_remainder_emit p q r (point, target.support)).symm.trans
          (congrArg (Option.map (completeRemainderEvent p q r (point, target.support))) absent)
      unfold LedgerWriteRowSourceAt.generateTransportedRemainder?
      split
      · rfl
      · rename_i event eventEq
        cases transported.symm.trans eventEq

theorem formed_source_consumes_original_generators (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
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
              ⟨rest.evolution, rest.exact⟩) := by
  obtain ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, terminalPresentation, q, r,
    formed, compilation, _row, _remainder, _selector⟩ :=
      formed_source_recovers_original_programmes N V original compiler encode
  exact ⟨material, G, W, generated, compiled, terminal, operations, rows, n, v, p, terminalPresentation, q, r, formed, compilation,
    fun context row => ⟨(completeRowSeal p q r context).symm_apply_apply row, completeRow_payload p q r context row⟩,
    completeRemainder_generate p q r, completeRemainder_payload p q r⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
