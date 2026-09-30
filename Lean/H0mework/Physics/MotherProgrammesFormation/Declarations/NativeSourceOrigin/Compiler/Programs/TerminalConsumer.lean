import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.TerminalFormation
import H0mework.Physics.MotherProgrammesFormation.Declarations.NetworkOrigin.Ledger.TerminalRows

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def terminalSealEquiv {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) (context : RowContext source) :
    GeneratedLedgerTerminalRowAt rows context.1.2 context.2 ≃ RowEvents rows context where
  toFun := fun row => row.event
  invFun := rows.generate
  left_inv := by
    rintro ⟨event, terminal, same⟩
    cases same
    rfl
  right_inv := fun _ => rfl

theorem settlementSeal_eq {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {rows : LedgerTerminalRowSourceAt source} {point : Point source}
    (left right : GeneratedLedgerSupportSettlementAt rows point.2) : left = right := by
  have same := Option.some.inj (left.selected.symm.trans right.selected)
  cases left
  cases right
  cases same
  rfl

theorem settlement_generated {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {rows : LedgerTerminalRowSourceAt source} {point : Point source}
    (value : GeneratedLedgerSupportSettlementAt rows point.2) :
    rows.generateSupportSettlement? point.2 = some value := by
  unfold LedgerTerminalRowSourceAt.generateSupportSettlement?
  split
  · rename_i absent
    cases value.selected.symm.trans absent
  · congr 1
    exact settlementSeal_eq _ _

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : LedgerTerminalRowSourceAt original} {rows : LedgerTerminalRowSourceAt generated}
    (q : TerminalPresentation (transportedTerminal p old) rows)

def formedRowEvent (context : RowContext original) :
    RowEvents old context ≃ RowEvents rows (rowContextEquiv p context) :=
  (terminalEventEquiv p old context).trans (q.row (rowContextEquiv p context))

def formedSettlementEvent (point : Point original) :
    SettlementEvents old point ≃ SettlementEvents rows (pointEquiv p point) :=
  (settlementEventEquiv p old point).trans (q.settlement (pointEquiv p point))

/-- The original seal is recovered as a whole, including its stored terminal
value and proof. Only the original generator constructs the new seal. -/
def formedRowEquiv (context : RowContext original) :
    GeneratedLedgerTerminalRowAt old context.1.2 context.2 ≃
      GeneratedLedgerTerminalRowAt rows (rowContextEquiv p context).1.2 (rowContextEquiv p context).2 :=
  (terminalSealEquiv old context).trans
    ((formedRowEvent p q context).trans (terminalSealEquiv rows (rowContextEquiv p context)).symm)

theorem formedRow_event (context : RowContext original)
    (row : GeneratedLedgerTerminalRowAt old context.1.2 context.2) :
    (formedRowEquiv p q context row).event = formedRowEvent p q context row.event := rfl

theorem formedRow_receipt (context : RowContext original)
    (row : GeneratedLedgerTerminalRowAt old context.1.2 context.2) :
    (formedRowEquiv p q context row).terminal.receipt = receiptEquiv p context.1 row.terminal.receipt := by
  change (rows.compile (q.row _ (terminalEventEquiv p old context row.event))).receipt = _
  rw [q.row_compile]
  exact (terminal_compile p old context row.event).trans
    (congrArg (fun terminal => receiptEquiv p context.1 terminal.receipt) row.terminal_eq)

theorem formedRow_generate (context : RowContext original) (event : RowEvents old context) :
    formedRowEquiv p q context (old.generate event) = rows.generate (formedRowEvent p q context event) := rfl

theorem formedSettlement_emit (point : Point original) :
    Option.map (formedSettlementEvent p q point) (old.supportSettlementSource.emit? point.2) =
      rows.supportSettlementSource.emit? (pointEquiv p point).2 := by
  change Option.map ((q.settlement _) ∘ (settlementEventEquiv p old point)) _ = _
  rw [← Option.map_map, settlement_emit, q.settlement_emit]

def formedSettlement (point : Point original) (value : GeneratedLedgerSupportSettlementAt old point.2) :
    GeneratedLedgerSupportSettlementAt rows (pointEquiv p point).2 :=
  MotherNetworkOrigin.sealSettlement rows (pointEquiv p point).2 (formedSettlementEvent p q point value.event)
    ((formedSettlement_emit p q point).symm.trans (congrArg (Option.map (formedSettlementEvent p q point)) value.selected))

theorem formedSettlement_event (point : Point original) (value : GeneratedLedgerSupportSettlementAt old point.2) :
    (formedSettlement p q point value).event = formedSettlementEvent p q point value.event :=
  MotherNetworkOrigin.sealSettlement_event _ _ _ _

theorem formedSettlement_receipt (point : Point original) (value : GeneratedLedgerSupportSettlementAt old point.2) :
    (formedSettlement p q point value).receipt = receiptEquiv p point value.receipt := by
  change rows.supportSettlementSource.compile (formedSettlement p q point value).event = _
  rw [formedSettlement_event]
  change rows.supportSettlementSource.compile (q.settlement _ (settlementEventEquiv p old point value.event)) = _
  rw [q.settlement_compile]
  exact settlement_compile p old point value.event

theorem formedSettlement_discharge (point : Point original)
    (value : GeneratedLedgerSupportSettlementAt old point.2) (entry : OpenResponsibilityAt N point.2.1) :
    ((formedSettlement p q point value).toLedgerTerminalEvolution.discharge
      (rowContextEquiv p ⟨point, entry⟩).2).receipt =
      receiptEquiv p point (value.toLedgerTerminalEvolution.discharge entry).receipt :=
  formedSettlement_receipt p q point value

theorem formedSettlement_generate (point : Point original) :
    Option.map (formedSettlement p q point) (old.generateSupportSettlement? point.2) =
      rows.generateSupportSettlement? (pointEquiv p point).2 := by
  cases selected : old.generateSupportSettlement? point.2 with
  | some value =>
      exact (settlement_generated (formedSettlement p q point value)).symm
  | none =>
      have absent : old.supportSettlementSource.emit? point.2 = none := by
        by_cases emitted : old.supportSettlementSource.emit? point.2 = none
        · exact emitted
        · obtain ⟨event, eventEq⟩ := Option.ne_none_iff_exists'.mp emitted
          have produced := settlement_generated (MotherNetworkOrigin.sealSettlement old point.2 event eventEq)
          rw [selected] at produced
          cases produced
      have transported : rows.supportSettlementSource.emit? (pointEquiv p point).2 = none :=
        (formedSettlement_emit p q point).symm.trans (congrArg (Option.map (formedSettlementEvent p q point)) absent)
      unfold LedgerTerminalRowSourceAt.generateSupportSettlement?
      split
      · rfl
      · rename_i event eventEq
        cases transported.symm.trans eventEq

/-- A single formed output retains full compilation values, all terminal
events, original row seals and the actual optional whole-support generator. -/
theorem formed_terminal_consumes_original_generators (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceTerminalTotal compiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ rows : LedgerTerminalRowSourceAt generated,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
      ∃ q : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) rows,
        formTerminalSource material = some ⟨⟨G, W, generated⟩, compiled, rows⟩ ∧
        (∀ point : Point original,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) ∧
        (∀ context : RowContext original, ∀ row : GeneratedLedgerTerminalRowAt compiler.terminalRowSource context.1.2 context.2,
          (formedRowEquiv p q context).symm (formedRowEquiv p q context row) = row ∧
          (formedRowEquiv p q context row).terminal.receipt = receiptEquiv p context.1 row.terminal.receipt) ∧
        (∀ point : Point original,
          Option.map (formedSettlement p q point) (compiler.terminalRowSource.generateSupportSettlement? point.2) =
            rows.generateSupportSettlement? (pointEquiv p point).2) ∧
        (∀ point : Point original, ∀ value : GeneratedLedgerSupportSettlementAt compiler.terminalRowSource point.2,
          (formedSettlement p q point value).event = formedSettlementEvent p q point value.event ∧
          (receiptEquiv p point).symm (formedSettlement p q point value).receipt = value.receipt) := by
  obtain ⟨material, G, W, generated, compiled, rows, n, v, p, q, formed, recover⟩ :=
    formed_terminal_recovers_original_programs N V original compiler encode
  refine ⟨material, G, W, generated, compiled, rows, n, v, p, q, formed, recover, ?_,
    formedSettlement_generate p q, ?_⟩
  · exact fun context row => ⟨(formedRowEquiv p q context).symm_apply_apply row, formedRow_receipt p q context row⟩
  · intro point value
    refine ⟨formedSettlement_event p q point value, ?_⟩
    rw [formedSettlement_receipt]
    exact (receiptEquiv p point).symm_apply_apply value.receipt

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
