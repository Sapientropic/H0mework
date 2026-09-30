import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.Admission

/-! A full compiler restriction in the original type indices. Type families
are the targets of the paid inverse presentations. Every operation, selector,
receipt, compilation and patch value is read from the generated compiler.
This is a faithful restriction transporter, not a source-material factory. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

private theorem inverse_option {A B : Type} (e : A ≃ B) {first : Option A} {last : Option B}
    (same : Option.map e first = last) : Option.map e.symm last = first := by
  rw [← same, Option.map_map]
  have inverse : e.symm ∘ e = id := funext e.symm_apply_apply
  rw [inverse, Option.map_id]
  rfl

namespace CompilerPresentation

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {originalCompiler : SourceNativeLedgerCompiler original}
    {generatedCompiler : SourceNativeLedgerCompiler generated}
    (presentation : CompilerPresentation p originalCompiler generatedCompiler)

def restrictedProject (context : WriteContext original)
    (value : (Transitions.ofCompiler originalCompiler).Exact context) :
    (Transitions.ofCompiler originalCompiler).Incidence (incidenceContext context) :=
  (formedIncidenceAtWrite p presentation.transitions context).symm
    ((Transitions.ofCompiler generatedCompiler).project (writeContextEquiv p context)
      (formedExactMember p presentation.transitions context value))

theorem restrictedProject_eq : presentation.restrictedProject =
    (Transitions.ofCompiler originalCompiler).project := by
  funext context value
  exact (congrArg (formedIncidenceAtWrite p presentation.transitions context).symm
    (formed_project p presentation.transitions context value)).trans
      ((formedIncidenceAtWrite p presentation.transitions context).symm_apply_apply _)

def restrictedRows (context : WriteContext original)
    (event : WriteEvents (operations := Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource context) :
    RowOutput (Transitions.ofCompiler originalCompiler) context :=
  (rowOutputEquiv p presentation.transitions context).symm
    (generatedCompiler.writeRowSource.compileEvolution
      (completeRowEvent p presentation.transitions presentation.rows context event),
    generatedCompiler.writeRowSource.compileExact
      (completeRowEvent p presentation.transitions presentation.rows context event))

theorem restrictedRows_eq : presentation.restrictedRows =
    fun (context : WriteContext original)
      (event : WriteEvents (operations := Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource context) =>
      (originalCompiler.writeRowSource.compileEvolution event,
      originalCompiler.writeRowSource.compileExact event) := by
  funext context event
  exact complete_row_compilation p presentation.transitions presentation.rows context event

def restrictedRemainders (context : RemainderContext original)
    (event : RemainderEvents (operations := Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource context) :
    RemainderOutput (Transitions.ofCompiler originalCompiler) context :=
  (remainderOutputEquiv p presentation.transitions context).symm
    ⟨generatedCompiler.writeRowSource.transportedRemainderSource.compileEvolution
      (completeRemainderEvent p presentation.transitions presentation.rows context event),
    generatedCompiler.writeRowSource.transportedRemainderSource.compileExact
      (completeRemainderEvent p presentation.transitions presentation.rows context event)⟩

theorem restrictedRemainders_eq : presentation.restrictedRemainders =
    fun (context : RemainderContext original)
      (event : RemainderEvents (operations := Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource context) =>
      ⟨originalCompiler.writeRowSource.transportedRemainderSource.compileEvolution event,
      originalCompiler.writeRowSource.transportedRemainderSource.compileExact event⟩ := by
  funext context event
  exact complete_remainder_compilation p presentation.transitions presentation.rows context event

def restrictedRemainderSelector (context : RemainderContext original) :
    Option (RemainderEvents (operations := Transitions.ofCompiler originalCompiler) originalCompiler.writeRowSource context) :=
  Option.map (completeRemainderEvent p presentation.transitions presentation.rows context).symm
    (generatedCompiler.writeRowSource.transportedRemainderSource.emit?
      (remainderContextEquiv p context).1.2 (remainderContextEquiv p context).2)

theorem restrictedRemainderSelector_eq : presentation.restrictedRemainderSelector =
    fun (context : RemainderContext original) => originalCompiler.writeRowSource.transportedRemainderSource.emit? context.1.2 context.2 := by
  funext context
  exact inverse_option (completeRemainderEvent p presentation.transitions presentation.rows context)
    (complete_remainder_emit p presentation.transitions presentation.rows context)

def restrictRemainderSource : LedgerTransportedRemainderSourceAt original originalCompiler.ExactTransitionAt where
  OccurrenceAt := originalCompiler.writeRowSource.transportedRemainderSource.OccurrenceAt
  emit? := fun {current} event target => presentation.restrictedRemainderSelector (⟨current, event⟩, target)
  compileEvolution := fun {current} {event} {target} value =>
    (presentation.restrictedRemainders (⟨current, event⟩, target) value).1
  compileExact := fun {current} {event} {target} value =>
    (presentation.restrictedRemainders (⟨current, event⟩, target) value).2

theorem restrictRemainderSource_eq :
    presentation.restrictRemainderSource = originalCompiler.writeRowSource.transportedRemainderSource := by
  unfold restrictRemainderSource
  rw [presentation.restrictedRemainders_eq, presentation.restrictedRemainderSelector_eq]

def restrictWriteSource : LedgerWriteRowSourceAt original originalCompiler.ExactTransitionAt where
  IncidenceOccurrenceAt := originalCompiler.writeRowSource.IncidenceOccurrenceAt
  compileEvolution := fun {current} {event} {target} {first} {last} value =>
    (presentation.restrictedRows ⟨current, event, target, first, last⟩ value).1
  compileExact := fun {current} {event} {target} {first} {last} value =>
    (presentation.restrictedRows ⟨current, event, target, first, last⟩ value).2
  transportedRemainderSource := presentation.restrictRemainderSource

theorem restrictWriteSource_eq : presentation.restrictWriteSource = originalCompiler.writeRowSource := by
  unfold restrictWriteSource
  rw [presentation.restrictedRows_eq, presentation.restrictRemainderSource_eq]

def restrictedTerminalReceipts (context : RowContext original)
    (event : RowEvents originalCompiler.terminalRowSource context) : Receipt context.1 :=
  (receiptEquiv p context.1).symm
    (generatedCompiler.terminalRowSource.compile (formedRowEvent p presentation.terminal context event)).receipt

theorem restrictedTerminalReceipts_eq : presentation.restrictedTerminalReceipts =
    fun (context : RowContext original) (event : RowEvents originalCompiler.terminalRowSource context) =>
      (originalCompiler.terminalRowSource.compile event).receipt := by
  funext context event
  exact (congrArg (receiptEquiv p context.1).symm
    (formedRow_receipt p presentation.terminal context (originalCompiler.terminalRowSource.generate event))).trans
      ((receiptEquiv p context.1).symm_apply_apply _)

def restrictedSettlements (point : Point original)
    (event : SettlementEvents originalCompiler.terminalRowSource point) : Receipt point :=
  (receiptEquiv p point).symm (generatedCompiler.terminalRowSource.supportSettlementSource.compile
    (formedSettlementEvent p presentation.terminal point event))

theorem restrictedSettlements_eq : presentation.restrictedSettlements =
    fun (point : Point original) (event : SettlementEvents originalCompiler.terminalRowSource point) =>
      originalCompiler.terminalRowSource.supportSettlementSource.compile event := by
  funext point event
  have same := (presentation.terminal.settlement_compile (pointEquiv p point)
    (settlementEventEquiv p originalCompiler.terminalRowSource point event)).trans
      (settlement_compile p originalCompiler.terminalRowSource point event)
  exact (congrArg (receiptEquiv p point).symm same).trans ((receiptEquiv p point).symm_apply_apply _)

def restrictedSettlementSelector (point : Point original) :
    Option (SettlementEvents originalCompiler.terminalRowSource point) :=
  Option.map (formedSettlementEvent p presentation.terminal point).symm
    (generatedCompiler.terminalRowSource.supportSettlementSource.emit? (pointEquiv p point).2)

theorem restrictedSettlementSelector_eq : presentation.restrictedSettlementSelector =
    fun (point : Point original) => originalCompiler.terminalRowSource.supportSettlementSource.emit? point.2 := by
  funext point
  exact inverse_option (formedSettlementEvent p presentation.terminal point)
    (formedSettlement_emit p presentation.terminal point)

def restrictSettlementSource : LedgerSupportSettlementSourceAt original where
  OccurrenceAt := originalCompiler.terminalRowSource.supportSettlementSource.OccurrenceAt
  emit? := fun {current} event => presentation.restrictedSettlementSelector ⟨current, event⟩
  compile := fun {current} {event} value => presentation.restrictedSettlements ⟨current, event⟩ value

theorem restrictSettlementSource_eq :
    presentation.restrictSettlementSource = originalCompiler.terminalRowSource.supportSettlementSource := by
  unfold restrictSettlementSource
  rw [presentation.restrictedSettlements_eq, presentation.restrictedSettlementSelector_eq]

def restrictTerminalSource : LedgerTerminalRowSourceAt original where
  IncidenceOccurrenceAt := originalCompiler.terminalRowSource.IncidenceOccurrenceAt
  compile := fun {current} {event} {entry} value =>
    ⟨presentation.restrictedTerminalReceipts ⟨⟨current, event⟩, entry⟩ value⟩
  supportSettlementSource := presentation.restrictSettlementSource

theorem restrictTerminalSource_eq : presentation.restrictTerminalSource = originalCompiler.terminalRowSource := by
  unfold restrictTerminalSource
  rw [presentation.restrictedTerminalReceipts_eq, presentation.restrictSettlementSource_eq]

include presentation in
theorem restrictedLineage (context : WriteContext original)
    (value : (Transitions.ofCompiler originalCompiler).Exact context) :
    N.lineageAt context.2.1.1 = N.lineageAt context.2.2.1 := by
  apply n.lineage.injective
  have emitted := (Transitions.ofCompiler generatedCompiler).lineage (writeContextEquiv p context)
    (formedExactMember p presentation.transitions context value)
  have left : n.lineage (N.lineageAt context.2.1.1) = G.lineageAt (p.event context.1 context.2.1).1 :=
    (n.lineage_commutes context.2.1.1).symm.trans
      (congrArg G.lineageAt (p.support_eq context.1 context.2.1).symm)
  exact left.trans (emitted.trans (n.lineage_commutes context.2.2.1))

/-- Old types specify the inverse representation's indices. All data-valued
operations below are reconstructed from generated operations and outputs. -/
def restrictLedgerCompiler : SourceNativeLedgerCompiler original where
  IncidenceTransitionAt := originalCompiler.IncidenceTransitionAt
  ExactTransitionAt := originalCompiler.ExactTransitionAt
  exact_incidence := fun {current} {event} {target} {first} {last} value =>
    presentation.restrictedProject ⟨current, event, target, first, last⟩ value
  exact_lineage := fun {current} {event} {target} {first} {last} value =>
    presentation.restrictedLineage ⟨current, event, target, first, last⟩ value
  writeRowSource := presentation.restrictWriteSource
  terminalRowSource := presentation.restrictTerminalSource
  compile := fun {current} event => (presentation.restore ⟨current, event⟩).1
  compilePatch := fun {current} event =>
    Equiv.cast (congrArg₂
      (fun rows terminal => SourceNativeFiniteLedgerPatchAt original originalCompiler.ExactTransitionAt
        rows terminal (presentation.restore ⟨current, event⟩).1)
      presentation.restrictWriteSource_eq.symm presentation.restrictTerminalSource_eq.symm)
      (presentation.restore ⟨current, event⟩).2

private theorem assembled_restriction_eq (compiler : SourceNativeLedgerCompiler original)
    (project : ∀ context, (Transitions.ofCompiler compiler).Exact context →
      (Transitions.ofCompiler compiler).Incidence (incidenceContext context))
    (project_eq : project = (Transitions.ofCompiler compiler).project)
    (lineage : ∀ context, (Transitions.ofCompiler compiler).Exact context →
      N.lineageAt context.2.1.1 = N.lineageAt context.2.2.1)
    (rows : LedgerWriteRowSourceAt original compiler.ExactTransitionAt)
    (rows_eq : rows = compiler.writeRowSource)
    (terminal : LedgerTerminalRowSourceAt original)
    (terminal_eq : terminal = compiler.terminalRowSource)
    (values : (point : Point original) → FullOutput (Transitions.ofCompiler compiler)
      compiler.writeRowSource compiler.terminalRowSource point)
    (values_eq : values = compilerOutput compiler) :
    (show SourceNativeLedgerCompiler original from {
      IncidenceTransitionAt := compiler.IncidenceTransitionAt
      ExactTransitionAt := compiler.ExactTransitionAt
      exact_incidence := fun {current} {event} {target} {first} {last} value =>
        project ⟨current, event, target, first, last⟩ value
      exact_lineage := fun {current} {event} {target} {first} {last} value =>
        lineage ⟨current, event, target, first, last⟩ value
      writeRowSource := rows
      terminalRowSource := terminal
      compile := fun {current} event => (values ⟨current, event⟩).1
      compilePatch := fun {current} event =>
        Equiv.cast (congrArg₂
          (fun r t => SourceNativeFiniteLedgerPatchAt original compiler.ExactTransitionAt
            r t (values ⟨current, event⟩).1) rows_eq.symm terminal_eq.symm)
          (values ⟨current, event⟩).2 }) = compiler := by
  cases project_eq
  cases rows_eq
  cases terminal_eq
  cases values_eq
  rfl

theorem restrictLedgerCompiler_eq : presentation.restrictLedgerCompiler = originalCompiler :=
  assembled_restriction_eq originalCompiler presentation.restrictedProject presentation.restrictedProject_eq
    presentation.restrictedLineage presentation.restrictWriteSource presentation.restrictWriteSource_eq
    presentation.restrictTerminalSource presentation.restrictTerminalSource_eq
    presentation.restore (funext presentation.restore_eq)

end CompilerPresentation
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
