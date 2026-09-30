import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Write

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private theorem cast_discharge_receipt (G : WorldRelationNetwork.{0}) {s t : G.Support}
    (same : s = t) (whole : LedgerTerminalEvolutionAt G ⟨s⟩) (entry : OpenResponsibilityAt G s) :
    (((Equiv.cast (congrArg (fun support => LedgerTerminalEvolutionAt G ⟨support⟩) same)) whole).discharge
      ((Equiv.cast (congrArg (OpenResponsibilityAt G) same)) entry)).receipt =
      (Equiv.cast (congrArg (fun support => G.DispositionAt support .supportSettlement) same))
        (whole.discharge entry).receipt := by
  cases same
  rfl

private theorem terminal_ext {N : WorldRelationNetwork.{0}} {ledger : CompleteLiveLedgerAt N}
    {left right : LedgerTerminalEvolutionAt N ledger}
    (same : ∀ a, left.discharge a = right.discharge a) : left = right := by
  have same := funext same
  cases left; cases right; cases same; rfl

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def terminalRowEquiv (point : Point original) (entry : OpenResponsibilityAt N point.2.1) :
    LedgerEntryTerminalAt N entry ≃ LedgerEntryTerminalAt G (sourceEntryEquiv p point entry) where
  toFun := fun value => ⟨receiptEquiv p point value.receipt⟩
  invFun := fun value => ⟨(receiptEquiv p point).symm value.receipt⟩
  left_inv := fun value => by cases value; simp only [Equiv.symm_apply_apply]
  right_inv := fun value => by cases value; simp only [Equiv.apply_symm_apply]

def terminalEquiv (point : Point original) :
    LedgerTerminalEvolutionAt N ⟨point.2.1⟩ ≃ LedgerTerminalEvolutionAt G ⟨(pointEquiv p point).2.1⟩ :=
  (n.wholeTerminalEquiv point.2.1).trans (Equiv.cast
    (congrArg (fun support => LedgerTerminalEvolutionAt G ⟨support⟩) (p.support_eq point.1 point.2).symm))

theorem terminal_discharge (point : Point original) (whole : LedgerTerminalEvolutionAt N ⟨point.2.1⟩)
    (entry : OpenResponsibilityAt N point.2.1) :
    (terminalEquiv p point whole).discharge (sourceEntryEquiv p point entry) =
      terminalRowEquiv p point entry (whole.discharge entry) := by
  have h := (cast_discharge_receipt G (p.support_eq point.1 point.2).symm
    (n.wholeTerminalEquiv point.2.1 whole) (n.ledger point.2.1 entry)).trans
      (congrArg ((Equiv.cast (congrArg (fun support => G.DispositionAt support .supportSettlement)
        (p.support_eq point.1 point.2).symm))) (congrArg LedgerEntryTerminalAt.receipt (n.whole_discharge whole entry)))
  exact congrArg (fun receipt => (⟨receipt⟩ : LedgerEntryTerminalAt G (sourceEntryEquiv p point entry))) h

variable {old : LedgerTerminalRowSourceAt original} {output : LedgerTerminalRowSourceAt generated}
    (s : TerminalPresentation (transportedTerminal p old) output)

def finiteTerminal (point : Point original) (patch : FiniteGeneratedLedgerTerminalPatchAt old point.2) :
    FiniteGeneratedLedgerTerminalPatchAt output (pointEquiv p point).2 where
  size := patch.size
  entryAt := fun i => sourceEntryEquiv p point (patch.entryAt i)
  rowAt := fun i => formedRowEquiv p s ⟨point, patch.entryAt i⟩ (patch.rowAt i)
  entryIndex := fun entry => patch.entryIndex ((sourceEntryEquiv p point).symm entry)
  entry_sound := fun entry => (congrArg (sourceEntryEquiv p point)
    (patch.entry_sound ((sourceEntryEquiv p point).symm entry))).trans ((sourceEntryEquiv p point).apply_symm_apply entry)

def terminalPatch (point : Point original) (patch : SourceGeneratedLedgerTerminalPatchAt old point.2) :
    SourceGeneratedLedgerTerminalPatchAt output (pointEquiv p point).2 := by
  cases patch with
  | finite patch => exact .finite (finiteTerminal p s point patch)
  | supportSettlement value => exact .supportSettlement (formedSettlement p s point value)

theorem finiteTerminal_fold (point : Point original) (patch : FiniteGeneratedLedgerTerminalPatchAt old point.2) :
    (finiteTerminal p s point patch).toLedgerTerminalEvolution = terminalEquiv p point patch.toLedgerTerminalEvolution := by
  apply terminal_ext
  intro entry
  obtain ⟨entry, rfl⟩ := (sourceEntryEquiv p point).surjective entry
  have same := patch.entry_sound entry
  generalize indexEq : patch.entryIndex entry = index at same
  cases same
  have newIndex : (finiteTerminal p s point patch).entryIndex (sourceEntryEquiv p point (patch.entryAt index)) = index :=
    (congrArg patch.entryIndex ((sourceEntryEquiv p point).symm_apply_apply (patch.entryAt index))).trans indexEq
  have left := MotherNetworkOrigin.terminal_discharge_at (finiteTerminal p s point patch)
    (sourceEntryEquiv p point (patch.entryAt index)) index newIndex rfl
  have right := congrArg (terminalRowEquiv p point (patch.entryAt index))
    (MotherNetworkOrigin.terminal_discharge_at patch (patch.entryAt index) index indexEq rfl)
  have middle := congrArg (fun receipt => (⟨receipt⟩ : LedgerEntryTerminalAt G (sourceEntryEquiv p point (patch.entryAt index))))
    (formedRow_receipt p s ⟨point, patch.entryAt index⟩ (patch.rowAt index))
  exact (left.trans (middle.trans right.symm)).trans (terminal_discharge p point patch.toLedgerTerminalEvolution (patch.entryAt index)).symm

theorem terminalPatch_fold (point : Point original) (patch : SourceGeneratedLedgerTerminalPatchAt old point.2) :
    (terminalPatch p s point patch).toLedgerTerminalEvolution = terminalEquiv p point patch.toLedgerTerminalEvolution := by
  cases patch with
  | finite patch => exact finiteTerminal_fold p s point patch
  | supportSettlement value =>
      apply terminal_ext
      intro entry
      obtain ⟨entry, rfl⟩ := (sourceEntryEquiv p point).surjective entry
      exact (congrArg (fun receipt => (⟨receipt⟩ : LedgerEntryTerminalAt G (sourceEntryEquiv p point entry)))
        (formedSettlement_receipt p s point value)).trans
        (terminal_discharge p point value.toLedgerTerminalEvolution entry).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
