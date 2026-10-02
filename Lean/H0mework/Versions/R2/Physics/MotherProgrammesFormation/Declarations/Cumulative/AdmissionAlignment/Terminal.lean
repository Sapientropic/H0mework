import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.CompilationSquare

/-! Full terminal-patch recovery through the existing source presentation.
The original finite rows and every stored selector are recovered. This
transporter supplies an inverse of the actual signed patch map; it does
not identify the new source types with the original source types. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment

open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open MotherPatchInventory MotherFullPatches
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

def terminalDataEquiv {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} (rows : LedgerTerminalRowSourceAt source)
    (point : Point source) :
    FiniteGeneratedLedgerTerminalPatchAt rows point.2 ≃
      (Σ body : TerminalBody rows point, TerminalIndices rows body) where
  toFun := fun value => ⟨terminalBody rows value, terminalIndices rows value⟩
  invFun := fun value => terminalFinite rows value.1 value.2
  left_inv := terminalFinite_original rows
  right_inv := by
    rintro ⟨⟨size, body⟩, indices⟩
    rfl

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : LedgerTerminalRowSourceAt original} {output : LedgerTerminalRowSourceAt generated}
    (s : TerminalPresentation (transportedTerminal p old) output)

def terminalItemEquiv (point : Point original) :
    TerminalItem old point ≃ TerminalItem output (pointEquiv p point) :=
  Equiv.sigmaCongr (sourceEntryEquiv p point) (fun entry => formedRowEvent p s ⟨point, entry⟩)

def terminalBodyEquiv (point : Point original) :
    TerminalBody old point ≃ TerminalBody output (pointEquiv p point) :=
  Equiv.sigmaCongrRight (fun _ => Equiv.piCongrRight (fun _ => terminalItemEquiv p s point))

def terminalIndicesEquiv (point : Point original) (body : TerminalBody old point) :
    TerminalIndices old body ≃ TerminalIndices output (terminalBodyEquiv p s point body) where
  toFun := fun indices entry =>
    ⟨(indices ((sourceEntryEquiv p point).symm entry)).val,
      (congrArg (sourceEntryEquiv p point) (indices ((sourceEntryEquiv p point).symm entry)).property).trans
        ((sourceEntryEquiv p point).apply_symm_apply entry)⟩
  invFun := fun indices entry =>
    ⟨(indices (sourceEntryEquiv p point entry)).val,
      (sourceEntryEquiv p point).injective (indices (sourceEntryEquiv p point entry)).property⟩
  left_inv := by
    intro indices
    funext entry
    apply Subtype.ext
    change (indices ((sourceEntryEquiv p point).symm (sourceEntryEquiv p point entry))).val = _
    rw [Equiv.symm_apply_apply]
  right_inv := by
    intro indices
    funext entry
    apply Subtype.ext
    change (indices (sourceEntryEquiv p point ((sourceEntryEquiv p point).symm entry))).val = _
    rw [Equiv.apply_symm_apply]

def finiteTerminalEquiv (point : Point original) :
    FiniteGeneratedLedgerTerminalPatchAt old point.2 ≃
      FiniteGeneratedLedgerTerminalPatchAt output (pointEquiv p point).2 :=
  (terminalDataEquiv old point).trans
    ((Equiv.sigmaCongr (terminalBodyEquiv p s point) (terminalIndicesEquiv p s point)).trans
      (terminalDataEquiv output (pointEquiv p point)).symm)

theorem finiteTerminalEquiv_apply (point : Point original)
    (patch : FiniteGeneratedLedgerTerminalPatchAt old point.2) :
    finiteTerminalEquiv p s point patch = finiteTerminal p s point patch := rfl

def settlementEquiv (point : Point original) :
    GeneratedLedgerSupportSettlementAt old point.2 ≃
      GeneratedLedgerSupportSettlementAt output (pointEquiv p point).2 where
  toFun := formedSettlement p s point
  invFun := fun value =>
    MotherNetworkOrigin.sealSettlement old point.2 ((formedSettlementEvent p s point).symm value.event) (by
      apply (Equiv.optionCongr (formedSettlementEvent p s point)).injective
      change Option.map (formedSettlementEvent p s point) (old.supportSettlementSource.emit? point.2) =
        Option.map (formedSettlementEvent p s point) (some ((formedSettlementEvent p s point).symm value.event))
      rw [Option.map_some, Equiv.apply_symm_apply]
      exact (formedSettlement_emit p s point).trans value.selected)
  left_inv := fun value => settlementSeal_eq _ value
  right_inv := fun value => settlementSeal_eq _ value

def terminalPatchEquiv (point : Point original) :
    SourceGeneratedLedgerTerminalPatchAt old point.2 ≃
      SourceGeneratedLedgerTerminalPatchAt output (pointEquiv p point).2 where
  toFun := terminalPatch p s point
  invFun := fun patch => match patch with
    | .finite finite => .finite ((finiteTerminalEquiv p s point).symm finite)
    | .supportSettlement value => .supportSettlement ((settlementEquiv p s point).symm value)
  left_inv := by
    intro patch
    cases patch with
    | finite finite =>
        change SourceGeneratedLedgerTerminalPatchAt.finite
          ((finiteTerminalEquiv p s point).symm (finiteTerminal p s point finite)) = .finite finite
        rw [← finiteTerminalEquiv_apply, Equiv.symm_apply_apply]
    | supportSettlement value =>
        exact congrArg SourceGeneratedLedgerTerminalPatchAt.supportSettlement
          ((settlementEquiv p s point).symm_apply_apply value)
  right_inv := by
    intro patch
    cases patch with
    | finite finite =>
        change SourceGeneratedLedgerTerminalPatchAt.finite
          (finiteTerminal p s point ((finiteTerminalEquiv p s point).symm finite)) = .finite finite
        rw [← finiteTerminalEquiv_apply, Equiv.apply_symm_apply]
    | supportSettlement value =>
        exact congrArg SourceGeneratedLedgerTerminalPatchAt.supportSettlement
          ((settlementEquiv p s point).apply_symm_apply value)

theorem terminalPatch_recovers (point : Point original)
    (patch : SourceGeneratedLedgerTerminalPatchAt old point.2) :
    (terminalPatchEquiv p s point).symm (terminalPatch p s point patch) = patch :=
  (terminalPatchEquiv p s point).symm_apply_apply patch

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
