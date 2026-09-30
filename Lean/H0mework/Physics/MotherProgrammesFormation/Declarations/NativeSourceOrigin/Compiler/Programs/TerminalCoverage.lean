import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Terminal

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
open MotherNetworkFactory MotherFullCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Classical
noncomputable section

abbrev RowEvents {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) (context : RowContext source) :=
  rows.IncidenceOccurrenceAt context.1.2 context.2

abbrev SettlementEvents {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) (point : Point source) := rows.supportSettlementSource.OccurrenceAt point.2

structure TerminalEncoding {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (rows : LedgerTerminalRowSourceAt source) where
  row : Sigma (RowEvents rows) ↪ B
  settlement : Sigma (SettlementEvents rows) ↪ B

structure TerminalPresentation {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (old generated : LedgerTerminalRowSourceAt source) where
  row : ∀ context, RowEvents old context ≃ RowEvents generated context
  settlement : ∀ point, SettlementEvents old point ≃ SettlementEvents generated point
  row_compile : ∀ context event, generated.compile (row context event) = old.compile event
  settlement_compile : ∀ point event, generated.supportSettlementSource.compile (settlement point event) =
    old.supportSettlementSource.compile event
  settlement_emit : ∀ point, Option.map (settlement point) (old.supportSettlementSource.emit? point.2) =
    generated.supportSettlementSource.emit? point.2

namespace TerminalEncoding
variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (coordinates : Coordinates source) (ledgerCoordinates : LedgerCoordinates N)
    (rows : LedgerTerminalRowSourceAt source) (encode : TerminalEncoding rows)

def graph (tag : Nat) (code : B) : Prop :=
  let pair := MotherHigherLawFamily.unpair code
  let tail := MotherHigherLawFamily.unpair pair.2
  match tag with
  | 0 => ∃ context event, rowContextEmbedding coordinates ledgerCoordinates context = pair.1 ∧
      encode.row ⟨context, event⟩ = pair.2
  | 1 => ∃ point event, coordinates.occurrence point = pair.1 ∧ encode.settlement ⟨point, event⟩ = pair.2
  | 2 => ∃ context event, rowContextEmbedding coordinates ledgerCoordinates context = pair.1 ∧
      encode.row ⟨context, event⟩ = tail.1 ∧
      ledgerCoordinates.settlement context.1.2.1 (rows.compile event).receipt = tail.2
  | 3 => ∃ point event, coordinates.occurrence point = pair.1 ∧ encode.settlement ⟨point, event⟩ = tail.1 ∧
      ledgerCoordinates.settlement point.2.1 (rows.supportSettlementSource.compile event) = tail.2
  | 4 => ∃ point event, coordinates.occurrence point = pair.1 ∧ encode.settlement ⟨point, event⟩ = pair.2 ∧
      rows.supportSettlementSource.emit? point.2 = some event
  | _ => False

def reader (code : B) (tag : Nat) : ℝ := if graph coordinates ledgerCoordinates rows encode tag code then 0 else 1

theorem reader_bit {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (tag : Nat) (code : B) : bit material tag code ↔ graph coordinates ledgerCoordinates rows encode tag code := by
  by_cases seen : graph coordinates ledgerCoordinates rows encode tag code <;>
    simp only [bit, hm, reader, seen, if_true, if_false, one_ne_zero, iff_self]

def rowEquiv {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (context : RowContext source) : RowEvents rows context ≃ TerminalEvent coordinates ledgerCoordinates material context :=
  MotherNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk context).trans encode.row)
    (fun address => r2 material 0 (rowContextEmbedding coordinates ledgerCoordinates context) address) (by
      intro address
      rw [r2, reader_bit coordinates ledgerCoordinates rows encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      constructor
      · rintro ⟨other, event, same, valueEq⟩
        have same := (rowContextEmbedding coordinates ledgerCoordinates).injective same
        cases same
        exact ⟨event, valueEq⟩
      · rintro ⟨event, valueEq⟩
        exact ⟨context, event, rfl, valueEq⟩)

def settlementEquiv {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (point : Point source) : SettlementEvents rows point ≃ SettlementEvent coordinates material point :=
  MotherNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk point).trans encode.settlement)
    (fun address => r2 material 1 (coordinates.occurrence point) address) (by
      intro address
      rw [r2, reader_bit coordinates ledgerCoordinates rows encode hm]
      simp only [graph, MotherHigherLawFamily.unpair_pair]
      constructor
      · rintro ⟨other, event, same, valueEq⟩
        have same := coordinates.occurrence.injective same
        cases same
        exact ⟨event, valueEq⟩
      · rintro ⟨event, valueEq⟩
        exact ⟨point, event, rfl, valueEq⟩)

theorem row_graph {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (context : RowContext source) (event : RowEvents rows context)
    (receipt : N.DispositionAt context.1.2.1 .supportSettlement) :
    r3 material 2 (rowContextEmbedding coordinates ledgerCoordinates context)
      (rowEquiv coordinates ledgerCoordinates rows encode hm context event).val
      (ledgerCoordinates.settlement context.1.2.1 receipt) ↔ receipt = (rows.compile event).receipt := by
  rw [r3, reader_bit coordinates ledgerCoordinates rows encode hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, e, contextEq, eventEq, receiptEq⟩
    have same := (rowContextEmbedding coordinates ledgerCoordinates).injective contextEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := RowEvents rows) context).trans encode.row).injective eventEq
    cases same
    exact ((ledgerCoordinates.settlement context.1.2.1).injective receiptEq).symm
  · intro same
    cases same
    exact ⟨context, event, rfl, rfl, rfl⟩

theorem settlement_graph {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (point : Point source) (event : SettlementEvents rows point)
    (receipt : N.DispositionAt point.2.1 .supportSettlement) :
    r3 material 3 (coordinates.occurrence point)
      (settlementEquiv coordinates ledgerCoordinates rows encode hm point event).val
      (ledgerCoordinates.settlement point.2.1 receipt) ↔ receipt = rows.supportSettlementSource.compile event := by
  rw [r3, reader_bit coordinates ledgerCoordinates rows encode hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, e, pointEq, eventEq, receiptEq⟩
    have same := coordinates.occurrence.injective pointEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := SettlementEvents rows) point).trans encode.settlement).injective eventEq
    cases same
    exact ((ledgerCoordinates.settlement point.2.1).injective receiptEq).symm
  · intro same
    cases same
    exact ⟨point, event, rfl, rfl, rfl⟩

theorem selected_graph {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode)
    (point : Point source) (event : SettlementEvents rows point) :
    r2 material 4 (coordinates.occurrence point) (settlementEquiv coordinates ledgerCoordinates rows encode hm point event).val ↔
      rows.supportSettlementSource.emit? point.2 = some event := by
  rw [r2, reader_bit coordinates ledgerCoordinates rows encode hm]
  simp only [graph, MotherHigherLawFamily.unpair_pair]
  constructor
  · rintro ⟨other, e, pointEq, eventEq, selected⟩
    have same := coordinates.occurrence.injective pointEq
    cases same
    have same := ((Function.Embedding.sigmaMk (β := SettlementEvents rows) point).trans encode.settlement).injective eventEq
    cases same
    exact selected
  · intro selected
    exact ⟨point, event, rfl, rfl, selected⟩

theorem checked {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode) :
    TerminalCheck coordinates ledgerCoordinates material where
  row := by
    intro context event
    obtain ⟨event, rfl⟩ := (rowEquiv coordinates ledgerCoordinates rows encode hm context).surjective event
    exact ⟨_, (row_graph coordinates ledgerCoordinates rows encode hm context event _).mpr rfl,
      fun receipt selected => (row_graph coordinates ledgerCoordinates rows encode hm context event receipt).mp selected⟩
  settlement := by
    intro point event
    obtain ⟨event, rfl⟩ := (settlementEquiv coordinates ledgerCoordinates rows encode hm point).surjective event
    exact ⟨_, (settlement_graph coordinates ledgerCoordinates rows encode hm point event _).mpr rfl,
      fun receipt selected => (settlement_graph coordinates ledgerCoordinates rows encode hm point event receipt).mp selected⟩
  selected_unique := by
    intro point left right hl hr
    obtain ⟨left, rfl⟩ := (settlementEquiv coordinates ledgerCoordinates rows encode hm point).surjective left
    obtain ⟨right, rfl⟩ := (settlementEquiv coordinates ledgerCoordinates rows encode hm point).surjective right
    exact congrArg (settlementEquiv coordinates ledgerCoordinates rows encode hm point)
      (Option.some.inj (((selected_graph coordinates ledgerCoordinates rows encode hm point left).mp hl).symm.trans
        ((selected_graph coordinates ledgerCoordinates rows encode hm point right).mp hr)))

theorem emit_eq {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode) (point : Point source) :
    Option.map (settlementEquiv coordinates ledgerCoordinates rows encode hm point) (rows.supportSettlementSource.emit? point.2) =
      selected? coordinates material point := by
  cases selected : rows.supportSettlementSource.emit? point.2 with
  | none =>
      have absent : selected? coordinates material point = none := by
        cases generated : selected? coordinates material point with
        | none => rfl
        | some event =>
            obtain ⟨event, rfl⟩ := (settlementEquiv coordinates ledgerCoordinates rows encode hm point).surjective event
            have wrong := (selected_graph coordinates ledgerCoordinates rows encode hm point event).mp
              (selected_of_emitted coordinates material point _ generated)
            rw [selected] at wrong
            cases wrong
      exact absent.symm
  | some event =>
      exact (emitted_of_selected coordinates ledgerCoordinates material (checked coordinates ledgerCoordinates rows encode hm)
        point _ ((selected_graph coordinates ledgerCoordinates rows encode hm point event).mpr selected)).symm

def presentation {material : M}
    (hm : MotherHigherLawFormation.read material = reader coordinates ledgerCoordinates rows encode) :
    TerminalPresentation rows (terminalRows coordinates ledgerCoordinates material (checked coordinates ledgerCoordinates rows encode hm)) where
  row := rowEquiv coordinates ledgerCoordinates rows encode hm
  settlement := settlementEquiv coordinates ledgerCoordinates rows encode hm
  row_compile := by
    intro context event
    apply congrArg LedgerEntryTerminalAt.mk
    exact (row_graph coordinates ledgerCoordinates rows encode hm context event _).mp
      (Classical.choose_spec ((checked coordinates ledgerCoordinates rows encode hm).row context _)).1
  settlement_compile := fun point event =>
    (settlement_graph coordinates ledgerCoordinates rows encode hm point event _).mp
      (Classical.choose_spec ((checked coordinates ledgerCoordinates rows encode hm).settlement point _)).1
  settlement_emit := emit_eq coordinates ledgerCoordinates rows encode hm

end TerminalEncoding
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourcePrograms
