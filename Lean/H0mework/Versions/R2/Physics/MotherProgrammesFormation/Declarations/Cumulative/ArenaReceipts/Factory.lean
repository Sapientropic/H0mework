import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Events
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Factory

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherObligationOrigin MotherFullCompiler MotherSourcePrograms MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem law_projection_formed (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) :
    MotherArenaProjection.formProjection ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold MotherArenaObligation.formLaw MotherArenaObligation.formLawParts at formed
  dsimp only at formed
  obtain ⟨projection, projectionFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨R, vocabularyFormed, selected⟩ := Option.pbind_eq_some_iff.mp selected
  obtain ⟨law, lawFormed, same⟩ := Option.map_eq_some_iff.mp selected
  exact projectionFormed.trans (congrArg (fun value : LawValue => some value.1) same)

def lawPoints (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) :
    MotherArenaCompiler.Coordinates (rank := rank) value.1.1.2.2.source.source :=
  MotherArenaProjection.rootCoordinates ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1 value.1.1
    (MotherArenaObligation.projection_root_formed _ value.1 (law_projection_formed material value formed))

def lawWorld (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) : MotherArenaCompiler.LedgerCoordinates (rank := rank) value.1.1.1 :=
  (MotherArenaObligation.rootWorldCoordinates ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).1).1 value.1.1
    (MotherArenaObligation.projection_root_formed _ value.1 (law_projection_formed material value formed))).toLedgerCoordinates

def formCompilerParts (parent material : M) : Option CompilerValue :=
  (MotherArenaObligation.formLaw parent).pbind (fun value formed =>
    (formCertificationSection (coordinatesOfLaw parent value formed) (lawWorld parent value formed) (lawPoints parent value formed)
      (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) material).map (fun certificates => ⟨value, compilerOf value certificates⟩))

/-- The public factory receives only one mother material. Every original
compiled branch keeps its full native restructuring certification, including
the selected split/merge receipts and their whole anchor functions. -/
def formRestructuringCompiler (material : M) : Option CompilerValue :=
  let parts := (MotherArenaHigher.split rank) material
  formCompilerParts parts.1 parts.2

def formRestructuringSource (material : M) :
    Option (Σ N : WorldRelationNetwork.{0}, Σ V : ConstructiveRoot.Vocabulary.{0}, SourceNativeRestructuringLedgerSource N V) :=
  (formRestructuringCompiler material).map (fun value => ⟨value.1.1.1.1, value.1.1.1.2.1, sourceOf value⟩)

theorem every_compiler_on_formed_law (parent : M) (value : LawValue) (formed : MotherArenaObligation.formLaw parent = some value)
    (certificates : LawCertification value) :
    ∃ material : M, formRestructuringCompiler material = some ⟨value, compilerOf value certificates⟩ ∧
      formRestructuringSource material = some ⟨value.1.1.1, value.1.1.2.1, sourceOf ⟨value, compilerOf value certificates⟩⟩ := by
  obtain ⟨material, allCertificates⟩ := every_certification_section (coordinatesOfLaw parent value formed)
    (lawWorld parent value formed) (lawPoints parent value formed)
    (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) certificates
  have compilerFormed : formRestructuringCompiler ((MotherArenaHigher.pack rank) (parent, material)) =
      some ⟨value, compilerOf value certificates⟩ := by
    simp only [formRestructuringCompiler, MotherArenaHigher.split_pack, formCompilerParts, formed, Option.pbind_some]
    change (formCertificationSection (coordinatesOfLaw parent value formed) (lawWorld parent value formed)
      (lawPoints parent value formed) (fun point => value.1.1.2.2.source.ledgerCompiler.compile point.2) material).map
        (fun certificates => (⟨value, compilerOf value certificates⟩ : CompilerValue)) = _
    rw [allCertificates]
    rfl
  refine ⟨(MotherArenaHigher.pack rank) (parent, material), compilerFormed, ?_⟩
  simp only [formRestructuringSource, compilerFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
