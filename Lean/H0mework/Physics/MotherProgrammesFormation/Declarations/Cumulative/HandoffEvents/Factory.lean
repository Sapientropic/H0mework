import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffEvents
open MotherArenaNetwork
noncomputable section
variable {rank : Ordinal.{0}}

abbrev Context (base : MotherArenaHigher.Material rank) :=
  {code : MotherArenaHigher.Base rank // bit base 0 code}

abbrev Event (base : MotherArenaHigher.Material rank) (context : Context base) :=
  {code : MotherArenaHigher.Base rank // r2 base 1 context.val code}

abbrev Point (base : MotherArenaHigher.Material rank) := Σ context, Event base context

def pointAddress (base : MotherArenaHigher.Material rank) : Point base ↪ MotherArenaHigher.Base rank :=
  MotherArenaObligation.sigmaEmbedding ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)

abbrev Value (rank : Ordinal.{0}) :=
  Σ base : MotherArenaHigher.Material rank, (context : Context base) → Event base context

/-- Complete context and event carriers come from the base graph; the
selected event is a separately formed total section of those exact fibres. -/
def formParts (base selection : MotherArenaHigher.Material rank) : Option (Value rank) :=
  (MotherArenaReceipts.NativeSection.form
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : Context base ↪ MotherArenaHigher.Base rank)
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) selection).map (fun emit => ⟨base, emit⟩)

def formEvents (material : MotherArenaHigher.Material rank) : Option (Value rank) :=
  let parts := MotherArenaHigher.split rank material
  formParts parts.1 parts.2

theorem every_emit (base : MotherArenaHigher.Material rank)
    (emit : (context : Context base) → Event base context) :
    ∃ material : MotherArenaHigher.Material rank, formEvents material = some ⟨base, emit⟩ := by
  obtain ⟨selection, formed⟩ := MotherArenaReceipts.NativeSection.every_section
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : Context base ↪ MotherArenaHigher.Base rank)
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) emit
  refine ⟨MotherArenaHigher.pack rank (base, selection), ?_⟩
  unfold formEvents
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [formParts, formed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHandoffEvents
