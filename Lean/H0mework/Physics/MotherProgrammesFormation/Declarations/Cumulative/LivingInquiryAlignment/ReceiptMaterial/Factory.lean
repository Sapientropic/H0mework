import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Higher

/-! Complete answer/receipt fibres and one actual dependent value are read
from material. The factory has no Answer, Receipt, selected value or decoder
argument; the original field types enter only its later inverse consumer. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
open scoped Classical
noncomputable section
universe u
variable {rank : Ordinal.{u}}

local notation "Base" => MotherReceiptHigher.Base rank
local notation "Material" => MotherReceiptHigher.Material rank

def bit (material : Material) (tag : Nat) (address : Base) : Prop :=
  MotherReceiptHigher.read rank material address tag = 0

def relation (material : Material) (tag : Nat) (first last : Base) : Prop :=
  bit material tag (MotherReceiptHigher.pair rank (first, last))

abbrev Answer (material : Material) := {address : Base // bit material 0 address}
abbrev Receipt (material : Material) (answer : Answer material) :=
  {address : Base // relation material 1 answer.val address}
abbrev Point (material : Material) := Σ answer, Receipt material answer

def pointAddress (material : Material) : Point material ↪ Base where
  toFun := fun point => MotherReceiptHigher.pair rank (point.1.val, point.2.val)
  inj' := by
    rintro ⟨first, receipt⟩ ⟨last, other⟩ same
    have pairSame := congrArg (MotherReceiptHigher.unpair rank) same
    rw [MotherReceiptHigher.unpair_pair, MotherReceiptHigher.unpair_pair] at pairSame
    have answerSame : first = last := Subtype.ext (congrArg Prod.fst pairSame)
    cases answerSame
    exact congrArg (Sigma.mk first) (Subtype.ext (congrArg Prod.snd pairSame))

abbrev Value (rank : Ordinal.{u}) := Σ material : MotherReceiptHigher.Material rank, Point material

def formParts (base selection : Material) : Option (Value rank) :=
  if existsUnique : ∃! point : Point base, bit selection 0 (pointAddress base point) then
    some ⟨base, Classical.choose existsUnique.exists⟩
  else none

def form (material : Material) : Option (Value rank) :=
  let parts := MotherReceiptHigher.split rank material
  formParts parts.1 parts.2

theorem every_selected (base : Material) (point : Point base) :
    ∃ material : Material, form material = some ⟨base, point⟩ := by
  obtain ⟨selection, readback⟩ := MotherReceiptHigher.read_surjective rank
    (fun address _ => if address = pointAddress base point then 0 else 1)
  have selected (other : Point base) :
      bit selection 0 (pointAddress base other) ↔ other = point := by
    simp only [bit, readback]
    by_cases same : other = point
    · subst other
      simp only [if_true, iff_self]
    · have different := fun h => same ((pointAddress base).injective h)
      simp only [if_neg different, one_ne_zero, same, iff_self]
  have unique : ∃! other : Point base, bit selection 0 (pointAddress base other) := by
    refine ⟨point, (selected point).mpr rfl, ?_⟩
    intro other holds
    exact (selected other).mp holds
  have recovered : Classical.choose unique.exists = point :=
    (selected _).mp (Classical.choose_spec unique.exists)
  refine ⟨MotherReceiptHigher.pack rank (base, selection), ?_⟩
  unfold form
  rw [MotherReceiptHigher.split_pack]
  dsimp only
  rw [formParts, dif_pos unique, recovered]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptPayload
