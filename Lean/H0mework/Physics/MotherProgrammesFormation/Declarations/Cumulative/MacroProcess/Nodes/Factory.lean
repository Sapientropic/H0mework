import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.CompleteInquiry.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {rank : Ordinal.{0}} (header : RootInquiryStatePresentation.{0})
    (query : header.Query ↪ MotherArenaHigher.Base rank)

abbrev Selection := Unit ⊕ header.Query

def selectionCode : Selection header ↪ MotherArenaHigher.Base rank :=
  MotherArenaObligation.sumEmbedding (MotherActionTranslation.unitAddress rank) query

def nodeAt : Selection header → RootInquiryProcessNode
  | .inl _ => .active header
  | .inr question => .answered header question

/-- The active/answered tag and complete prior query are source data. Both
constructors retain the entire already formed inquiry presentation. -/
def form (material : MotherArenaHigher.Material rank) : Option RootInquiryProcessNode :=
  (MotherArenaReceipts.NativeSection.form (MotherActionTranslation.unitAddress rank)
    (fun _ => selectionCode header query) material).map (fun selected => nodeAt header (selected ()))

theorem every_selection (selection : Selection header) :
    ∃ material : MotherArenaHigher.Material rank, form header query material = some (nodeAt header selection) := by
  obtain ⟨material, formed⟩ := MotherArenaReceipts.NativeSection.every_section
    (MotherActionTranslation.unitAddress rank) (fun _ => selectionCode header query) (fun _ => selection)
  exact ⟨material, by rw [form, formed]; rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
