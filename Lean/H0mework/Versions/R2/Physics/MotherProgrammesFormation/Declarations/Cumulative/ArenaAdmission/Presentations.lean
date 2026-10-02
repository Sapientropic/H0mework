import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Sources
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Presentations

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork MotherObligationOrigin MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution
open scoped Classical
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {I : Type} {A C : I → Type} (index : I ↪ MotherArenaHigher.Base rank) (left : ∀ i, A i ↪ MotherArenaHigher.Base rank) (right : ∀ i, C i ↪ MotherArenaHigher.Base rank)

def formPresentationSection (material : M) : Option ((i : I) → ConstructivePresentation (A i) (C i)) :=
  (MotherArenaReceipts.NativeSection.form (MotherArenaObligation.sigmaEmbedding index left) (fun value => right value.1) material).bind (fun forward =>
    if bijective : ∀ i, Function.Bijective (fun value : A i => forward ⟨i, value⟩) then
      some (fun i => presentationFromEquiv (Equiv.ofBijective (fun value => forward ⟨i, value⟩) (bijective i)))
    else none)

/-- The inverse program is uniquely determined by the forward program and
the original inverse laws. The complete native presentation still recovers. -/
theorem every_presentation_section (original : (i : I) → ConstructivePresentation (A i) (C i)) :
    ∃ material : M, formPresentationSection index left right material = some original := by
  obtain ⟨material, formed⟩ := MotherArenaReceipts.NativeSection.every_section (MotherArenaObligation.sigmaEmbedding index left) (fun value => right value.1)
    (fun value => (original value.1).forward value.2)
  have bijective : ∀ i, Function.Bijective (fun value : A i => (original i).forward value) := fun i => presentation_bijective (original i)
  refine ⟨material, ?_⟩
  simp only [formPresentationSection, formed, Option.bind_some, dif_pos bijective]
  exact congrArg some (funext fun i => presentationFromForward_recovers (original i))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
