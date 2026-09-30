import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations

/-! Non-surjective translations retain both programs. The backward map on
new coordinates is not reconstructed from a forward injection. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionRetract
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}} {I : Type} {A C : I → Type}
    (index : I ↪ MotherArenaHigher.Base rank)
    (left : ∀ i, A i ↪ MotherArenaHigher.Base rank)
    (right : ∀ i, C i ↪ MotherArenaHigher.Base rank)

local notation "M" => MotherArenaHigher.Material rank

def form (material : M) : Option ((i : I) → ConstructiveRetract (A i) (C i)) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaReceipts.NativeSection.form (MotherArenaObligation.sigmaEmbedding index left)
    (fun point => right point.1) parts.1).bind (fun forward =>
  (MotherArenaReceipts.NativeSection.form (MotherArenaObligation.sigmaEmbedding index right)
    (fun point => left point.1) parts.2).bind (fun backward =>
    if retracts : ∀ i value, backward ⟨i, forward ⟨i, value⟩⟩ = value then
      some (fun i => {
        forward := fun value => forward ⟨i, value⟩
        backward := fun value => backward ⟨i, value⟩
        backward_forward := retracts i })
    else none))

theorem every_retract (original : (i : I) → ConstructiveRetract (A i) (C i)) :
    ∃ material : M, form index left right material = some original := by
  obtain ⟨forwardMaterial, forwardFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (MotherArenaObligation.sigmaEmbedding index left) (fun point => right point.1)
    (fun point => (original point.1).forward point.2)
  obtain ⟨backwardMaterial, backwardFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (MotherArenaObligation.sigmaEmbedding index right) (fun point => left point.1)
    (fun point => (original point.1).backward point.2)
  refine ⟨MotherArenaHigher.pack rank (forwardMaterial, backwardMaterial), ?_⟩
  simp only [form, MotherArenaHigher.split_pack, forwardFormed, Option.bind_some,
    backwardFormed, dif_pos (fun i value => (original i).backward_forward value)]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionRetract
