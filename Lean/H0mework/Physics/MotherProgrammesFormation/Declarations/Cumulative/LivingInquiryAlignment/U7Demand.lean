import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Demand
open MotherArenaNetwork
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {rank : Ordinal.{0}} {N : WorldRelationNetwork.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev ObstructionPoint (N : WorldRelationNetwork.{0}) := Σ support, N.ObstructionAt support
abbrev Total (old : U7ProducerCalculus N) := Σ point : ObstructionPoint N, old.DemandAt point.2

variable (address : ObstructionPoint N ↪ MotherArenaHigher.Base rank)

def Demand (base : M) (point : ObstructionPoint N) : Type :=
  {code : B // r2 base 0 (address point) code}

def assemble (base : M) (generate : ∀ point : ObstructionPoint N, Demand address base point) : U7ProducerCalculus N where
  DemandAt := fun {support} obstruction => Demand address base ⟨support, obstruction⟩
  generateDemand := fun {support} obstruction => generate ⟨support, obstruction⟩

def formParts (base programme : M) : Option (U7ProducerCalculus N) :=
  (MotherArenaReceipts.NativeSection.form address
    (fun point => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : Demand address base point ↪ B)) programme).map
      (assemble address base)

/-- Actual demand fibers and their total generator are both mother-material
outputs. All legal demands are retained, including unselected members. -/
def form (material : M) : Option (U7ProducerCalculus N) :=
  let parts := MotherArenaHigher.split rank material
  formParts address parts.1 parts.2

structure Presentation (old generated : U7ProducerCalculus N) where
  demand : ∀ support (obstruction : N.ObstructionAt support), old.DemandAt obstruction ≃ generated.DemandAt obstruction
  generated_eq : ∀ support (obstruction : N.ObstructionAt support),
    generated.generateDemand obstruction = demand support obstruction (old.generateDemand obstruction)

namespace Presentation

variable {old generated : U7ProducerCalculus N} (p : Presentation old generated)

def restrict : U7ProducerCalculus N where
  DemandAt := old.DemandAt
  generateDemand := fun {support} obstruction => (p.demand support obstruction).symm (generated.generateDemand obstruction)

theorem restrict_eq : p.restrict = old := by
  have same : (fun {support} (obstruction : N.ObstructionAt support) =>
      (p.demand support obstruction).symm (generated.generateDemand obstruction)) = @old.generateDemand := by
    funext support obstruction
    exact (congrArg (p.demand support obstruction).symm (p.generated_eq support obstruction)).trans
      ((p.demand support obstruction).symm_apply_apply _)
  unfold restrict
  rw [same]

end Presentation

theorem every_at_rank (old : U7ProducerCalculus N) (code : Total old ↪ B) :
    ∃ material : M, ∃ generated : U7ProducerCalculus N,
      form address material = some generated ∧ Nonempty (Presentation old generated) := by
  obtain ⟨base, relation⟩ := MotherArenaNetwork.every_binary_graph (rank := rank) 0
    (fun context output => ∃ point : ObstructionPoint N, ∃ demand : old.DemandAt point.2,
      address point = context ∧ code ⟨point, demand⟩ = output)
  have at_fiber (point : ObstructionPoint N) (output : B) :
      r2 base 0 (address point) output ↔ ∃ demand : old.DemandAt point.2, code ⟨point, demand⟩ = output := by
    rw [relation]
    constructor
    · rintro ⟨other, demand, same, selected⟩
      have equal := address.injective same
      cases equal
      exact ⟨demand, selected⟩
    · rintro ⟨demand, selected⟩
      exact ⟨point, demand, rfl, selected⟩
  let fibers : ∀ point : ObstructionPoint N, old.DemandAt point.2 ≃ Demand address base point :=
    fun point => MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk point).trans code)
      (r2 base 0 (address point)) (at_fiber point)
  let generate : ∀ point : ObstructionPoint N, Demand address base point :=
    fun point => fibers point (old.generateDemand point.2)
  obtain ⟨programme, formed⟩ := MotherArenaReceipts.NativeSection.every_section address
    (fun point => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : Demand address base point ↪ B)) generate
  refine ⟨MotherArenaHigher.pack rank (base, programme), assemble address base generate, ?_, ⟨{
    demand := fun support obstruction => fibers ⟨support, obstruction⟩
    generated_eq := fun _ _ => rfl }⟩⟩
  unfold form
  rw [MotherArenaHigher.split_pack]
  dsimp only
  rw [formParts, formed]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Demand
