import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Header

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Header
open MotherInquiryU7Demand
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}}

/-- Full source operands for both header records, before any selection or
emitted trajectory is taken. This total is small and used only in coverage. -/
abbrev AddressTotal (header : Header N) :=
  ObstructionPoint N ⊕ MotherInquiryU7Demand.Total header.1 ⊕
    MotherInquiryU7Events.Total header.1 header.2.source ⊕ (Σ support, OpenResponsibilityAt N support) ⊕
    MotherInquiryU7.EventTotal header.2.source ⊕ (Σ point, MotherInquiryU7.DispositionAt header.2.source point)

private def left {A C B : Type} (code : A ⊕ C ↪ B) : A ↪ B :=
  ⟨fun value => code (.inl value), fun _ _ same => Sum.inl.inj (code.injective same)⟩

private def right {A C B : Type} (code : A ⊕ C ↪ B) : C ↪ B :=
  ⟨fun value => code (.inr value), fun _ _ same => Sum.inr.inj (code.injective same)⟩

def addressesOfTotal {rank : Ordinal.{0}} (header : Header N)
    (shared : AddressTotal header ↪ MotherArenaHigher.Base rank) : Addresses (rank := rank) header where
  obstruction := left shared
  demand := left (right shared)
  event := left (right (right shared))
  entry := left (right (right (right shared)))
  compilerEvent := left (right (right (right (right shared))))
  disposition := right (right (right (right (right shared))))

/-- No address or representation condition remains on the original U7 and
its complete calculus. One sufficient rank pays all three material stages. -/
theorem every_original_header (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) :
    ∃ rank : Ordinal.{0}, ∃ addresses : Addresses (rank := rank) ⟨U7, calculus⟩,
      FormationAt U7 calculus addresses :=
  ⟨MotherArenaHigher.carrierRank (AddressTotal ⟨U7, calculus⟩),
    addressesOfTotal ⟨U7, calculus⟩ (MotherArenaHigher.carrierAddress (AddressTotal ⟨U7, calculus⟩)),
    header_at_rank U7 calculus
      (addressesOfTotal ⟨U7, calculus⟩ (MotherArenaHigher.carrierAddress (AddressTotal ⟨U7, calculus⟩)))⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInquiryU7Header
