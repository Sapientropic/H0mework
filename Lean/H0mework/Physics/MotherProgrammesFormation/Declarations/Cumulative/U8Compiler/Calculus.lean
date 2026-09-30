import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.HeaderOrigin

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork.{0}} {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7}

def calculusAt (header : MotherInquiryU7Header.Header N) (same : header.1 = U7) :
    U7ObstructionEvolutionCalculus N U7 :=
  Eq.mp (congrArg (U7ObstructionEvolutionCalculus N) same) header.2

theorem calculusAt_eq (header : MotherInquiryU7Header.Header N) (same : header = ⟨U7, calculus⟩) :
    calculusAt header (congrArg Sigma.fst same) = calculus := by
  cases same
  rfl

/-- Read the face's own entire calculus from its actual source material.
The original U7 type is only the inverse dependent index. -/
def readCalculus {rank : Ordinal.{0}} (origin : MotherInquirySource.HeaderOrigin (rank := rank) U7 calculus) :
    U7ObstructionEvolutionCalculus N U7 :=
  calculusAt origin.read (congrArg Sigma.fst origin.read_eq)

theorem readCalculus_eq {rank : Ordinal.{0}} (origin : MotherInquirySource.HeaderOrigin (rank := rank) U7 calculus) :
    readCalculus origin = calculus := calculusAt_eq origin.read origin.read_eq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
