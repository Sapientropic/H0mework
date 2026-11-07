import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Key

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

private def DestinationExact (current : code.Current)
    (image : SourceNativeLedgerEvolutionAt (source code) (emitted code current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emitted code current) image,
    HEq actual.ledgerEvolution.destination (code.evolution current code.emission).destination

private def OriginExact (current : code.Current)
    (image : SourceNativeLedgerEvolutionAt (source code) (emitted code current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emitted code current) image,
    HEq actual.ledgerEvolution.origin (code.evolution current code.emission).origin

theorem successor_destination (current : code.Current) :
    HEq (successor code current).ledgerEvolution.destination (code.evolution current code.emission).destination := by
  have same : DestinationExact code current ((ledgerCompiler code).compile (emitted code current)) := by
    dsimp only [ledgerCompiler,sourcePacket,emitted,represented]
    split <;> intro actual <;> exact heq_of_eq
      (congrArg LedgerWriteEvolutionAt.destination (patch_is_the_complete_original_transport code current code.emission))
  exact same _

theorem successor_origin (current : code.Current) :
    HEq (successor code current).ledgerEvolution.origin (code.evolution current code.emission).origin := by
  have same : OriginExact code current ((ledgerCompiler code).compile (emitted code current)) := by
    dsimp only [ledgerCompiler,sourcePacket,emitted,represented]
    split <;> intro actual <;> exact heq_of_eq
      (congrArg LedgerWriteEvolutionAt.origin (patch_is_the_complete_original_transport code current code.emission))
  exact same _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
