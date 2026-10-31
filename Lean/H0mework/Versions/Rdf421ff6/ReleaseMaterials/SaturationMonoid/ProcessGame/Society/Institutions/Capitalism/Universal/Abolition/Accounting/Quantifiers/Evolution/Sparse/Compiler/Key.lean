import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Occurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Key

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (code : Code N)

def initialVisit : SourceNativeTemporalVisitAt (livingRoot code).toAuthoritativeRoot.toLedgerRoot :=
  .finite (livingRoot code).toAuthoritativeRoot.toRoot.initialVisit

private def ImageKey {current : code.Current}
    (entry : OpenResponsibilityAt N (code.support current)) (expected : N.Responsibility)
    (image : SourceNativeLedgerEvolutionAt (source code) (emitted code current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emitted code current) image,
    (actual.ledgerEvolution.destination entry).1.1 = expected

theorem canonical_key (current : code.Current)
    (entry : OpenResponsibilityAt N (code.support current)) (expected : N.Responsibility)
    (key : ((code.evolution current code.emission).destination entry).1.1 = expected) :
    ((livingRoot code).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (next_eq code current) entry).1 = expected := by
  have actualKey : ImageKey code entry expected ((ledgerCompiler code).compile (emitted code current)) := by
    dsimp only [ledgerCompiler,sourcePacket,emitted,represented]
    split <;> intro actual <;>
      change ((patch code current code.emission).toLedgerWriteEvolution.destination entry).1.1 = expected
    all_goals rw [patch_is_the_complete_original_transport]; exact key
  exact Abolition.Accounting.Root.Compiler.canonical_key
    (livingRoot code).toAuthoritativeRoot.toLedgerRoot current (code.next current)
    (next_eq code current) (successor code current) entry expected (actualKey _)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler
