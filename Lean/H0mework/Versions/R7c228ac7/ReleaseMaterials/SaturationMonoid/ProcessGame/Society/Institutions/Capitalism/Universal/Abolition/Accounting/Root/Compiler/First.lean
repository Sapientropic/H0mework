import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.GeneratedRow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} (F : Flow N)

local notation "root" => livingRoot F
local notation "emit" => emitted F

def initialVisit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot :=
  .finite (root).toAuthoritativeRoot.toRoot.initialVisit

theorem successor_support (current : F.Current) :
    (successor F current).targetOccurrence.1 =
      F.support (F.next current) := by
  have emittedAt := occurrence_eq_emitted F
    (successor F current).targetOccurrence
  exact (congrArg (fun occurrence => occurrence.1) emittedAt).trans
    (congrArg (F.support) (successor_current F current))

private def DestinationExact (current : F.Current)
    (image : SourceNativeLedgerEvolutionAt (source F) (emit current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emit current) image,
    HEq actual.ledgerEvolution.destination (F.evolution current).destination

theorem successor_destination (current : F.Current) :
    HEq (successor F current).ledgerEvolution.destination
      (F.evolution current).destination := by
  have exactImage : DestinationExact F current
      ((ledgerCompiler F).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact heq_of_eq (patch_destination F current)
  exact exactImage _


theorem every_step_generates_the_same_root_next
    (visit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot) :
    (root).generatedNextCurrentAt visit =
      ⟨V F, (root).toAuthoritativeRoot, visit.next (successor F visit.current).next_eq⟩ :=
  SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
    (root) visit (successor F visit.current)

#print axioms successor_destination
#print axioms every_step_generates_the_same_root_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
