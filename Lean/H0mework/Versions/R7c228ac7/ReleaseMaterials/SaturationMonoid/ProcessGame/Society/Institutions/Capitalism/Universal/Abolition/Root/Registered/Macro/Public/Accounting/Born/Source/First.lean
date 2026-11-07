import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.GeneratedRow
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)

local notation "root" => livingRoot prior origin registered
local notation "emit" => emitted prior origin registered

def initialVisit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot :=
  .finite (root).toAuthoritativeRoot.toRoot.initialVisit

def initialOldRow (entry : OpenResponsibilityAt world (oldSupport prior origin)) :=
  generatedRow prior origin registered (initialVisit prior origin registered)
    (oldEntry (law := Born.law origin registered) (state? := some .pending) entry)

def initialBornRow := generatedRow prior origin registered (initialVisit prior origin registered)
  (debtEntry (N := world) (law := Born.law origin registered) (oldSupport prior origin) .pending)

def initialOldAuthority (entry : OpenResponsibilityAt world (oldSupport prior origin)) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow (root)
    (oldEntry (law := Born.law origin registered) (state? := some .pending) entry)
    (initialOldRow prior origin registered entry)

def initialBornAuthority :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow (root)
    (debtEntry (N := world) (law := Born.law origin registered) (oldSupport prior origin) .pending)
    (initialBornRow prior origin registered)

def firstSuccessor := successor prior origin registered none

def firstVisit : SourceNativeTemporalVisitAt (root).toAuthoritativeRoot.toLedgerRoot :=
  (initialVisit prior origin registered).next (firstSuccessor prior origin registered).next_eq

theorem first_visit_is_the_literal_registered_next :
    (firstVisit prior origin registered).current = some registered.next :=
  successor_current prior origin registered none

theorem successor_support (current : State origin registered) :
    (successor prior origin registered current).targetOccurrence.1 =
      supportAt prior origin registered (next origin registered current) := by
  have emittedAt := occurrence_eq_emitted prior origin registered
    (successor prior origin registered current).targetOccurrence
  exact (congrArg (fun occurrence => occurrence.1) emittedAt).trans
    (congrArg (supportAt prior origin registered) (successor_current prior origin registered current))

private def DestinationExact (current : State origin registered)
    (image : SourceNativeLedgerEvolutionAt (source prior origin registered) (emit current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emit current) image,
    HEq actual.ledgerEvolution.destination (wholeEvolution prior origin registered current).destination

theorem successor_destination (current : State origin registered) :
    HEq (successor prior origin registered current).ledgerEvolution.destination
      (wholeEvolution prior origin registered current).destination := by
  have exactImage : DestinationExact prior origin registered current
      ((ledgerCompiler prior origin registered).compile (emit current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact heq_of_eq (patch_destination prior origin registered current)
  exact exactImage _

theorem first_support_is_the_literal_complete_admission :
    (firstSuccessor prior origin registered).targetOccurrence.1 = targetSupport prior origin registered :=
  successor_support prior origin registered none

theorem first_destination_is_the_literal_complete_admission :
    HEq (firstSuccessor prior origin registered).ledgerEvolution.destination
      (firstWrite prior origin registered).destination :=
  successor_destination prior origin registered none

theorem the_first_write_produces_the_root_next :
    (root).generatedNextCurrentAt (initialVisit prior origin registered) =
      ⟨V prior origin registered, (root).toAuthoritativeRoot, firstVisit prior origin registered⟩ :=
  Registered.Macro.Ingress.next_is_the_same_generated_successor (root)
    (initialVisit prior origin registered) (firstSuccessor prior origin registered)

#print axioms initialBornAuthority
#print axioms first_visit_is_the_literal_registered_next
#print axioms first_destination_is_the_literal_complete_admission
#print axioms the_first_write_produces_the_root_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
