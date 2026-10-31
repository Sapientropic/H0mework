import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Origin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : OriginAt input frame visit claim)
  (gate : Responsibility.GateOccurrence mechanism past nature response)

include origin in
theorem the_responsible_controller_is_present_on_its_original_occurrence :
    Source.ProgrammeFace.ActualBirth.presentAt input (originalVisit input frame visit)
      (gate.controller mechanism past nature response) := by
  change gate.controller mechanism past nature response ∈
    Source.ProgrammeFace.parties input.law
      (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current,
       ProgrammeSource.rawEvent input (originalVisit input frame visit).current)
  unfold Source.ProgrammeFace.parties
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨gate.item.val,?_,?_⟩
  · rw [← the_assessed_inventory_is_the_literal_original_execution input frame visit claim origin]
    exact gate.item.property
  · rw [← origin.law]
    exact gate.controller_is_an_original_item_participant mechanism past nature response

/-- This actor is read from the original lineage fold; the responsibility
compiler does not manufacture one from the displayed controller key. -/
def originalController := Source.ProgrammeFace.ActualBirth.atCurrent input
  (originalVisit input frame visit) (gate.controller mechanism past nature response)
  (the_responsible_controller_is_present_on_its_original_occurrence input frame visit claim origin gate)

def originalControllerActor := (originalController input frame visit claim origin gate).actor input

#print axioms originalControllerActor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source
