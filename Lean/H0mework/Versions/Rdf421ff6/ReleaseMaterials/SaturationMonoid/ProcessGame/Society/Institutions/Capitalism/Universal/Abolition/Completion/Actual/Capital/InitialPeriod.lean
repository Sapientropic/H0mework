import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Enactment.Admitted.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Scope.FirstPeriod
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

private theorem accepted_body (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
    (start : Physical.Cursor Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : Physical.Public.wordAt (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past)
      start.incoming = some word)
    (lawful : ∀ item ∈ (Physical.Public.interpreter input).rawItems
      (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past).raw word,
      (Physical.Public.interpreter input).Valid item.before item.request)
    (generated : Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast start = .accepted word selected lawful) :
    Physical.Public.body input depth count prefixLimit renewalLimit oldPast start =
      ((Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past).raw, word) := by
  simp only [Physical.Public.body, Physical.Public.execution, generated, Physical.Public.ResultAt.execution]
  rw [RawLaw.inventory_requests_exact]

variable (origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount)
  (admission : Functions.Revision.InitialAdmissionAt origin)

def firstBody := Physical.Public.body input depth count prefixLimit renewalLimit origin.germ.snapshot.past
  (Functions.Revision.InitialAdmission.start admission)

def originalMembers := Epoch.Interface.Actors.Census.parties input depth count prefixLimit renewalLimit origin.germ.snapshot

/-- The paid bundles belong to the literal source execution of the initial
public root. An admission marker or a law field alone supplies no payment. -/
theorem the_actual_initial_public_body_pays_all_original_life_and_maintenance :
    Exit.Necessity.AllNeedsPaid (Physical.Public.interpreter input) (firstBody origin admission).1
      (originalMembers origin) (firstBody origin admission).2 := by
  cases admission with
  | legacy ready =>
      have legal := fun item present => (ready.scope.checked.2.2.1 item present).1
      obtain ⟨selected, lawful, generated⟩ :=
        Functions.Revision.Scope.the_source_renewal_is_actually_accepted_without_old_consents input
          (Physical.stateAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past)
          ready.scope.word ready.scope.phase legal
      have body := accepted_body (input := input) (depth := depth) (count := count)
        (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) origin.germ.snapshot.past
        (Functions.Revision.InitialAdmission.start (.legacy ready)) _ selected lawful generated
      change Exit.Necessity.AllNeedsPaid _ _ _ _
      unfold firstBody
      rw [body]
      apply (Functions.Revision.Scope.the_public_renewal_keeps_every_original_necessity_and_maintenance_payment input
        (Physical.stateAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past)
        ready.scope.word legal (originalMembers origin)).mpr
      intro person present
      exact ready.scope.checked.2.2.2.1 person
        (List.mem_dedup.mpr (List.mem_append_left _ present))
  | publicPlan plan source =>
      have accepted := Functions.Revision.PublicPlan.the_actual_public_first_period_is_accepted plan
      change (Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
        (Functions.Revision.InitialAdmission.start (.publicPlan plan source))).isAccepted = true at accepted
      cases generated : Physical.Public.resultAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past
          (Functions.Revision.InitialAdmission.start (.publicPlan plan source)) with
      | accepted word selected lawful =>
          have same : word = Functions.Revision.PublicPlan.executable plan.rawWord := Option.some.inj selected.symm
          cases same
          unfold firstBody
          rw [accepted_body _ _ _ selected lawful generated]
          intro person present
          have oldPresent : person ∈ Epoch.Interface.Actors.Census.parties input depth count prefixLimit renewalLimit
              (Physical.Prefix.cursor (Functions.Revision.InitialAdmission.sourceSnapshot origin).past) := by
            unfold Epoch.Interface.Actors.Census.parties
            rw [Physical.Prefix.past_readback]
            exact present
          exact Functions.Revision.PublicPlan.the_public_word_pays_each_original_member plan person oldPresent
      | refused word selected item listed failed => rw [generated] at accepted; cases accepted
      | metadata absent => cases absent

#print axioms the_actual_initial_public_body_pays_all_original_life_and_maintenance

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Capital
