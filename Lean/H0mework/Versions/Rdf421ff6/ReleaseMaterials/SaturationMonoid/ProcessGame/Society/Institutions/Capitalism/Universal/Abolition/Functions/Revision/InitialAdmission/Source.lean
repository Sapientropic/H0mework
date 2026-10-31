import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Trigger.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (context : Context (input := input) (review := review) depth count prefixLimit renewalLimit sourceDepth sourceCount)

namespace InitialAdmission

def sourceSnapshot := Physical.receive context.germ.snapshot context.germ.raw
abbrev PublicPlanAt := PublicPlan.Plan input depth count prefixLimit renewalLimit (sourceSnapshot context)
abbrev PublicObstructionAt := PublicPlan.Obstruction input depth count prefixLimit renewalLimit (sourceSnapshot context)
abbrev inspectPublic := PublicPlan.compile input depth count prefixLimit renewalLimit (sourceSnapshot context)

end InitialAdmission

inductive InitialAdmissionAt : Type
  | legacy (ready : Trigger.ReadyAt context)
  | publicPlan (plan : InitialAdmission.PublicPlanAt context)
      (source : InitialAdmission.inspectPublic context = .accepted plan)

structure InitialObstructionAt where
  previous : Trigger.Selection context
  previous_source : Trigger.select context = previous
  publicObstruction : InitialAdmission.PublicObstructionAt context
  public_source : InitialAdmission.inspectPublic context = .obstructed publicObstruction

inductive InitialSelection : Type
  | admitted (admission : InitialAdmissionAt context)
  | obstructed (obstruction : InitialObstructionAt context)

namespace InitialAdmission

def fromPublic : InitialSelection context :=
  match public_source : inspectPublic context with
  | .accepted plan => .admitted (.publicPlan plan public_source)
  | .obstructed failed => .obstructed ⟨Trigger.select context, rfl, failed, public_source⟩

def select : InitialSelection context :=
  match Abolition.Completion.Actual.Dividend.Financial.Preference.select
      input depth count prefixLimit renewalLimit (sourceSnapshot context) with
  | .selected _ => fromPublic context
  | .noStrict _ => match Trigger.select context with
      | .enactment ready => .admitted (.legacy ready)
      | _ => fromPublic context

variable {context}

def start : InitialAdmissionAt context → Physical.Cursor Party Good Port Technology Instrument
  | .legacy _ => Physical.initial
  | .publicPlan plan _ => Physical.receive Physical.initial (.execute plan.rawWord)

def reader (_ : InitialAdmissionAt context) : Macro.Raw.Reader input depth count :=
  Adaptive.reader input depth count prefixLimit renewalLimit context.germ.snapshot.past context.reader

variable (context)

theorem a_publicly_available_source_plan_forces_admission
    (available : ∃ word ∈ PublicPlan.candidates input depth count prefixLimit renewalLimit (sourceSnapshot context),
      PublicPlan.Checks input depth count prefixLimit renewalLimit (sourceSnapshot context) word) :
    ∃ admission, select context = .admitted admission := by
  obtain ⟨plan, generated⟩ := PublicPlan.a_publicly_available_source_word_cannot_be_vetoed input depth count
    prefixLimit renewalLimit (sourceSnapshot context) available
  cases result : select context with
  | admitted admission => exact ⟨admission, rfl⟩
  | obstructed obstruction =>
      have rejected := obstruction.public_source
      change PublicPlan.compile input depth count prefixLimit renewalLimit (sourceSnapshot context) = _ at rejected
      rw [generated] at rejected
      cases rejected

theorem an_available_strict_plan_is_selected_before_the_old_authority
    (selection : Abolition.Completion.Actual.Dividend.Financial.Preference.Selected
      input depth count prefixLimit renewalLimit (sourceSnapshot context))
    (preferred : Abolition.Completion.Actual.Dividend.Financial.Preference.select
      input depth count prefixLimit renewalLimit (sourceSnapshot context) = .selected selection) :
    ∃ plan, ∃ source : inspectPublic context = .accepted plan,
      select context = .admitted (.publicPlan plan source) ∧
      Abolition.Completion.Actual.Dividend.Financial.Checks input depth count prefixLimit renewalLimit
        (sourceSnapshot context).past
        (Abolition.Completion.Actual.Dividend.Financial.Preference.firstPeriod plan.rawWord) := by
  obtain ⟨plan, source, _same, strict⟩ :=
    PublicPlan.an_available_full_account_improvement_is_the_actual_public_plan
      input depth count prefixLimit renewalLimit (sourceSnapshot context) selection preferred
  refine ⟨plan, source, ?_, strict⟩
  simp only [select, preferred, fromPublic]
  split
  · rename_i actual produced
    have same : actual = plan := PublicPlan.Outcome.accepted.inj (produced.symm.trans source)
    cases same
    rfl
  · rename_i failed produced
    have impossible : PublicPlan.Outcome.accepted plan = .obstructed failed := source.symm.trans produced
    cases impossible

#print axioms select
#print axioms a_publicly_available_source_plan_forces_admission
#print axioms an_available_strict_plan_is_selected_before_the_old_authority

end InitialAdmission
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision
