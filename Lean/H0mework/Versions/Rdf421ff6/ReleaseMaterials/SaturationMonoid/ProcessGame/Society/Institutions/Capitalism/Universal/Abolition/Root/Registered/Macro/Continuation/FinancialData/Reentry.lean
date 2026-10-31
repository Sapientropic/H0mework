import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  {review : Option (ReviewPhase.ContextAt input)}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor)

local notation "frame" => Reentry.nativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

private theorem next_body_is_actual
    (current : Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0) :
    Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
      ((frame).next current) = true :=
  (congrArg (Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0)
    (Reentry.successor_current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current)).trans
    (Accounting.every_generated_next_has_a_completed_body (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current)

def reentry : FinancialData (frame) where
  Ready := fun current => Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 current = true
  ready_next := fun current _ => next_body_is_actual (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current
  bodyPaid := fun _ ready => ready
  familyAt := fun current _ =>
    ⟨Reentry.currentFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current,
      Reentry.current_family_is_the_same_root_support (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current⟩
  next_support := fun current _ =>
    Reentry.original_native_next_reads_the_same_family (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current
  occurrence_eq_emitted := fun _ occurrence => Reentry.occurrence_eq_emitted (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal family seed_eq occurrence

theorem reentry_body_generates_the_same_financial_dictionary :
    (reentry (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq).Ready
      ((frame).next (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0)) :=
  next_body_is_actual (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq _

#print axioms reentry
#print axioms reentry_body_generates_the_same_financial_dictionary

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData
