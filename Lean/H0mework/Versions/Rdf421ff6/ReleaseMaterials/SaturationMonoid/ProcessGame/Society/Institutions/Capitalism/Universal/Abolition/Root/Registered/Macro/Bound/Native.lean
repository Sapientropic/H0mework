import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound.Rank
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Frame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)

local notation "measure" => rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

/-- The exact source image fixes the accounting successor for every lawful
realization; choosing a different witness cannot postpone the same item. -/
theorem every_generated_successor_has_the_same_accounting_next (current : frame.V.Current)
    (actual : SourceNativeLedgerGeneratedSuccessorAt (frame.root.emitted current)
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current)) :
    frame.cursor actual.targetCurrent =
      Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
        (frame.cursor current) := by
  have same : actual.targetCurrent = (frame.successor current).targetCurrent :=
    Option.some.inj (actual.next_eq.symm.trans (frame.successor current).next_eq)
  rw [same]
  exact frame.next_exact current

theorem every_pending_root_successor_consumes_one_unit (current : frame.V.Current)
    (actual : SourceNativeLedgerGeneratedSuccessorAt (frame.root.emitted current)
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current))
    (pending : 0 < measure (frame.cursor current)) :
    measure (frame.cursor actual.targetCurrent) + 1 = measure (frame.cursor current) := by
  rw [every_generated_successor_has_the_same_accounting_next (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition frame current actual]
  exact each_pending_source_step_consumes_one_unit (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) pending

theorem completed_bookkeeping_keeps_the_same_physical_state (current : frame.V.Current)
    (actual : SourceNativeLedgerGeneratedSuccessorAt (frame.root.emitted current)
      (frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current))
    (paid : Accounting.bodyPaid (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition (frame.cursor current) = true) :
    Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (frame.cursor actual.targetCurrent) =
    Accounting.physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (frame.cursor current) := by
  rw [every_generated_successor_has_the_same_accounting_next (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition frame current actual]
  exact Accounting.bookkeeping_does_not_replay_the_physical_body (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal sourcePosition (frame.cursor current) paid

#print axioms every_generated_successor_has_the_same_accounting_next
#print axioms every_pending_root_successor_consumes_one_unit
#print axioms completed_bookkeeping_keeps_the_same_physical_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound
