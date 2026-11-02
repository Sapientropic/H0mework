import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData.Builders
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData.Reentry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

def EntryAligned
    {frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}
    (data : FinancialData frame) (basis : Inquiry.Basis frame.N) : Prop :=
  ∀ current ready support, (basis.entry support).1 = ((data.familyAt current ready).val.entry support).1

theorem base_entry_aligned : EntryAligned
    (base (input := input) (depth := depth) (count := count) (prefixLimit := prefixLimit)
      (renewalLimit := renewalLimit) (sourceDepth := sourceDepth) (sourceCount := sourceCount)
      (start := start) (proposal := proposal) (sourcePosition := sourcePosition))
    (Inquiry.baseBasis (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) := by
  intro current ready support
  rfl

theorem born_entry_aligned
    {frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition}
    (data : FinancialData frame) (basis : Inquiry.Basis frame.N) (aligned : EntryAligned data basis)
    {origin : frame.V.Current}
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)
    (current : Admission.Current frame registered) (ready : (data.born registered).Ready current)
    (support : (Admission.nativeFrame frame registered).N.Support) :
    (oldEntry (state? := support.2) (basis.entry support.1)).1 =
      (((data.born registered).familyAt current ready).val.entry support).1 := by
  rcases current with ⟨current, event⟩
  cases event with
  | pending => exact ready.2.elim
  | registered native => exact congrArg Sum.inl (aligned current ready.1 support.1)

theorem reentry_entry_aligned
    {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
    (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
    (seed_eq : Accounting.seedAccount (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0 = anchor) :
    EntryAligned
      (reentry (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq)
      (Reentry.basis input depth count family) := by
  intro current ready support
  rfl

#print axioms base_entry_aligned
#print axioms born_entry_aligned
#print axioms reentry_entry_aligned

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.FinancialData
