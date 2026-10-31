import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

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

local notation "C" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0
local notation "frame" => activeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq

def currentFamily (current : C) : Epoch.Finance.Future.Continuation.AccountFamily input depth count world current.account :=
  family.after current.account
    (nativeTail (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal seed_eq current)

theorem current_family_is_the_same_root_support (current : C) :
    (currentFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).currentSupport =
      (frame).sourceSupport current := rfl

theorem original_native_next_reads_the_same_family (current : C) :
    (currentFamily (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal family seed_eq current).support
      ((frame).account ((frame).next current)) ⟨(frame).native current⟩ =
        (frame).sourceSupport ((frame).next current) := rfl

theorem first_body_does_not_repeat_financial_admission :
    (frame).account ((frame).next
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0)) = anchor := by
  have next := congrArg Accounting.Current.account ((frame).next_exact
    (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal 0))
  exact next.trans ((Accounting.first_body_keeps_the_entire_native_account (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal 0).trans seed_eq)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.currentFamily
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.original_native_next_reads_the_same_family
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Reentry.first_body_does_not_repeat_financial_admission
