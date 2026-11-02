import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem the_original_actual_issue_generates_its_native_claim
    (item : Epoch.Finance.ActualItem input depth count)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation =
      .issue instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid
      (item.instruction input depth count).before (item.instruction input depth count).request) :
    (Epoch.Finance.readNewClaim input depth count item).isSome = true := by
  unfold Epoch.Finance.readNewClaim
  split
  · simp only [dif_pos accepted, Option.isSome_some]
  · simp_all
    rename_i absent
    exact absent instrument debtor holder quantity rfl rfl rfl rfl

variable (prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

theorem the_paid_original_issue_head_generates_its_registration
    (current : Macro.Public.Accounting.Current input depth count anchor)
    (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (head : Macro.Public.Accounting.item? input depth count prefixLimit renewalLimit oldPast start current = some item)
    (instrument : Instrument) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation =
      .issue instrument debtor holder quantity)
    (accepted : (item.interpreter input depth count).Valid
      (item.instruction input depth count).before (item.instruction input depth count).request) :
    (Macro.Public.Accounting.registration? input depth count prefixLimit renewalLimit oldPast start current).isSome = true := by
  have found := the_original_actual_issue_generates_its_native_claim input depth count
    item instrument debtor holder quantity operation accepted
  unfold Macro.Public.Accounting.registration?
  rw [dif_pos paid]
  split
  · rename_i absent
    cases absent.symm.trans head
  · rename_i actual present
    have same : actual = item := Option.some.inj (present.symm.trans head)
    subst actual
    split
    · rename_i missing
      rw [missing] at found
      cases found
    · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native
