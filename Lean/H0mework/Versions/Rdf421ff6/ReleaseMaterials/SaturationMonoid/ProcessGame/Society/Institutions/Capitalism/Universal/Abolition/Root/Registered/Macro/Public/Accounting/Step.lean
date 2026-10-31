import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {anchor : (Epoch.Finance.process input depth count).GeneratedState}

def item? (current : Current input depth count anchor) : Option (Epoch.Finance.ActualItem input depth count) :=
  if current.bodyPaid then (items input depth count prefixLimit renewalLimit oldPast start)[current.position]? else none

/-- A newly issued debt is exposed for the original admission compiler.
The ordinary source cannot append its slot before that first write. -/
def next (current : Current input depth count anchor) : Current input depth count anchor :=
  if paid : current.bodyPaid = true then
    match item? input depth count prefixLimit renewalLimit oldPast start current with
    | none => current
    | some item => match Epoch.Finance.readNewClaim input depth count item with
      | some _ => current
      | none => current.afterItem paid item
  else bodyTarget input depth count anchor

theorem the_unexecuted_body_has_no_financial_head :
    item? input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor) = none := rfl

theorem the_first_write_executes_the_body_only_once :
    next input depth count prefixLimit renewalLimit oldPast start (initial input depth count anchor) =
      bodyTarget input depth count anchor := rfl

theorem the_original_admission_cannot_be_bypassed_by_an_ordinary_step
    (current : Current input depth count anchor) (paid : current.bodyPaid = true)
    (item : Epoch.Finance.ActualItem input depth count)
    (present : item? input depth count prefixLimit renewalLimit oldPast start current = some item)
    (claim : Epoch.Finance.NewClaim input depth count)
    (issued : Epoch.Finance.readNewClaim input depth count item = some claim) :
    next input depth count prefixLimit renewalLimit oldPast start current = current := by
  simp only [next, dif_pos paid, present, issued]

def physical (current : Current input depth count anchor) :=
  if current.bodyPaid then
    Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast (Physical.next start).past
  else Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past

theorem financial_steps_do_not_replay_the_physical_body
    (current : Current input depth count anchor) (paid : current.bodyPaid = true) :
    physical input depth count prefixLimit renewalLimit oldPast start
        (next input depth count prefixLimit renewalLimit oldPast start current) =
      physical input depth count prefixLimit renewalLimit oldPast start current := by
  unfold next
  rw [dif_pos paid]
  split
  · rfl
  · split
    · rfl
    · simp only [physical, (Current.after_item_reads_the_source_generated_native_account current paid _).2.2,
        paid, if_true]

#print axioms next
#print axioms the_original_admission_cannot_be_bypassed_by_an_ordinary_step
#print axioms financial_steps_do_not_replay_the_physical_body

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting
