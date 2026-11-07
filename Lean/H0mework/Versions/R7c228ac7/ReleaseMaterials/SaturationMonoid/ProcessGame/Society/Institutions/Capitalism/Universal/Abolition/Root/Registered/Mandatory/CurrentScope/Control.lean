import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- A rejected current renewal cannot execute the old automatic advance.
Other raw alternatives retain their original continuing responsibility. -/
def filterRaw (proposal selected : Compile.RawInput Party Good Port Technology Instrument) :
    Compile.RawInput Party Good Port Technology Instrument :=
  match hazard? input depth count prefixLimit renewalLimit current with
  | none => selected
  | some _ => match proposal with | .advance => .stopReview | _ => proposal

/-- A rejected advance retains its original proposal as refused work.
A nonadvance alternative actually forwarded by this guard is not deferred. -/
def filterDeferred (proposal : Compile.RawInput Party Good Port Technology Instrument)
    (selected : Option (Compile.RawInput Party Good Port Technology Instrument)) :
    Option (Compile.RawInput Party Good Port Technology Instrument) :=
  match hazard? input depth count prefixLimit renewalLimit current with
  | none => selected
  | some _ => match proposal with | .advance => some .advance | _ => none

theorem a_clear_actual_scope_keeps_the_original_opcode
    (clear : hazard? input depth count prefixLimit renewalLimit current = none)
    (proposal selected : Compile.RawInput Party Good Port Technology Instrument) :
    filterRaw input depth count prefixLimit renewalLimit current proposal selected = selected := by
  simp only [filterRaw, clear]

theorem a_rejected_actual_scope_forces_the_typed_stop
    (failure : Failure input depth count prefixLimit renewalLimit current)
    (source : hazard? input depth count prefixLimit renewalLimit current = some failure)
    (selected : Compile.RawInput Party Good Port Technology Instrument) :
    filterRaw input depth count prefixLimit renewalLimit current .advance selected = .stopReview := by
  simp only [filterRaw, source]

theorem no_rejected_actual_scope_can_become_an_automatic_payment
    (failure : Failure input depth count prefixLimit renewalLimit current)
    (source : hazard? input depth count prefixLimit renewalLimit current = some failure)
    (proposal selected : Compile.RawInput Party Good Port Technology Instrument) :
    filterRaw input depth count prefixLimit renewalLimit current proposal selected ≠ .advance := by
  cases proposal <;> simp only [filterRaw, source] <;> intro impossible <;> cases impossible

theorem every_nonadvance_alternative_remains_the_original_raw_input
    (failure : Failure input depth count prefixLimit renewalLimit current)
    (source : hazard? input depth count prefixLimit renewalLimit current = some failure)
    (raw selected : Compile.RawInput Party Good Port Technology Instrument) (other : raw ≠ .advance) :
    filterRaw input depth count prefixLimit renewalLimit current raw selected = raw := by
  cases raw
  · exact (other rfl).elim
  all_goals simp only [filterRaw, source]

#print axioms filterRaw
#print axioms a_rejected_actual_scope_forces_the_typed_stop
#print axioms no_rejected_actual_scope_can_become_an_automatic_payment

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Mandatory.CurrentScope
