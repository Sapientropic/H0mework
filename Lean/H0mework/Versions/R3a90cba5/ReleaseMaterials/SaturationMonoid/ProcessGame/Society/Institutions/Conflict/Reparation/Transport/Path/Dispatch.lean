import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)

abbrev NativeWork (cut : C) := Public.Inquiry.HasWork cut.native.frame cut.native.actual.actual

abbrev registrationAt (cut : C) := Public.Accounting.registration? cut.native.input cut.native.depth cut.native.count
  cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast cut.native.start cut.native.actual.actual

inductive Selected (cut : C)
  | material (ready : ¬ NativeWork cut)
  | accounting (work : NativeWork cut) (noBirth : registrationAt cut = none)
  | registration (work : NativeWork cut)
      (registered : Public.Accounting.Registration cut.native.input cut.native.depth cut.native.count
        cut.native.prefixLimit cut.native.renewalLimit cut.native.oldPast cut.native.start cut.native.actual.actual)
      (original : registrationAt cut = some registered)

def inspect (cut : C) : Selected cut :=
  if work : NativeWork cut then
    match original : registrationAt cut with
    | none => .accounting work original
    | some registered => .registration work registered original
  else .material work

theorem native_step_has_no_material_items {cut : C} (input : Input) (work : NativeWork (query cut input)) :
    inventory cut [input] = [] := by
  simpa only [inventory, List.append_nil] using
    (Optimality.Programme.Epoch.native_accounting_has_no_second_material_submission
      (query cut input) work).2

theorem query_keeps_the_native_network (cut : C) (input : Input) :
    (query cut input).native.frame.N = cut.native.frame.N := by cases input <;> rfl

theorem selected_registration_is_the_original_native_next {cut : C}
    (input : Input) (work : NativeWork (query cut input))
    {registered : Public.Accounting.Registration (query cut input).native.input (query cut input).native.depth
      (query cut input).native.count (query cut input).native.prefixLimit (query cut input).native.renewalLimit
      (query cut input).native.oldPast (query cut input).native.start (query cut input).native.actual.actual}
    (selected : registrationAt (query cut input) = some registered) :
    (next cut input).native = (query cut input).native.birth registered := by
  unfold registrationAt at selected
  unfold next Evolving.Epoch.Current.advance
  rw [dif_pos work, selected]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
