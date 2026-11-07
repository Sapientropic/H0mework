import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

/-- The original body report resets the item position for each primitive.
All intermediate stocks, signers and operations agree with the raw fold. -/
theorem primitive_inventory {source target : C}
    {word : RawEvent Party Good Port Technology Instrument} (actual : Trace source word target)
    (index : Nat) :
    inventory source (primitiveScript word) =
      (((Physical.Public.interpreter source.native.input).execute source.raw index word).items.map
        fun item => {item with index := 0}) := by
  induction actual generalizing index with
  | nil => rfl
  | cons source request tail target ready review noConsents valid later ih =>
      have body := the_original_root_executes_the_generated_request source request ready review noConsents valid
      have head := the_actual_body_must_consume_its_original_native_head source request ready review noConsents valid
      have consumed := (Optimality.Programme.Epoch.native_accounting_has_no_second_material_submission
        (afterBody source request) head).2
      have first : Optimality.Programme.Epoch.materialItems (queued source request) =
          [⟨0, source.raw, request⟩] := by
        unfold Optimality.Programme.Epoch.materialItems
        rw [if_neg ((queued_is_ready_iff source request).mpr ready)]
        exact body.2.1
      change Optimality.Programme.Epoch.materialItems (queued source request) ++
          (Optimality.Programme.Epoch.materialItems (afterBody source request) ++
            inventory (afterNative source request) (primitiveScript tail)) = _
      rw [first, consumed, List.nil_append, ih]
      rw [afterNative_keeps_the_same_original_input source request,
        (two_actual_root_steps_pay_and_consume_the_generated_primitive source request
          ready review noConsents valid).2]
      rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
