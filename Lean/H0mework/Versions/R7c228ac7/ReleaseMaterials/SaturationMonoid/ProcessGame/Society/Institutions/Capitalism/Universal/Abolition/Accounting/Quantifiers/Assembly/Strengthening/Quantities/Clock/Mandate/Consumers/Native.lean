import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Release

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Consumers

open Source.Program PublicFunction PublicFunction.Mandate

noncomputable section

def actualBound : BoundSource Source.base Source.scope := ⟨Source.source, rfl⟩

theorem the_original_real_clock_expires_at_eleven_for_every_input_history
    (inputs : List (List Source.Action)) (ordinal : Nat) :
    Source.scope.task.deadline < clockAt actualBound inputs ordinal ↔ 11 ≤ ordinal := by
  have clock := exact_expiry_for_owned_constant_duration actualBound inputs 1 (by decide) (fun _ => rfl) ordinal
  have bound : expiryOrdinal actualBound.source.seed.initial.clock Source.scope.task.deadline 1 = 11 := by
    decide +kernel
  simpa only [bound] using clock

theorem the_original_ordinal_ten_is_still_inside_the_inclusive_window
    (inputs : List (List Source.Action)) : clockAt actualBound inputs 10 ≤ Source.scope.task.deadline := by
  apply le_of_not_gt
  intro expired
  have impossible := (the_original_real_clock_expires_at_eleven_for_every_input_history inputs 10).mp expired
  omega

theorem the_original_expired_cut_consumes_the_no_renewal_contract
    (inputs : List (List Source.Action)) (ordinal : Nat) (late : 11 ≤ ordinal)
    (word : List Source.Action)
    (actual : ActualCommand Source.base Source.scope
      (OutstandingSource.History.currentAt actualBound.source inputs ordinal) word) :
    actual.command ≠ .accept ∧ actual.command ≠ .renew ∧ ∀ candidate, actual.command ≠ .propose candidate :=
  the_expired_original_root_cannot_propose_accept_or_renew actualBound inputs ordinal
    ((the_original_real_clock_expires_at_eleven_for_every_input_history inputs ordinal).mpr late) word actual

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Consumers
