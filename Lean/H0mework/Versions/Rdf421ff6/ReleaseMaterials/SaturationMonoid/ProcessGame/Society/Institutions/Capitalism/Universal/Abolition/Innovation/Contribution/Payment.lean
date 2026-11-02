import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.RiskMath
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution

open Source.Program

variable {Party Good Port Technology Instrument : Type}

/-- A finite cash rule. The actual producer supplies its branch only from
the paid local observation and checks the resulting request on that source. -/
def payment (payer bearer : Party) (unit : Good) (purpose : Port)
    (loss reward : ℚ) (succeeded : Bool) : Request Party Good Port Technology Instrument :=
  if succeeded then ⟨payer, [], purpose, [], .transfer payer bearer [(unit, reward)]⟩
  else ⟨bearer, [], purpose, [], .transfer bearer payer [(unit, loss)]⟩

theorem the_payment_is_signed_by_its_actual_material_contributor
    (payer bearer : Party) (unit : Good) (purpose : Port) (loss reward : ℚ) (succeeded : Bool) :
    (payment (Technology := Technology) (Instrument := Instrument)
      payer bearer unit purpose loss reward succeeded).signer =
      if succeeded then payer else bearer := by
  cases succeeded <;> rfl

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem a_cash_contribution_does_not_change_the_old_claims_or_control_rule
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (payer bearer : Party) (unit : Good) (purpose : Port) (loss reward : ℚ) (succeeded : Bool) :
    (law.step before (payment payer bearer unit purpose loss reward succeeded)).claims = before.claims ∧
      (law.step before (payment payer bearer unit purpose loss reward succeeded)).technology = before.technology ∧
      (∀ port subject,
        law.allowed (law.step before (payment payer bearer unit purpose loss reward succeeded)).technology port subject =
          law.allowed before.technology port subject) := by
  by_cases accepted : law.Valid before (payment payer bearer unit purpose loss reward succeeded)
  · simp only [RawLaw.step, if_pos accepted]
    cases succeeded <;> exact ⟨rfl, rfl, fun _ _ => rfl⟩
  · rw [law.rejected_preserves_current _ _ accepted]
    exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem an_actual_success_pays_its_declared_finite_reward
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (payer bearer : Party) (different : payer ≠ bearer) (unit : Good) (purpose : Port)
    (loss reward : ℚ)
    (paid : law.Valid before (payment payer bearer unit purpose loss reward true)) :
    (law.step before (payment payer bearer unit purpose loss reward true)).stock bearer unit =
        before.stock bearer unit + reward ∧
      (law.step before (payment payer bearer unit purpose loss reward true)).stock payer unit =
        before.stock payer unit - reward := by
  simp only [RawLaw.step, if_pos paid]
  simp [payment, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
    flowAt, locate, amount, different, Ne.symm different]

theorem an_actual_failure_keeps_its_real_material_bearer
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (payer bearer : Party) (different : payer ≠ bearer) (unit : Good) (purpose : Port)
    (loss reward : ℚ)
    (paid : law.Valid before (payment payer bearer unit purpose loss reward false)) :
    (law.step before (payment payer bearer unit purpose loss reward false)).stock bearer unit =
        before.stock bearer unit - loss ∧
      (law.step before (payment payer bearer unit purpose loss reward false)).stock payer unit =
        before.stock payer unit + loss := by
  simp only [RawLaw.step, if_pos paid]
  simp [payment, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
    flowAt, locate, amount, different, Ne.symm different]

theorem an_unpaid_reward_does_not_create_a_phantom_transfer
    (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument)
    (payer bearer : Party) (unit : Good) (purpose : Port) (loss reward : ℚ) (succeeded : Bool)
    (failed : ¬ law.Valid before (payment payer bearer unit purpose loss reward succeeded)) :
    law.step before (payment payer bearer unit purpose loss reward succeeded) = before :=
  law.rejected_preserves_current _ _ failed

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution
