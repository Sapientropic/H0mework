import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

open Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (current : Physical.Cursor Party Good Port Technology Instrument)
  (code : Admission.FeeCode (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def feeInput := Physical.receive current (.primitive code.request)
def feeTarget := Physical.next (feeInput current code)

/-- The existing lower source compiler already realizes the fee as one
actual microstep. Its enclosing mandatory phase must select this input. -/
theorem original_fee_compiler_uses_the_same_paid_microstep :
    match Review.attempt source.seed.law code.request code.scope
        (state source depth count prefixLimit renewalLimit current).raw with
    | .inl paid =>
        (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw = paid.microNext ∧
        (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.stock code.scope.payer code.scope.good +
          code.scope.amount = (state source depth count prefixLimit renewalLimit current).raw.stock code.scope.payer code.scope.good ∧
        (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.claims =
          (state source depth count prefixLimit renewalLimit current).raw.claims ∧
        (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.clock =
          (state source depth count prefixLimit renewalLimit current).raw.clock ∧
        (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.round =
          (state source depth count prefixLimit renewalLimit current).raw.round
    | .inr _obstruction =>
        state source depth count prefixLimit renewalLimit (feeTarget current code) =
          state source depth count prefixLimit renewalLimit current ∧
        ¬ source.seed.law.Valid (state source depth count prefixLimit renewalLimit current).raw code.request := by
  have step := Physical.consumed_input_generates_its_own_after source.input depth count prefixLimit renewalLimit (feeInput current code)
  change state source depth count prefixLimit renewalLimit (feeTarget current code) =
    Compile.next source.input depth count prefixLimit renewalLimit (state source depth count prefixLimit renewalLimit current)
      (.primitive code.request) at step
  cases produced : Review.attempt source.seed.law code.request code.scope
      (state source depth count prefixLimit renewalLimit current).raw with
  | inl paid =>
      have accepted : source.input.law.Valid (state source depth count prefixLimit renewalLimit current).raw code.request := paid.accepted
      have next : (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw = paid.microNext := by
        rw [step]
        simp only [Compile.next, Compile.compile, Actual.inspectPrimitive, dif_pos accepted,
          Compile.Result.next, Actual.Command.next, Actual.primitiveNext, Review.PaymentAt.microNext]
        rfl
      refine ⟨next, ?_, ?_, ?_, ?_⟩
      · rw [next]
        exact paid.micro_stock_balance code.scope
      · rw [next]
        exact paid.micro_claims_unchanged code.scope
      · rw [next]
        exact paid.micro_clock_and_round.1
      · rw [next]
        exact paid.micro_clock_and_round.2
  | inr obstruction =>
      have rejected : ¬ source.input.law.Valid (state source depth count prefixLimit renewalLimit current).raw code.request := obstruction.request_is_actually_rejected
      refine ⟨?_, obstruction.request_is_actually_rejected⟩
      rw [step]
      simp only [Compile.next, Compile.compile, Actual.inspectPrimitive,
        dif_neg rejected, Compile.Result.next]

theorem original_fee_item_is_retained_on_both_branches :
    (Physical.execution source.input depth count prefixLimit renewalLimit (feeInput current code)).items =
      [⟨0, (state source depth count prefixLimit renewalLimit current).raw, code.request⟩] := by
  change (Compile.execution source.input depth count prefixLimit renewalLimit
    (state source depth count prefixLimit renewalLimit current) (.primitive code.request)).items = _
  cases produced : Actual.inspectPrimitive source.input (state source depth count prefixLimit renewalLimit current) code.request <;>
    simp only [Compile.execution, Compile.compile, produced, Compile.Result.execution,
      Compile.Result.requests, Actual.Command.requests, Compile.refusalRequests, RawLaw.execute]

theorem source_fee_microstep_adds_no_period :
    (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.clock =
      (state source depth count prefixLimit renewalLimit current).raw.clock ∧
    (state source depth count prefixLimit renewalLimit (feeTarget current code)).raw.round =
      (state source depth count prefixLimit renewalLimit current).raw.round := by
  have actual := original_fee_compiler_uses_the_same_paid_microstep source depth count prefixLimit renewalLimit current code
  cases produced : Review.attempt source.seed.law code.request code.scope (state source depth count prefixLimit renewalLimit current).raw with
  | inl paid => rw [produced] at actual; exact actual.2.2.2
  | inr obstruction => rw [produced] at actual; rw [actual.1]; exact ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.original_fee_compiler_uses_the_same_paid_microstep
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.Budget.original_fee_item_is_retained_on_both_branches
