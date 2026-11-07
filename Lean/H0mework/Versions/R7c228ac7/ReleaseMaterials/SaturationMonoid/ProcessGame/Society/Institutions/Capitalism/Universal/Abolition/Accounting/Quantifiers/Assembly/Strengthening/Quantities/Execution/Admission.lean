import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Coverage
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Resign

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- A physically admitted original word is paid by the same native root.
There is no separate bound on its length and no supplied target. -/
theorem pay_checked_primitives (source : C) (word : Word) (index : Nat)
    (ready : Ready source) (review : ReviewAvailable source)
    (unconsented : ∀ request ∈ word, request.consents = [])
    (valid : ∀ item ∈ ((Physical.Public.interpreter source.native.input).execute source.raw index word).items,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request) :
    Trace source word (endAt source (primitiveScript word)) ∧
      Ready (endAt source (primitiveScript word)) ∧ ReviewAvailable (endAt source (primitiveScript word)) := by
  induction word generalizing source index with
  | nil => exact ⟨.nil source, ready, review⟩
  | cons request tail ih =>
      simp only [RawLaw.execute, List.forall_mem_cons] at valid
      have noConsents := unconsented request List.mem_cons_self
      let current := afterNative source request
      have actual := two_actual_root_steps_pay_and_consume_the_generated_primitive
        source request ready review noConsents valid.1
      have sameInput : current.native.input = source.native.input :=
        afterNative_keeps_the_same_original_input source request
      have sameCut : current.raw =
          (Physical.Public.interpreter source.native.input).step source.raw request := actual.2
      have later : ∀ item ∈ ((Physical.Public.interpreter current.native.input).execute
          current.raw (index + 1) tail).items,
          (Physical.Public.interpreter current.native.input).Valid item.before item.request := by
        rw [sameInput, sameCut]
        exact valid.2
      obtain ⟨trace, finished, available⟩ := ih current (index + 1) actual.1
        (afterNative_keeps_the_available_review source request ready review noConsents valid.1)
        (fun next inside => unconsented next (List.mem_cons_of_mem _ inside)) later
      exact ⟨.cons source request tail _ ready review noConsents valid.1 trace, finished, available⟩

theorem pay_checked_word (source : C) (word : Word) (ready : Ready source)
    (review : ReviewAvailable source)
    (valid : ∀ item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw word,
      (Physical.Public.interpreter source.native.input).Valid item.before item.request) :
    Trace source (normalise word) (endAt source (primitiveScript (normalise word))) ∧
      Ready (endAt source (primitiveScript (normalise word))) :=
  let actual := pay_checked_primitives source (normalise word) 0 ready review
    (normalised_requests_have_no_controller_consents word)
    (public_normalisation_preserves_all_actual_request_guards source.native.input.law source.raw 0 word valid)
  ⟨actual.1, actual.2.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution
