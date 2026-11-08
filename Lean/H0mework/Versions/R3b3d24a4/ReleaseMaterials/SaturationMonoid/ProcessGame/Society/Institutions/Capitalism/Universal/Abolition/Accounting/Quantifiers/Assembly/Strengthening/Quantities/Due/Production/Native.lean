import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Funding
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Authority
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Trace Ready ReviewAvailable)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Word" => RawEvent Party Good Port Technology Instrument
abbrev interpreter (source : C) := Physical.Public.interpreter source.native.input

abbrev PermissionShortage (source : C) (word : Word) :=
  RawRefusal (interpreter source) source.raw word

structure PaymentAt (source : C) (word held : Word) where
  trace : Trace source word (Execution.endAt source (Execution.primitiveScript word))
  ready : Ready (Execution.endAt source (Execution.primitiveScript word))
  review : ReviewAvailable (Execution.endAt source (Execution.primitiveScript word))
  holds : ∀ party good, required held party good ≤
    (Execution.endAt source (Execution.primitiveScript word)).raw.stock party good
  whole : Recorded source (Execution.primitiveScript word)

inductive NativeDecision (source : C) (word held : Word)
  | short (issue : FundingShortage source.raw word held)
  | refused (issue : PermissionShortage source word)
  | paid (payment : PaymentAt source word held)

/-- Compare opening stock and original authorities before submitting any
new debit. Admission submits the exact original primitive word. -/
def run (source : C) (word held : Word)
    (services : ∀ request ∈ word, IsService request) (reserve : ∀ request ∈ held, IsService request)
    (unconsented : ∀ request ∈ word, request.consents = [])
    (opening : ∀ party good, 0 ≤ source.raw.stock party good)
    (ready : Ready source) (review : ReviewAvailable source) : NativeDecision source word held := by
  match inspectFunding source.raw word held opening with
  | .short issue => exact .short issue
  | .funded funds =>
    let law := interpreter source
    match inspectAuthority law source.raw word with
    | .refused issue => exact .refused issue
    | .authorized authorized =>
      obtain ⟨valid, remaining⟩ :=
        (all_original_services_are_paid_exactly_when_authorized_and_funded law source.raw 0 word
          services (required held) (required_nonnegative held reserve)).mpr ⟨authorized, funds⟩
      obtain ⟨actual, nextReady, nextReview⟩ :=
        Execution.pay_checked_primitives source word 0 ready review unconsented valid
      refine .paid ⟨actual, nextReady, nextReview, fun party good => ?_, record source _⟩
      rw [actual.raw_is_the_complete_original_execution 0]
      exact remaining party good

theorem a_funded_and_authorized_word_is_submitted_to_the_original_root
    (source : C) (word held : Word)
    (services : ∀ request ∈ word, IsService request) (reserve : ∀ request ∈ held, IsService request)
    (unconsented : ∀ request ∈ word, request.consents = [])
    (opening : ∀ party good, 0 ≤ source.raw.stock party good)
    (ready : Ready source) (review : ReviewAvailable source)
    (funds : ∀ party good, required word party good + required held party good ≤ source.raw.stock party good)
    (authorized : Every (interpreter source) source.raw 0 word (Permitted (interpreter source))) :
    ∃ paid, run source word held services reserve unconsented opening ready review = .paid paid := by
  cases run source word held services reserve unconsented opening ready review with
  | paid result => exact ⟨result, rfl⟩
  | short issue => exact (not_lt_of_ge (funds issue.address.1 issue.address.2) issue.short).elim
  | refused issue => exact (issue.refused (authorized issue.original issue.occurs)).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
