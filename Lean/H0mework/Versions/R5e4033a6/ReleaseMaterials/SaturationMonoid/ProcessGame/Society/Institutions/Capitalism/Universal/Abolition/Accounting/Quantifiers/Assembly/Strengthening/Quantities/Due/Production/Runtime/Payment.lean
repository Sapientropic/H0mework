import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Runtime
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- Executable law data from the same live source. The witness is erased
when the raw planner reads the policy and original port checks. -/
structure LawRead (source : C) where
  law : RawLaw Party Good Port Technology Instrument
  exactLaw : law = interpreter source

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {past : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

local notation "Now" => Execution.endAt source past
local notation "Snapshot" => Service.Floor.Runtime.Snapshot source past

local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Readings" => List ((Party × Use × Good × ℚ) × ℚ)

inductive RawPaymentInspection (current : Raw) (rows : Readings) (law : Law) (word : Word)
  | stock (issue : AddressShortage current (Service.Floor.Runtime.chargeRows rows word)
      (Service.Floor.Runtime.supportRows rows word))
  | refused (issue : RawRefusal law current word)
  | ready (funded : ∀ key, Service.Floor.Runtime.chargeRows rows word key ≤ current.stock key.1 key.2)
      (permitted : Every law current 0 word (Permitted law))

/-- This evaluator needs the data read from the source, even when the
logical occurrence itself has no compiled representation. -/
def inspectRawPayment (current : Raw) (rows : Readings) (law : Law) (word : Word)
    (opening : ∀ party good, 0 ≤ current.stock party good) : RawPaymentInspection current rows law word :=
  match Service.Floor.Runtime.inspectRows current rows word opening with
  | .short issue => .stock issue
  | .funded funded =>
    match inspectAuthority law current word with
    | .refused issue => .refused issue
    | .authorized permitted => .ready funded permitted

abbrev PaymentInspection (read : Snapshot) (authority : LawRead Now) (word : Word) :=
  RawPaymentInspection read.current read.rows authority.law word

def inspectPayment (read : Snapshot) (authority : LawRead Now) (word : Word)
    (opening : ∀ party good, 0 ≤ read.current.stock party good) :
    PaymentInspection read authority word :=
  inspectRawPayment read.current read.rows authority.law word opening

/-- An executable positive check is consumed by the original action
interpreter. Stock protecting the original floor survives the actual debit. -/
theorem the_runtime_payment_is_admitted_by_the_original_root
    (read : Snapshot) (authority : LawRead Now) (word : Word)
    (services : ∀ request ∈ word, IsService request)
    (signatures : ∀ request ∈ word, request.consents = [])
    (opening : ∀ party good, 0 ≤ read.current.stock party good)
    (ready : Ready Now) (review : ReviewAvailable Now)
    (funded : ∀ key, read.charge word key ≤ read.current.stock key.1 key.2)
    (permitted : Every authority.law read.current 0 word (Permitted authority.law)) :
    Nonempty (PaymentAt Now word []) ∧
      ∀ key, Service.Floor.holding source (past ++ Execution.primitiveScript word) key ≤
        (Execution.endAt source (past ++ Execution.primitiveScript word)).raw.stock key.1 key.2 := by
  have exactFunds (key : Party × Good) : floorCharge source past word key ≤ (Now).raw.stock key.1 key.2 := by
    rw [← read.current_exact, ← read.charge_exact]
    exact funded key
  have allowed : Every (interpreter Now) (Now).raw 0 word (Permitted (interpreter Now)) := by
    rw [← read.current_exact, ← authority.exactLaw]
    exact permitted
  have originalStock : ∀ party good, 0 ≤ (Now).raw.stock party good := by
    rw [← read.current_exact]
    exact opening
  have useStock (party : Party) (good : Good) :
      required word party good + required ([] : Word) party good ≤ (Now).raw.stock party good := by
    have holds := Service.Floor.forecastHolding_nonnegative source past word (party, good)
    have fits := exactFunds (party, good)
    change required word party good + Service.Floor.forecastHolding source past word (party, good) ≤
      (Now).raw.stock party good at fits
    change required word party good + 0 ≤ (Now).raw.stock party good
    linarith only [holds, fits]
  obtain ⟨paid, _⟩ := a_funded_and_authorized_word_is_submitted_to_the_original_root
    Now word [] services (by simp) signatures originalStock ready review useStock allowed
  exact ⟨⟨paid⟩, fun key => (original_floor_protection_is_exact_for_a_paid_word source past word services paid key).mp
    (exactFunds key)⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Runtime
