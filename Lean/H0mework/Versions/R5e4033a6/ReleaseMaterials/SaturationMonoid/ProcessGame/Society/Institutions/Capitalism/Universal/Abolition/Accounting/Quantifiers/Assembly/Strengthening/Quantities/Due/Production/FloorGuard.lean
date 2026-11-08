import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Floor.Forecast.Actual
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production.Native
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Witness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

def floorCharge (source : C) (past : Script) (word : Word) (key : Party × Good) : ℚ :=
  required word key.1 key.2 + Service.Floor.forecastHolding source past word key

def floorSupport (source : C) (word : Word) : List (Party × Good) :=
  addresses word ++ Service.Floor.holdingAddresses source

def inspectFloorStock (source : C) (past : Script) (word : Word)
    (opening : ∀ party good, 0 ≤ (Execution.endAt source past).raw.stock party good) :
    StockDecision (Execution.endAt source past).raw (floorCharge source past word) (floorSupport source word) := by
  refine inspectStock _ _ _ ?_ opening
  intro key absent
  have outside : key ∉ Service.Floor.holdingAddresses source :=
    fun member => absent (List.mem_append_right _ member)
  unfold floorCharge
  rw [required_is_zero_at_an_unmentioned_address _ _ _ (fun member => absent (List.mem_append_left _ member)),
    Service.Floor.forecastHolding_zero_off_support source past word key outside, zero_add]

def extraForOriginalFloor (source : C) (past : Script) (word : Word) (key : Party × Good) : ℚ :=
  max 0 (floorCharge source past word key - (Execution.endAt source past).raw.stock key.1 key.2)

theorem extraForOriginalFloor_is_the_tight_address_bound
    (source : C) (past : Script) (word : Word) (key : Party × Good) (extra : ℚ) :
    extraForOriginalFloor source past word key ≤ extra ↔
      0 ≤ extra ∧ floorCharge source past word key ≤
        (Execution.endAt source past).raw.stock key.1 key.2 + extra := by
  rw [extraForOriginalFloor, max_le_iff, sub_le_iff_le_add, add_comm extra]

/-- A submitted use pays its own material once. Its contribution to an
old floor reduces the amount that has to remain after this same word. -/
theorem original_floor_protection_is_exact_for_a_paid_word
    (source : C) (past : Script) (word : Word)
    (services : ∀ request ∈ word, IsService request)
    (paid : PaymentAt (Execution.endAt source past) word []) (key : Party × Good) :
    floorCharge source past word key ≤ (Execution.endAt source past).raw.stock key.1 key.2 ↔
      Service.Floor.holding source (past ++ Execution.primitiveScript word) key ≤
        (Execution.endAt source (past ++ Execution.primitiveScript word)).raw.stock key.1 key.2 := by
  let current := Execution.endAt source past
  have materials : (Execution.endAt current (Execution.primitiveScript word)).raw.stock key.1 key.2 =
      current.raw.stock key.1 key.2 - required word key.1 key.2 := by
    rw [paid.trace.raw_is_the_complete_original_execution 0]
    exact the_paid_service_word_debits_exactly_its_required_stock _ _ _ _ services
      (Execution.admitted_items_of_original_trace paid.trace 0) key.1 key.2
  rw [Execution.endAt_append, materials, ← Service.Floor.paid_trace_realizes_forecastHolding source past word paid.trace key,
    floorCharge, le_sub_iff_add_le, add_comm (Service.Floor.forecastHolding source past word key)]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Production
