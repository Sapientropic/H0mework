import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve.Funding
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Admission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program Abolition.Root Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- The stock change of an original funding prefix includes actual debits.
All financial and control coordinates remain at its literal successor. -/
def stockChange (source : C) (funding : Script) (bearer : Party) (good : Good) : ℚ :=
  (Execution.endAt source funding).raw.stock bearer good - source.raw.stock bearer good

def stockBaseline (source : C) (funding : Script) : RawCurrent Party Good Technology Instrument :=
  { (Execution.endAt source funding).raw with stock := source.raw.stock }

abbrev fundedLaw (source : C) (funding : Script) :=
  Physical.Public.interpreter (Execution.endAt source funding).native.input

theorem the_funded_current_has_exactly_the_real_stock_change (source : C) (funding : Script) :
    (stockBaseline source funding).addReserve (stockChange source funding) =
      (Execution.endAt source funding).raw := by
  apply RawCurrent.ext
  · funext bearer good
    change source.raw.stock bearer good +
        ((Execution.endAt source funding).raw.stock bearer good - source.raw.stock bearer good) =
      (Execution.endAt source funding).raw.stock bearer good
    ring
  · rfl
  · rfl
  · rfl
  · rfl

theorem real_funding_admits_the_original_word_iff_exact_stock_and_gates
    (source : C) (funding : Script) (word : Word) :
    Accepted (fundedLaw source funding) (Execution.endAt source funding).raw word ↔
      Guards (fundedLaw source funding) (stockChange source funding) (stockBaseline source funding) word ∧
      FitsThrough (fundedLaw source funding) (stockChange source funding) (stockBaseline source funding) word := by
  have exactDomain := the_original_word_is_executable_iff_its_gates_and_joint_stock_fit
    (fundedLaw source funding) (stockBaseline source funding) word (stockChange source funding)
  rw [the_funded_current_has_exactly_the_real_stock_change] at exactDomain
  exact exactDomain

def fundedScript (funding : Script) (word : Word) : Script :=
  funding ++ Execution.primitiveScript (normalise word)

theorem exact_paid_funding_generates_the_original_word_and_complete_account
    (source : C) (funding : Script) (word : Word)
    (ready : Ready (Execution.endAt source funding))
    (review : ReviewAvailable (Execution.endAt source funding))
    (gates : Guards (fundedLaw source funding) (stockChange source funding) (stockBaseline source funding) word)
    (stock : FitsThrough (fundedLaw source funding) (stockChange source funding) (stockBaseline source funding) word) :
    Trace (Execution.endAt source funding) (normalise word)
      (Execution.endAt source (fundedScript funding word)) ∧
    Ready (Execution.endAt source (fundedScript funding word)) ∧
    Recorded source (fundedScript funding word) := by
  have accepted := (real_funding_admits_the_original_word_iff_exact_stock_and_gates source funding word).mpr ⟨gates, stock⟩
  obtain ⟨paid, finished⟩ := Execution.pay_checked_word (Execution.endAt source funding) word ready review accepted
  exact ⟨by rw [fundedScript, Execution.endAt_append]; exact paid,
    by rw [fundedScript, Execution.endAt_append]; exact finished, record source _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve
