import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity.Holding
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Row : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

def beforeStock (source : C) (script : Script)
    (item : OriginalOrdinal source script) (key : Party × Good) : ℚ :=
  (Execution.timedAt source script item).1.before.stock key.1 key.2

theorem actual_debit_uses_pre_credit_stock
    (source : C) (script : Script) (address : Row → Party × Good) (deadline required : Row → ℚ)
    (paid : Row → OriginalOrdinal source script → ℚ) (item : OriginalOrdinal source script)
    (nonnegative : ∀ party good, 0 ≤ beforeStock source script item (party, good)) (key : Party × Good) :
    (profile source script address deadline required paid).debit item key ≤ beforeStock source script item key := by
  let law := source.native.handlerFace.rootRead
  let actual := (Execution.timedAt source script item).1
  change flowAt (law.actualDebit actual.before actual.request) key.1 key.2 ≤ actual.before.stock key.1 key.2
  delta RawLaw.actualDebit
  split
  · rename_i accepted
    exact law.debit_affordable actual.before actual.request nonnegative accepted key.1 key.2
  · exact nonnegative key.1 key.2

variable [Fintype Row]

def inspectOriginalRolling (source : C) (script : Script) (address : Row → Party × Good)
    (deadline required : Row → ℚ) (paid : Row → OriginalOrdinal source script → ℚ)
    (addresses : List (Party × Good)) (reserve : Party × Good → ℚ) :
    (let view := profile source script address deadline required paid
     view.DecisionAt (view.protectedGap (beforeStock source script)) addresses reserve) ×
      PLift (Recorded source script) :=
  ⟨(profile source script address deadline required paid).inspectProtected
      (beforeStock source script) addresses reserve, ⟨record source script⟩⟩

theorem original_rolling_shortage_has_a_cut_and_whole_ledger
    (source : C) (script : Script) (address : Row → Party × Good)
    (deadline required : Row → ℚ) (paid : Row → OriginalOrdinal source script → ℚ)
    (addresses : List (Party × Good)) (reserve : Party × Good → ℚ)
    (fundedReserve : ∀ key ∈ addresses, 0 ≤ reserve key)
    (failure : let view := profile source script address deadline required paid
      view.FirstShortageAt (view.protectedGap (beforeStock source script)) addresses reserve) :
    let view := profile source script address deadline required paid
    Recorded source (committedPrefix failure.time source script) ∧
      (reserve failure.address <
        view.outstandingDue failure.time failure.address -
          (Execution.endAt source (committedPrefix failure.time source script)).raw.stock
            failure.address.1 failure.address.2 ∨
       ∃ item : OriginalOrdinal source script,
         (Execution.timedAt source script item).2 = failure.time ∧
           reserve failure.address < view.beforeDebitGap (beforeStock source script) item failure.address) := by
  let view := profile source script address deadline required paid
  have cause := Profile.protected_shortage_cause
    (fun item => (Execution.an_ordinal_uses_its_actual_committing_clock source script item).1)
    fundedReserve failure
  refine ⟨record _ _, ?_⟩
  rcases cause with after | during
  · exact .inl (by
      rw [← profile_stock_is_original_stock_at_the_commit_cut source script address deadline required paid]
      exact after)
  · exact .inr during

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Liquidity
