import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Residual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "RequestAt" => Request Party Good Port Technology Instrument

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem located_amount (owner person : Party) (goods : Bundle Good) (good : Good) :
    flowAt (locate owner goods) person good = if owner = person then amount Good goods good else 0 := by
  by_cases equal : owner = person
  · subst owner
    simp only [flowAt, amount, locate, List.map_map, Function.comp_def, Prod.mk.injEq, true_and, if_true]
  · simp [flowAt, amount, locate, List.map_map, Function.comp_def, Prod.mk.injEq, equal]

omit [DecidableEq Port] [DecidableEq Instrument] in
private theorem nothing_to_debit (law : Law) (current : Raw) (request : RequestAt) (good : Good)
    (zero : ∀ person, current.stock person good = 0) (valid : law.Valid current request)
    (person : Party) : flowAt (law.debit current request) person good = 0 := by
  apply le_antisymm _ (amount_nonnegative _ valid.2.2.2.1 _)
  by_cases occurs : ∃ lot ∈ law.debit current request, lot.1 = (person, good)
  · obtain ⟨lot, listed, address⟩ := occurs
    have affordable := valid.2.2.2.2.2 lot listed
    rw [address, zero] at affordable
    exact affordable
  · exact (amount_zero_of_absent _ _ (fun lot listed equal => occurs ⟨lot, listed, equal⟩)).le

omit [DecidableEq Port] in
private theorem empty_stock_step (law : Law) (current : Raw) (request : RequestAt) (good : Good)
    (noOutput : ∀ tech person, amount Good (law.technique tech person).outputs good = 0)
    (zero : ∀ person, current.stock person good = 0) :
    ∀ person, (law.step current request).stock person good = 0 := by
  intro person
  by_cases valid : law.Valid current request
  · have debit := nothing_to_debit law current request good zero valid
    have noCredit : flowAt (law.credit current request) person good = 0 := by
      cases kind : request.operation with
      | produce operator =>
        simp [RawLaw.credit, kind, located_amount, noOutput]
      | transfer sender recipient goods =>
        have none := debit sender
        simp only [RawLaw.debit, kind, located_amount, if_true] at none
        simp [RawLaw.credit, kind, located_amount, none]
      | settle code debtor creditor quantity =>
        have none := debit debtor
        simp only [RawLaw.debit, kind, located_amount, if_true] at none
        simp [RawLaw.credit, kind, located_amount, none]
      | use | issue | assign | revise | present => simp [RawLaw.credit, kind, flowAt, amount]
    simp [RawLaw.step, valid, RawLaw.paidStep, zero, debit, noCredit]
  · rw [law.rejected_preserves_current current request valid, zero]

omit [DecidableEq Port] in
private theorem empty_stock_word (law : Law) (word : List RequestAt) (current : Raw) (index : Nat)
    (good : Good) (noOutput : ∀ tech person, amount Good (law.technique tech person).outputs good = 0)
    (zero : ∀ person, current.stock person good = 0) :
    ∀ person, (law.execute current index word).final.stock person good = 0 := by
  induction word generalizing current index with
  | nil => exact zero
  | cons request tail ih =>
    exact ih (law.step current request) (index + 1) (empty_stock_step law current request good noOutput zero)

omit [DecidableEq Port] in
private theorem empty_stock_programme (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (word : List (Compile.RawInput Party Good Port Technology Instrument))
    (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (good : Good) (noOutput : ∀ tech person,
      amount Good ((Physical.Public.interpreter input).technique tech person).outputs good = 0)
    (zero : ∀ person, before.raw.stock person good = 0) :
    ∀ person, (Optimality.Programme.run input before word).raw.stock person good = 0 := by
  induction word generalizing before with
  | nil => exact zero
  | cons proposal tail ih =>
    apply ih
    cases Physical.Public.compile input before proposal with
    | accepted word selected checked =>
      cases proposal <;> exact empty_stock_word (Physical.Public.interpreter input) word before.raw 0 good noOutput zero
    | refused => exact zero
    | metadata => exact zero

/-- An exhausted good with no output in any installed technique cannot
be replenished by any actual continuation, including revision, transfer,
financial settlement and pending-work execution. -/
theorem zero_original_stock_stays_zero_without_a_productive_source
    (origin : C) (good : Good)
    (noOutput : ∀ tech person,
      amount Good ((Physical.Public.interpreter origin.native.input).technique tech person).outputs good = 0)
    (zero : ∀ person, origin.raw.stock person good = 0) (continuation : Script) :
    ∀ person, (Execution.endAt origin continuation).raw.stock person good = 0 := by
  have physical := empty_stock_programme origin.native.input (Execution.programme origin continuation)
    (Evolving.Epoch.Source.originalState origin.native) good noOutput zero
  rw [Execution.physical_is_the_folded_actual_end] at physical
  exact physical

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
