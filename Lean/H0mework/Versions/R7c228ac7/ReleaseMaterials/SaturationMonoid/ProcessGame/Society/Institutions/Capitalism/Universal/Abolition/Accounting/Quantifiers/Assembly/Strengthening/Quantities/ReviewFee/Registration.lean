import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Payment
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Commands.Review

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolving.Epoch
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Code" => ReviewSource.Control.Code Party Good Port Technology Instrument

def registration (source : C) (code : Code) := Execution.next source (some (.review code))

abbrev CanRegister (source : C) :=
  boundary (Public.Scope.checkInput source.native.input)
    (Actual.origin source.native.input source.native.depth source.native.count) source.members source.native.depth
    source.native.count source.native.prefixLimit source.native.renewalLimit source.state

theorem registration_preserves_the_actual_source_and_installs_the_original_fee
    (source : C) (code : Code) (ready : ¬ Pending source) (unregistered : source.control.review = none)
    (admitted : CanRegister source) :
    let installed := registration source code
    installed.raw = source.raw ∧ ¬ Pending installed ∧
      installed.control.review = some (ReviewCursor.initial code source.native.prefixLimit source.native.renewalLimit) := by
  let query := Execution.query source (some (.review code))
  have noReview : query.control.review = none :=
    (congrArg Control.review (source.requery_keeps_control_and_complete_account (fun _ _ => .review code)).1).trans unregistered
  have registered : CanRegister query := by
    have unchanged : query.control = source.control :=
      (source.requery_keeps_control_and_complete_account (fun _ _ => .review code)).1
    unfold CanRegister Current.state
    rw [unchanged]
    exact admitted
  have readyAt : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual := ready
  change query.advance.raw = source.raw ∧ ¬ Pending query.advance ∧ query.advance.control.review = _
  rw [query.advance_eq_epoch readyAt]
  refine ⟨?_, query.the_actual_review_registration_is_ready_for_its_own_next_query code rfl noReview registered readyAt, ?_⟩
  · rw [Transition.next_state_reads_the_same_actual_material_target query readyAt, Current.physicalResult,
      query.review_execution_is_the_original_registration code rfl noReview registered]
    rfl
  · rw [Transition.next_reads_the_written_control, query.review_installs_only_the_original_finite_code code rfl noReview registered]
    rfl

private theorem select_live_review (source : C)
    (control : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (cursor : ReviewCursor (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (installed : control.review = some cursor) (noRecourse : cursor.recourse = false) :
    select (Public.Scope.checkInput source.native.input)
      (Actual.origin source.native.input source.native.depth source.native.count) source.raw source.members
      source.native.depth source.native.count source.native.prefixLimit source.native.renewalLimit
      control source.proposal =
    .reviewing cursor installed (Review.compile (Public.Scope.checkInput source.native.input)
      (Actual.origin source.native.input source.native.depth source.native.count) source.raw source.members cursor) := by
  cases control with
  | mk phase remaining original =>
    change original = some cursor at installed
    subst original
    simp only [select, noRecourse, Bool.false_eq_true, if_false]

theorem a_registered_positive_fee_is_selected_at_its_own_review_cut
    (source : C) (code : Code) (prefixLimit renewalLimit : Nat)
    (scope : Abolition.Review.FeeScope code.fee)
    (installed : source.control.review = some (ReviewCursor.initial code prefixLimit renewalLimit)) :
    ∃ chosen, selected? source = some chosen ∧ chosen.fee.scope.amount = scope.amount ∧
      chosen.fee.scope.payer = scope.payer ∧ chosen.fee.scope.good = scope.good := by
  let cursor := ReviewCursor.initial code prefixLimit renewalLimit
  have candidate : ([], []) ∈ code.candidates prefixLimit renewalLimit :=
    (code.candidates_are_exactly_the_original_finite_code _ _ _).mpr (by simp)
  obtain ⟨parsedScope, parsed⟩ := ReviewSource.Fees.every_positive_original_fee_is_recognized scope
  have same : parsedScope.amount = scope.amount ∧ parsedScope.payer = scope.payer ∧ parsedScope.good = scope.good := by
    have operation := parsedScope.operation.symm.trans scope.operation
    injection operation with payer goods
    have goodAmount := List.cons.inj goods |>.1
    exact ⟨congrArg Prod.snd goodAmount, payer, congrArg Prod.fst goodAmount⟩
  have observed : source.choice = .reviewing cursor installed (.fee parsedScope parsed) := by
    have noRecourse : cursor.recourse = false := by
      have nonempty : code.candidates prefixLimit renewalLimit ≠ [] :=
        fun none => List.not_mem_nil (none ▸ candidate)
      simp only [cursor, ReviewCursor.initial, ReviewCursor.recourse, Bool.false_or, Option.isNone_none,
        Bool.and_true, List.isEmpty_eq_false_iff]
      exact nonempty
    unfold Current.choice
    rw [select_live_review source source.control cursor installed noRecourse]
    congr 1
    unfold Review.compile
    have exhausted : cursor.remaining ≠ [] := by
      intro none
      change code.candidates prefixLimit renewalLimit = [] at none
      exact List.not_mem_nil (none ▸ candidate)
    have fee : ReviewSource.Fees.scope? cursor.code.fee = some parsedScope := parsed
    simp only [show cursor.halted = false from rfl, Bool.false_eq_true, dite_false]
    split
    · contradiction
    · split
      · rename_i empty
        exact (exhausted empty).elim
      · simp only [show cursor.feePaid = false from rfl, Bool.false_eq_true, if_false]
        split
        · rename_i absent
          have impossible := fee.symm.trans absent
          cases impossible
        · rename_i actual seen
          have exactScope := Option.some.inj (seen.symm.trans fee)
          subst actual
          rfl
  obtain ⟨chosen, exactChoice, amount, payer, good⟩ :=
    the_installed_fee_choice_generates_its_own_quantified_payment source cursor installed parsedScope parsed observed
  exact ⟨chosen, exactChoice, amount.trans same.1, payer.trans same.2.1, good.trans same.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee
