import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term.Native
import Mathlib.Data.EReal.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term

open Source.Program PublicFunction PublicFunction.Mandate
open OutstandingSource.History.NativeService

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

theorem Issue.refutes {bound : BoundSource base scope} {past suffix : Inputs}
    (issue : Issue bound past suffix) : ¬ PaidAt bound past suffix := by
  intro paid
  cases issue with
  | service slot live =>
      have unpaid := ((serviceThread bound past suffix slot).native_live_iff_unpaid bound.source).mp live
      obtain ⟨ordinal, retired⟩ :=
        ((serviceThread bound past suffix slot).native_terminal_iff_recorded bound.source).mp (paid.slots slot)
      rw [unpaid] at retired
      cases retired
  | overlap short => exact short.ne paid.distinctDebits
  | authority active => exact active paid.closed

theorem every_candidate_preserves_its_original_current_and_service_rows
    (bound : BoundSource base scope) (past suffix : Inputs) :
    OutstandingSource.History.currentAt bound.source (past ++ suffix) (past.length + 2) =
      target bound past [] ∧
    ∀ slot, type_of% ((serviceThread bound past suffix slot).original_obligation_is_retained bound.source) := by
  constructor
  · unfold target
    simp only [List.append_nil]
    rw [(OutstandingSource.History.actual_frame bound.source (past ++ suffix) (past.length + 2)).1,
      (OutstandingSource.History.actual_frame bound.source past (past.length + 2)).1,
      OutstandingSource.History.extending_inputs_preserves_its_executed_prefix bound.source past suffix
        (past.length + 2) (Nat.le_refl _)]
  · intro slot
    exact (serviceThread bound past suffix slot).original_obligation_is_retained bound.source

def readClock (bound : BoundSource base scope) (past suffix : Inputs) : EReal :=
  (((target bound past suffix).clock : ℝ) : EReal)

def times (bound : BoundSource base scope) (past : Inputs) : Set EReal :=
  fun time => ∃ suffix : Inputs, PaidAt bound past suffix ∧ readClock bound past suffix = time

inductive Resolution (bound : BoundSource base scope) (past : Inputs) : Prop
  | attained (suffix : Inputs) (completed : PaidAt bound past suffix)
      (exactCut : readClock bound past suffix = sInf (times bound past))
  | approached (nonempty : (times bound past).Nonempty) (notReached : sInf (times bound past) ∉ times bound past)
      (actual : ∀ deadline, sInf (times bound past) < deadline →
        ∃ suffix : Inputs, PaidAt bound past suffix ∧ readClock bound past suffix < deadline)
  | blocked (issues : ∀ suffix : Inputs, Nonempty (Issue bound past suffix))

/-- The tight actual termination time includes distinct service and the
actual end of holder/offer authority, all from this original past. -/
theorem the_original_mandate_resolves_its_paid_completion_and_release_deadline
    (bound : BoundSource base scope) (past : Inputs) :
    IsGLB (times bound past) (sInf (times bound past)) ∧ Resolution bound past := by
  classical
  refine ⟨isGLB_sInf _, ?_⟩
  by_cases attained : sInf (times bound past) ∈ times bound past
  · obtain ⟨suffix, paid, exactTime⟩ := attained
    exact .attained suffix paid exactTime
  by_cases feasible : (times bound past).Nonempty
  · refine .approached feasible attained ?_
    intro deadline looser
    obtain ⟨time, ⟨suffix, paid, rfl⟩, onTime⟩ := sInf_lt_iff.mp looser
    exact ⟨suffix, paid, onTime⟩
  · refine .blocked fun suffix => ?_
    cases decide bound past suffix with
    | blocked issue => exact ⟨issue⟩
    | paid actual => exact (feasible ⟨_, suffix, actual, rfl⟩).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term
