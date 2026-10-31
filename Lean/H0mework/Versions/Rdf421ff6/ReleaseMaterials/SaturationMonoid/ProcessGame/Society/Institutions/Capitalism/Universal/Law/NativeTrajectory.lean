import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.SamePath
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.CompleteWord
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.LocalRenewal

/-! One actual path, one common tail cut.  Control families are supplied by
the original relation producer.  The finite full-word check and actual needs
check are consumed here; this layer constructs no executor or relation. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.NativeTrajectory

open Source.Program Source.ProgrammeControl

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument)
  (members : RawCurrent Party Good Technology Instrument → List Party)
  (family : (n : Nat) → At program n → List Port)

/-- A missing requirement stays with its original current and member;
an empty requested word cannot manufacture a payment. -/
def UnpaidAt (n : Nat) : Prop :=
  ∃ person ∈ members (program.currentAt n),
    ¬ Exit.Necessity.BundlePaid program.law (program.currentAt n)
      (program.emit (program.currentAt n)) person
      (program.law.necessities (program.currentAt n) person) .necessity ∨
    ¬ Exit.Necessity.BundlePaid program.law (program.currentAt n)
      (program.emit (program.currentAt n)) person
      (program.law.mandatoryMaintenance (program.currentAt n) person) .maintenance

/-- Unrecognized exclusion, refusal and missing livelihood are different
reasons with their original witnesses; none is renamed necessary control. -/
def ResidualAt (n : Nat) : Prop :=
  Nonempty (UnresolvedItem program.law (program.currentAt n)
    (program.emit (program.currentAt n)) (family n) (members (program.currentAt n))) ∨
  UnpaidAt program members n

/-- The alternative is literally the word returned by the same finite
joint authorization and needs checks, not a word sharing its endpoint. -/
def PaidIndependentAt (n : Nat) : Prop :=
  ∃ programme : PortIndependent program.law (program.currentAt n)
      (program.emit (program.currentAt n)) (family n) (members (program.currentAt n)),
    Exit.LocalRenewal.attempt program members (program.currentAt n) =
      some programme.alternative ∧
    Exit.Necessity.AllNeedsPaid program.law (program.currentAt n)
      (members (program.currentAt n)) programme.alternative

def PaidControlFreeTail (start : Nat) : Prop :=
  Exit.LocalRenewal.PaidTail program members start ∧
  ∀ offset, PaidIndependentAt program members family (start + offset)

omit [DecidableEq Port] in
theorem unpaid_iff_missing_needs (n : Nat) :
    UnpaidAt program members n ↔
      ¬ Exit.Necessity.AllNeedsPaid program.law (program.currentAt n)
        (members (program.currentAt n)) (program.emit (program.currentAt n)) := by
  classical
  unfold UnpaidAt Exit.Necessity.AllNeedsPaid
  simp only [not_forall, not_and, exists_prop, or_iff_not_imp_left, not_not]

/-- The existing complete finite classifier is the sole source of the
control / unresolved / independent branches. -/
theorem actual_current_classification (n : Nat) :
    ActualControlAt program family n ∨
      ResidualAt program members family n ∨
      PaidIndependentAt program members family n := by
  classical
  cases classifyComplete program.law (program.currentAt n)
      (program.emit (program.currentAt n)) (family n) (members (program.currentAt n)) with
  | controlled use => exact Or.inl ⟨use⟩
  | unresolved item => exact Or.inr (Or.inl (Or.inl ⟨item⟩))
  | independent programme =>
      by_cases paid : Exit.Necessity.AllNeedsPaid program.law (program.currentAt n)
          (members (program.currentAt n)) (program.emit (program.currentAt n))
      · right; right
        refine ⟨programme, ?_, ?_⟩
        · simpa only [Exit.LocalRenewal.attempt, if_pos paid] using programme.generated
        · exact Exit.Necessity.allNeedsPaid_jointWord program.law (program.currentAt n)
            (members (program.currentAt n)) _ _ programme.generated paid
      · exact Or.inr (Or.inl (Or.inr ((unpaid_iff_missing_needs program members n).mpr paid)))

theorem cleared_tail_generates_paid_continuation (start : Nat)
    (controlFree : ∀ n ≥ start, ¬ ActualControlAt program family n)
    (clear : ∀ n ≥ start, ¬ ResidualAt program members family n) :
    PaidControlFreeTail program members family start := by
  have eachPaid : ∀ offset, PaidIndependentAt program members family (start + offset) := by
    intro offset
    rcases actual_current_classification program members family (start + offset) with
      control | residual | paid
    · exact False.elim (controlFree _ (by omega) control)
    · exact False.elim (clear _ (by omega) residual)
    · exact paid
  refine ⟨Exit.LocalRenewal.successful_tail_generated program members start ?_, eachPaid⟩
  intro offset
  obtain ⟨programme, generated, _paid⟩ := eachPaid offset
  rw [generated]
  exact Option.some_ne_none _

/-- All original items, all current members and all their source bundles
share this one cutoff.  Refusal of an optional instruction stays in the
residual branch and cannot establish a livelihood-dependence theorem. -/
theorem control_or_original_residual_or_paid_control_free_tail :
    Recurrently (ActualControlAt program family) ∨
      Recurrently (ResidualAt program members family) ∨
      ∃ start, PaidControlFreeTail program members family start := by
  classical
  by_cases control : Recurrently (ActualControlAt program family)
  · exact Or.inl control
  · right
    by_cases residual : Recurrently (ResidualAt program members family)
    · exact Or.inl residual
    · right
      unfold Recurrently at control residual
      push Not at control residual
      obtain ⟨afterControl, noControl⟩ := control
      obtain ⟨afterResidual, noResidual⟩ := residual
      refine ⟨max afterControl afterResidual,
        cleared_tail_generates_paid_continuation program members family _ ?_ ?_⟩
      · intro n after
        exact noControl n (le_trans (le_max_left _ _) after)
      · intro n after
        exact noResidual n (le_trans (le_max_right _ _) after)

/-- The quantified absence concerns every tail of this same actual path.
It does not substitute an initial-state inability or a hostile strategy. -/
theorem absence_of_paid_control_free_tail_forces_recurrence
    (noTail : ∀ start, ¬ PaidControlFreeTail program members family start) :
    Recurrently (ActualControlAt program family) ∨
      Recurrently (ResidualAt program members family) := by
  rcases control_or_original_residual_or_paid_control_free_tail program members family with
    control | residual | ⟨start, tail⟩
  · exact Or.inl control
  · exact Or.inr residual
  · exact False.elim (noTail start tail)

omit [DecidableEq Port] in
theorem paid_tail_has_no_original_control (start : Nat)
    (tail : PaidControlFreeTail program members family start) :
    ∀ offset, ∀ item : At program (start + offset),
      program.law.Valid item.val.before item.val.request ∧
        ∀ port ∈ program.law.requiredPorts item.val.before item.val.request,
          port ∉ family (start + offset) item := by
  intro offset item
  obtain ⟨programme, _generated, _paid⟩ := tail.2 offset
  exact ⟨programme.originalValid item, programme.noControl item⟩

#print axioms control_or_original_residual_or_paid_control_free_tail
#print axioms absence_of_paid_control_free_tail_forces_recurrence

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.NativeTrajectory
