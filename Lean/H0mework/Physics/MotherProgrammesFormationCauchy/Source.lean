import H0mework.Physics.QuantumFoundation.RuntimeOccurrence
import H0mework.Physics.Cauchy.GeneratedMotherTimeCauchyFlow
import H0mework.Realization.SourceComparison.RawConsumption

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PhysicalCoverage

open StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineCanonicalCauchyState
open StageNineSourceGeneratedMotherTimeCauchyFlow
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot


noncomputable section

abbrev source := Stage9G.Runtime.source

/-- Complete primitive data and the original mother-connection time-axis transport clock. -/
abbrev Current := StageNineCauchyState × ℝ
abbrev Duration := {elapsed : ℝ // 0 < elapsed}

/-- The source's internal color transport acts on the whole state. Its
transport parameter remains distinct from the chosen Cauchy slice time. -/
def advance (current : Current) (elapsed : ℝ) : Current :=
  (sourceGeneratedMotherTimeCauchyUpdate source elapsed current.1, current.2 + elapsed)

/-- Initial local data remain explicit. The unit-transport emitter is a finite
source rule, not a supplied future. This mathematical root is not a runtime installation. -/
def dynamics (initial : StageNineCauchyState) : RawGeneratedRoot.Dynamics where
  State := Current
  EventAt := fun _ => Duration
  initial := (initial, 0)
  emit := fun _ => ⟨1, by norm_num⟩
  update := fun {current} elapsed => advance current elapsed.val

/-- The default local data are read from the original configuration's fixed zero slice. -/
def originalInitial : StageNineCauchyState :=
  canonicalCauchyRestriction 0 Stage9G.Runtime.configuration

def realization (initial : StageNineCauchyState) := RawGeneratedRoot.realization (dynamics initial)

theorem elapsed_recovered (current : Current) (elapsed : ℝ) :
    (advance current elapsed).2 - current.2 = elapsed := by
  simp [advance]

theorem update_event_injective (current : Current) : Function.Injective (advance current) := by
  intro first last same
  exact add_left_cancel (congrArg Prod.snd same)

theorem chronological_progress (current : Current) (elapsed : Duration) :
    current.2 < (advance current elapsed.val).2 := lt_add_of_pos_right _ elapsed.property

theorem advance_inverse (current : Current) (elapsed : ℝ) :
    advance (advance current elapsed) (-elapsed) = current := by
  apply Prod.ext
  · exact sourceGeneratedMotherTimeCauchyUpdate_left_inverse source elapsed current.1
  · simp [advance]

theorem generated_current (initial : StageNineCauchyState) (index : ℕ) :
    RawGeneratedRoot.currentAt (dynamics initial) index =
      (sourceGeneratedMotherTimeCauchyUpdate source (index : ℝ) initial, (index : ℝ)) := by
  induction index with
  | zero => simp [RawGeneratedRoot.currentAt, dynamics]
  | succ index previous =>
    change advance (RawGeneratedRoot.currentAt (dynamics initial) index) 1 = _
    rw [previous]
    apply Prod.ext
    · change sourceGeneratedMotherTimeCauchyUpdate source 1
        (sourceGeneratedMotherTimeCauchyUpdate source (index : ℝ) initial) = _
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        (sourceGeneratedMotherTimeCauchyUpdate_add source 1 (index : ℝ) initial).symm
    · simp [advance, Nat.cast_add]

/-- The full-fibre consumer includes all positive durations, including
non-emitted ones, with their actual updates and row transfers. -/
theorem event_consumed (initial : StageNineCauchyState) (current : Current) (elapsed : Duration) :
    (RawGeneratedRoot.eventPresentation (dynamics initial) current).backward
        ((RawGeneratedRoot.eventPresentation (dynamics initial) current).forward elapsed) = elapsed ∧
      (RawGeneratedRoot.generatedSuccessor (dynamics initial) (state := current) elapsed).targetCurrent =
        advance current elapsed.val ∧
      (RawGeneratedRoot.generatedSuccessor (dynamics initial) (state := current) elapsed).ledgerEvolution.destination
          (RawGeneratedRoot.entry (dynamics initial) current) =
        ⟨RawGeneratedRoot.entry (dynamics initial) (advance current elapsed.val),
          .transferred elapsed rfl rfl (Nat.le_refl _)⟩ :=
  (RawGeneratedRoot.every_raw_dynamics_realized (dynamics initial)).2.1 current elapsed

theorem visit_generated (initial : StageNineCauchyState) (index : ℕ) :
    (RawGeneratedRoot.visitAt (dynamics initial) index).current =
      (sourceGeneratedMotherTimeCauchyUpdate source (index : ℝ) initial, (index : ℝ)) :=
  (RawGeneratedRoot.visit_current (dynamics initial) index).trans (generated_current initial index)

theorem generated_next (initial : StageNineCauchyState)
    (visit : GroundedFaithfulRealization.Visit (RawGeneratedRoot.root (dynamics initial))) :
    (RawGeneratedRoot.root (dynamics initial)).generatedNextCurrentAt visit =
      ⟨RawGeneratedRoot.vocabulary (dynamics initial), (RawGeneratedRoot.root (dynamics initial)).toAuthoritativeRoot,
        visit.next (next := advance visit.current 1) rfl⟩ :=
  RawGeneratedRoot.next_current (dynamics initial) visit

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.PhysicalCoverage
