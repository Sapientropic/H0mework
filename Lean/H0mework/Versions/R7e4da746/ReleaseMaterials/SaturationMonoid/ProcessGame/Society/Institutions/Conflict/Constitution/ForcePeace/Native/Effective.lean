import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Publication

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "L" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)
local notation "Input" => Reparation.Actual.Input Party Good Port (State Party Technology) Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port (State Party Technology) Instrument

/-- Read an effective withdrawal from the literal submitted request and
the original material receipt at its position on the same source path. -/
structure EffectiveRelease (base : L) (scope : J) (seed submitted : C) (actor : Party) (word : Word) where
  before : Word
  after : Word
  original : word = before ++ withdrawalInput scope submitted actor :: after
  receipt : ReleaseReceipt base scope submitted (endAt seed before) actor

namespace EffectiveRelease

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed submitted : Root.Cut Party Good Port (State Party Technology) Instrument} {actor : Party}
  {word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (effective : EffectiveRelease base scope seed submitted actor word)

def extend (tail : Word) : EffectiveRelease base scope seed submitted actor (word ++ tail) where
  before := effective.before
  after := effective.after ++ tail
  original := (congrArg (· ++ tail) effective.original).trans (by
    simp only [List.append_assoc, List.cons_append])
  receipt := effective.receipt

def ordinal := effective.before.length

def clock := (endAt seed effective.before).raw.clock

end EffectiveRelease

variable {base : RawLaw Party Good Port Technology Instrument}
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (past : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument) (actor : Party)
  (rival : Nat → Root.Cut Party Good Port (State Party Technology) Instrument →
    Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)

def effectiveReservation
    (paid : ReleaseReceipt base scope (endAt seed past) (atReservedVisit scope (endAt seed past) actor rival) actor) :
    EffectiveRelease base scope seed (endAt seed past) actor
      (past ++ reservation (endAt seed past) (withdrawalInput scope (endAt seed past) actor) rival) where
  before := past ++ queuedPrefix (endAt seed past) (withdrawalInput scope (endAt seed past) actor) rival
  after := []
  original := (List.append_assoc _ _ _).symm
  receipt := by rwa [endAt_append]

theorem the_paid_reservation_has_an_exact_latest_effective_visit
    (paid : ReleaseReceipt base scope (endAt seed past) (atReservedVisit scope (endAt seed past) actor rival) actor) :
    let written := effectiveReservation scope seed past actor rival paid
    written.ordinal = past.length + remainingNative (endAt seed past) ∧
      written.clock = (endAt seed past).raw.clock ∧
    ∀ earlier : Word, earlier.length < remainingNative (endAt seed past) →
      inventory (endAt seed past) earlier = [] := by
  refine ⟨?_, ?_, fun earlier short =>
    (all_native_interleavings_spend_the_same_backlog_without_material_effects _ earlier short.le).2.2.2⟩
  · simp only [EffectiveRelease.ordinal, effectiveReservation, List.length_append, queuedPrefix_length]
  · simp only [EffectiveRelease.clock, effectiveReservation, endAt_append]
    exact congrArg (·.clock)
      (the_first_material_visit_is_reserved_at_the_same_physical_cut (endAt seed past)
        (withdrawalInput scope (endAt seed past) actor) rival).2.1

theorem a_material_free_prefix_cannot_complete_a_post_submission_withdrawal (wait : Word)
    (materialFree : inventory (endAt seed past) wait = [])
    (effective : EffectiveRelease base scope seed (endAt seed past) actor (past ++ wait)) :
    effective.ordinal < past.length := by
  by_contra notBefore
  have prior : effective.before <+: past ++ wait := by
    exact Eq.mpr (congrArg (fun word : Word => effective.before <+: word) effective.original)
      (List.prefix_append _ _)
  have before : past <+: effective.before := List.prefix_of_prefix_length_le
    (List.prefix_append past wait) prior (Nat.le_of_not_gt notBefore)
  obtain ⟨native, added⟩ := before
  have whole := effective.original
  rw [← added, List.append_assoc] at whole
  have waitExact := List.append_cancel_left whole
  have item := effective.receipt.originalItem
  rw [← added, endAt_append] at item
  have empty := materialFree
  rw [waitExact, inventory_append] at empty
  change inventory (endAt seed past) native ++ inventory (endAt (endAt seed past) native)
    ([withdrawalInput scope (endAt seed past) actor] ++ effective.after) = [] at empty
  rw [inventory_append, item] at empty
  have impossible := (List.append_eq_nil_iff.mp empty).2
  simp at impossible

theorem a_native_only_prefix_cannot_complete_a_post_submission_withdrawal (wait : Word)
    (within : wait.length ≤ remainingNative (endAt seed past))
    (effective : EffectiveRelease base scope seed (endAt seed past) actor (past ++ wait)) :
    effective.ordinal < past.length :=
  a_material_free_prefix_cannot_complete_a_post_submission_withdrawal scope seed past actor wait
    (all_native_interleavings_spend_the_same_backlog_without_material_effects _ wait within).2.2.2 effective

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
