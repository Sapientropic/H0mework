/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.Fixture.GeneratedSocialSpaceCrossing
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver

/-!
# M12 generated-flow observer fixture

Two observers read the same three exact M11 crossings into the same visible
type.  The coarse observer puts all crossings in one fibre.  The fine observer
keeps the recurrent false-state crossings together and moves the middle true
state to a second fibre.  Neither observer changes occurrence identity,
flow payload or source authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12GeneratedFlowObserverFixture

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Capacity Space Observer
open M10OccurrenceCapacityProcessFixture
open M11GeneratedSocialSpaceCrossingFixture

abbrev ExactCrossing := crossingCompiler.ExactCrossing

inductive Visible where
  | conditioned
  | outside
  deriving DecidableEq, Repr

/-- Exact position is retained as the authority residual hidden by both
observers on the recurrent pair. -/
def crossingAuthorityK (crossing : ExactCrossing) : Nat :=
  crossing.position.val

/-- Every exact crossing is placed in the common visible fibre. -/
def coarseObserver : AuthorityObserver ExactCrossing Visible Nat where
  forget := fun _crossing => .conditioned
  authorityK := crossingAuthorityK

/-- Exact source state controls the finer visible split.  The first and
recurrent occurrences share state `false`; the middle occurrence has state
`true`. -/
def fineObserver : AuthorityObserver ExactCrossing Visible Nat where
  forget := fun crossing =>
    if crossing.state = false then .conditioned else .outside
  authorityK := crossingAuthorityK

/-- Event whose probability will be observed: the exact first occurrence,
not every crossing with the same state or site gauge. -/
def firstOccurrenceEvent (crossing : ExactCrossing) : Prop :=
  crossing.position.val = firstPosition.val

instance firstOccurrenceEventDecidable (crossing : ExactCrossing) :
    Decidable (firstOccurrenceEvent crossing) := by
  unfold firstOccurrenceEvent
  infer_instance

@[simp] theorem coarse_first_visible :
    coarseObserver.forget firstCrossing = .conditioned :=
  rfl

@[simp] theorem coarse_middle_visible :
    coarseObserver.forget middleCrossing = .conditioned :=
  rfl

@[simp] theorem coarse_recurrent_visible :
    coarseObserver.forget recurrentCrossing = .conditioned :=
  rfl

@[simp] theorem fine_first_visible :
    fineObserver.forget firstCrossing = .conditioned :=
  rfl

@[simp] theorem fine_middle_visible :
    fineObserver.forget middleCrossing = .outside :=
  rfl

@[simp] theorem fine_recurrent_visible :
    fineObserver.forget recurrentCrossing = .conditioned :=
  rfl

@[simp] theorem event_first : firstOccurrenceEvent firstCrossing :=
  rfl

@[simp] theorem event_middle_not : ¬ firstOccurrenceEvent middleCrossing := by
  decide

@[simp] theorem event_recurrent_not :
    ¬ firstOccurrenceEvent recurrentCrossing := by
  decide

/-- The recurrent pair is one nontrivial authority kernel fibre for the
coarse observer. -/
def coarseKernelPair : AuthorityKernelPair coarseObserver where
  left := firstCrossing
  right := recurrentCrossing
  occurrence_ne :=
    SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
      recurrent_positions_are_distinct
  visible_eq := rfl
  authority_ne := by decide

/-- Refining away the middle occurrence does not make the conditioned fibre
faithful: the recurrent pair remains hidden. -/
def fineKernelPair : AuthorityKernelPair fineObserver where
  left := firstCrossing
  right := recurrentCrossing
  occurrence_ne :=
    SourceOwnedCrossingCompiler.ExactCrossing.ne_of_position_ne
      recurrent_positions_are_distinct
  visible_eq := rfl
  authority_ne := by decide

theorem coarse_no_authority_factorization :
    ¬ Nonempty (AuthorityFactorization coarseObserver) :=
  coarseKernelPair.noAuthorityFactorization

theorem fine_no_authority_factorization :
    ¬ Nonempty (AuthorityFactorization fineObserver) :=
  fineKernelPair.noAuthorityFactorization

/-- Same exact source, event and visible label; only kernel geometry changes. -/
theorem observer_geometry_only_change :
    firstOccurrenceEvent = firstOccurrenceEvent ∧
      (.conditioned : Visible) = .conditioned ∧
      coarseObserver.authorityK = fineObserver.authorityK :=
  ⟨rfl, rfl, rfl⟩

end
end M12GeneratedFlowObserverFixture
end Society
end ProcessGame
end SaturationMonoid
