import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Engine
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SourceNativeInquiryRuntime
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "current" => actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
local notation "actualRun" => run (review := review) input depth sourceStart datum prefixLimit renewalLimit reader

theorem actual_internal_fold_is_the_same_registered_history (tick steps : Nat) :
    ActivatedFrame.after (current tick) steps = current (tick + steps) := by
  induction steps with
  | zero => rfl
  | succ steps inherited => rw [ActivatedFrame.after_succ, inherited]; rfl

def internalBoundaryTick (tick : Nat) : Nat := tick + (current tick).complete.steps

def actualInternalBoundary (tick : Nat) : ActivatedFrame.BoundaryAt
    (current (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)) := by
  rw [internalBoundaryTick, ← actual_internal_fold_is_the_same_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick _]
  exact (current tick).boundary

theorem every_actual_current_reaches_its_first_internal_boundary (tick : Nat) :
    (current tick).complete.steps ≤ (current tick).internalMass ∧
    (current (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)).internalMass = 0 ∧
    ∀ index < (current tick).complete.steps, 0 < (current (tick + index)).internalMass := by
  have first := ActivatedFrame.completion_is_the_first_actual_raw_boundary (current tick)
  refine ⟨(current tick).complete.within, ?_, ?_⟩
  · rw [internalBoundaryTick, ← actual_internal_fold_is_the_same_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick _]
    exact (current tick).complete.finished
  · intro index before
    rw [← actual_internal_fold_is_the_same_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick _]
    exact first.2 index before

def actualInternalNative (tick : Nat) :
    (Epoch.Finance.process input depth (Ingress.cut input depth sourceStart)).Run
      (current tick).account.current
      (current (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)).account.current := by
  rw [internalBoundaryTick, ← actual_internal_fold_is_the_same_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick _]
  exact ActivatedFrame.afterNative (current tick) (current tick).complete.steps

theorem the_internal_boundary_is_visited_by_the_original_engine (tick : Nat) :
    (actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1)).engine.node =
      .active (current (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick)).presentation :=
  run_is_the_original_registered_history (review := review) input depth sourceStart datum prefixLimit renewalLimit reader _

theorem the_boundary_action_is_the_next_original_engine_occurrence (tick : Nat) :
    (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
      (actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1))).next.engine.node =
      .active (current (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1)).presentation :=
  actual_next (review := review) input depth sourceStart datum prefixLimit renewalLimit reader _ _
    (the_internal_boundary_is_visited_by_the_original_engine (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick) _

theorem the_boundary_action_preserves_the_whole_root_and_generates_next (tick : Nat) :
    (actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1)).engine.node.PreservesGeneratedLivingLawAt
      ((actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1)).engine.registeredInquiryActivation
        (event (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
          (actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1))).input).query
      (advance (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
        (actualRun (internalBoundaryTick (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick + 1))).engine.node :=
  each_actual_attempt_has_the_original_complete_next (review := review) input depth sourceStart datum prefixLimit renewalLimit reader _

#print axioms actualInternalBoundary
#print axioms every_actual_current_reaches_its_first_internal_boundary
#print axioms actualInternalNative
#print axioms the_boundary_action_is_the_next_original_engine_occurrence
#print axioms the_boundary_action_preserves_the_whole_root_and_generates_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
