import H0mework.Versions.R2.Probability.Source.Field
import H0mework.Realization.HilbertTransfer.Chain
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual source empirical measures feed the shared complete Hilbert transfer and history fold. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOwnedObservationHistory

open MeasureTheory

noncomputable section

universe u

variable {State B : Type u} [AddCommGroup B]
variable (step : State → State) (read : State → B)

local instance : MeasurableSpace (Field step read) := fieldBorel step read

abbrev Space (state : State) (bound : Nat) :=
  Lp ℂ 2 (empirical step read state bound).toMeasure

theorem source_measurePreserving (state : State) (bound : Nat) :
    MeasurePreserving (fieldAction step read) (empirical step read state bound).toMeasure
      (empirical step read (step state) bound).toMeasure :=
  ⟨fieldAction_measurable step read,
    congrArg ProbabilityMeasure.toMeasure (empirical_map step read state bound)⟩

def pullback (state : State) (bound : Nat) :
    Space step read (step state) bound →ₗᵢ[ℂ] Space step read state bound :=
  Lp.compMeasurePreservingₗᵢ ℂ (fieldAction step read) (source_measurePreserving step read state bound)

theorem pullback_ae (state : State) (bound : Nat) (value : Space step read (step state) bound) :
    pullback step read state bound value =ᵐ[(empirical step read state bound).toMeasure]
      value ∘ fieldAction step read :=
  Lp.coeFn_compMeasurePreserving value (source_measurePreserving step read state bound)

abbrev ResidualSpace (state : State) (bound : Nat) :=
  IsometricRetainedTransfer.ResidualSpace (pullback step read state bound)

def retainedUpdate (state : State) (bound : Nat) :
    Space step read state bound ≃ₗ[ℂ]
      Space step read (step state) bound × ResidualSpace step read state bound :=
  IsometricRetainedTransfer.retainedUpdate (pullback step read state bound)

theorem retainedUpdate_energy (state : State) (bound : Nat) (value : Space step read state bound) :
    ‖value‖ ^ 2 = ‖(retainedUpdate step read state bound value).1‖ ^ 2 +
      ‖(retainedUpdate step read state bound value).2‖ ^ 2 :=
  IsometricRetainedTransfer.retainedUpdate_energy (pullback step read state bound) value

def advance (state : State) : Nat → State
  | 0 => state
  | depth + 1 => step (advance state depth)

theorem advance_eq_iterate (state : State) (depth : Nat) :
    advance step state depth = step^[depth] state := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
      exact (congrArg step previous).trans (Function.iterate_succ_apply' step depth state).symm

def stagePullback (state : State) (bound depth : Nat) :
    Space step read (advance step state (depth + 1)) bound →ₗᵢ[ℂ]
      Space step read (advance step state depth) bound :=
  pullback step read (advance step state depth) bound

abbrev Inventory (state : State) (bound depth : Nat) :=
  IsometricRetainedTransfer.Chain.Inventory
    (H := fun index => Space step read (advance step state index) bound)
    (stagePullback step read state bound) depth

def retainedHistory (state : State) (bound depth : Nat) :
    Space step read state bound ≃ₗ[ℂ]
      Space step read (advance step state depth) bound × Inventory step read state bound depth :=
  IsometricRetainedTransfer.Chain.retainedHistory
    (H := fun index => Space step read (advance step state index) bound)
    (stagePullback step read state bound) depth

abbrev inventoryEnergy (state : State) (bound depth : Nat) :
    Inventory step read state bound depth → ℝ :=
  IsometricRetainedTransfer.Chain.inventoryEnergy
    (H := fun index => Space step read (advance step state index) bound)
    (stagePullback step read state bound) depth

theorem retainedHistory_energy (state : State) (bound depth : Nat) (value : Space step read state bound) :
    ‖value‖ ^ 2 = ‖(retainedHistory step read state bound depth value).1‖ ^ 2 +
      inventoryEnergy step read state bound depth (retainedHistory step read state bound depth value).2 :=
  IsometricRetainedTransfer.Chain.retainedHistory_energy
    (H := fun index => Space step read (advance step state index) bound)
    (stagePullback step read state bound) depth value

end
end SourceOwnedObservationHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
