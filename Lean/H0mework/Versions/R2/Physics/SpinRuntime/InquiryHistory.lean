import H0mework.Versions.R2.Physics.Revision.InquiryHistory
import H0mework.Versions.R2.Physics.SpinRuntime.InquiryPrograms
import H0mework.Versions.R2.Physics.Actual.RuntimeInquiry
import H0mework.Versions.R2.Physics.QuantumRuntime.Inquiry

/-! The six generated historical activations lead to the spin-pair action
at the same material occurrence. New visits are distinguished by their actual
initial support, which is already a qualified material state. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootU7AnswerNext
open StageTenPhysicalRoot

noncomputable section

def historicalState : Fin 7 → MacroState :=
  ![.original 0, .original 1, .original 2, .cartanAction, .material 0, .material 1, .material 2]

def historicalPresentation (index : Fin 7) : RootInquiryStatePresentation :=
  if index = 6 then inquiryPresentation else macroPresentation (historicalState index)

theorem historicalPresentation_erase (index : Fin 7) :
    (historicalPresentation index).erase = (macroPresentation (historicalState index)).erase := by
  fin_cases index <;> rfl

private theorem historicalState_injective : Function.Injective historicalState := by
  intro left right equality
  fin_cases left <;> fin_cases right <;> cases equality <;> rfl

private theorem visit_depth (n : Nat) : temporalDepth (visit n).history = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp only [visit]
      exact (temporalDepth_next (visit n).history _).trans (congrArg (· + 1) ih)

private theorem read_depth (n : Nat) : erasedDepth (readPresentation n).erase = n + 1 :=
  visit_depth (n + 1)

private def InitiallyQualified (value : AnyAuthoritativeRootCurrent) : Prop :=
  ∃ identifies : value.N.Support = MaterialSupport, ∃ state : MaterialState,
    (identifies ▸ value.current.root.toRoot.supportAt
      value.current.root.toRoot.source.initial) = .inr state

private theorem read_initiallyQualified (n : Nat) :
    InitiallyQualified (readPresentation n).erase := ⟨rfl, _, rfl⟩

private theorem material_not_initiallyQualified (n : Nat) :
    ¬ InitiallyQualified (materialInquiryPresentation n).erase := by
  rintro ⟨identifies, state, equality⟩
  have identifies_eq : identifies = rfl := Subsingleton.elim _ _
  cases identifies_eq
  cases equality

private theorem read_initiallySettled (n : Nat) :
    InitiallySettled (readPresentation n).erase := by
  refine ⟨rfl, ?_⟩
  intro responsibility opened
  change MaterialOpenAt (.inr _) responsibility at opened
  cases opened.exact
  rfl

private theorem old_ne_read (state : MacroState) (n : Nat) :
    (macroPresentation state).erase ≠ (readPresentation n).erase := by
  intro equality
  cases state with
  | original index =>
      exact old_not_initiallySettled (physicalRuntimeVisit index)
        ((congrArg InitiallySettled equality).mpr (read_initiallySettled n))
  | cartanAction =>
      exact old_not_initiallySettled afterGravityTemporalVisit
        ((congrArg InitiallySettled equality).mpr (read_initiallySettled n))
  | material index =>
      exact material_not_initiallyQualified index
        ((congrArg InitiallyQualified equality).mpr (read_initiallyQualified n))

inductive RuntimeState
  | history (index : Fin 7)
  | native (index : Nat)

def runtimePresentation : RuntimeState → RootInquiryStatePresentation
  | .history index => historicalPresentation index
  | .native 0 => readPresentation 0
  | .native 1 => Stage9CU.Runtime.weakPresentation 1
  | .native 2 => readPresentation 2
  | .native (index + 3) => Stage9DEF.Runtime.quantumPresentation (index + 3)

theorem runtimePresentation_native_erase (index : ℕ) :
    (runtimePresentation (.native index)).erase = (readPresentation index).erase := by
  rcases index with _ | _ | _ | index <;> rfl

theorem runtimePresentation_erase_injective :
    Function.Injective (fun state => (runtimePresentation state).erase) := by
  intro left right equality
  cases left with
  | history i =>
      cases right with
      | history j =>
          change (historicalPresentation i).erase = (historicalPresentation j).erase at equality
          rw [historicalPresentation_erase, historicalPresentation_erase] at equality
          exact congrArg RuntimeState.history
            (historicalState_injective (macroPresentation_erase_injective equality))
      | native j =>
          change (historicalPresentation i).erase =
            (runtimePresentation (.native j)).erase at equality
          rw [historicalPresentation_erase, runtimePresentation_native_erase] at equality
          exact False.elim (old_ne_read (historicalState i) j equality)
  | native i =>
      cases right with
      | history j =>
          change (runtimePresentation (.native i)).erase =
            (historicalPresentation j).erase at equality
          rw [historicalPresentation_erase, runtimePresentation_native_erase] at equality
          exact False.elim (old_ne_read (historicalState j) i equality.symm)
      | native j =>
          change (runtimePresentation (.native i)).erase =
            (runtimePresentation (.native j)).erase at equality
          rw [runtimePresentation_native_erase, runtimePresentation_native_erase] at equality
          have depths := congrArg erasedDepth equality
          change erasedDepth (readPresentation i).erase = erasedDepth (readPresentation j).erase at depths
          rw [read_depth, read_depth] at depths
          exact congrArg RuntimeState.native (Nat.add_right_cancel depths)

end
end SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair
