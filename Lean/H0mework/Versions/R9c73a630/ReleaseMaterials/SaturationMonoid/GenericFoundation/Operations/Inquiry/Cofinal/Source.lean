import H0mework.Realization.Completion.ProcessDiagram
import H0mework.Versions.R2.Realization.Operations.Inquiry.Source
import H0mework.Realization.Operations.Substitution.Complex
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInquiryCofinalDiagram
open RootInquiryCompletion CategoryTheory SourceOperationEffects SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalProcessDiagram
variable {process : SourceNativeInquiryEngineProcess.{u}} (runtime : SourceNativeInquiryRuntime process)
abbrev Value (_ : PUnit.{u+14}) := SourceOperationInquiry.Carrier runtime
abbrev Var (_ : PUnit.{u+14}) := PUnit.{u+14}
abbrev PairedValue := PairValue (Value runtime)
def environment (state : runtime.State) : Env (PairedValue runtime) Var :=
 fun _ _ => (SourceOperationInquiry.point runtime state,
 SourceOperationInquiry.point runtime state.tick.nextState - SourceOperationInquiry.point runtime state)
def binding : ∀ sort, Var sort → Expr (PairedValue runtime) Var sort :=
 fun sort name => .linear (s := sort) (t := sort)
 (pairLinear (SourceOperationInquiry.sourceAction runtime).toAddMonoidHom) (.var name)

theorem actual_environment (state : runtime.State) :
 SourceSubstitution.sourceEnvironment (binding runtime) (environment runtime state) =
 environment runtime state.tick.nextState := by
 funext sort name
 apply Prod.ext
 · exact SourceOperationInquiry.point_action runtime state
 · exact (map_sub (SourceOperationInquiry.sourceAction runtime) _ _).trans
    (congrArg₂ (· - ·) (SourceOperationInquiry.point_action runtime state.tick.nextState)
      (SourceOperationInquiry.point_action runtime state))

abbrev object (state : runtime.State) := presentationComplex (R := ℤ) (s := PUnit.unit) (environment runtime state)
def transition (state : runtime.State) : object runtime state.tick.nextState ⟶ object runtime state := by
 unfold object
 rw [← actual_environment runtime state]
 exact SourceSubstitution.complexMorphism (R := ℤ) (binding runtime) (environment runtime state)

def localProcess : CofinalDiagramSuccessorProcessAt (ShortComplex (ModuleCat.{u+13} ℤ)) where
 State := runtime.State
 seed := runtime.initialState
 next := SourceOperationInquiry.nextState runtime
 object := object runtime
 transition := transition runtime

theorem generated_state (count : Nat) : (localProcess runtime).stateAt count = runtime.stateAt count := by
 induction count with
 | zero => rfl
 | succ count previous =>
  change SourceOperationInquiry.nextState runtime ((localProcess runtime).stateAt count) = _
  rw [previous]
  rfl

theorem iterated_point (start count : Nat) :
 (SourceOperationInquiry.sourceAction runtime)^[count]
  (SourceOperationInquiry.point runtime (runtime.stateAt start)) =
 SourceOperationInquiry.point runtime (runtime.stateAt (start+count)) := by
 induction count with
 | zero => rfl
 | succ count previous =>
  rw [Function.iterate_succ_apply', previous]
  exact SourceOperationInquiry.actual_point_action runtime (start+count)

def generatedDiagram := (localProcess runtime).diagram

theorem actual_diagram_arrow (count : Nat) :
 (generatedDiagram runtime).map (homOfLE (Nat.le_add_right count 1)).op =
 (localProcess runtime).transitionAt count :=
 Functor.ofOpSequence_map_homOfLE_succ _ count

end SourceInquiryCofinalDiagram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
