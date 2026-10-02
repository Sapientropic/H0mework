import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Compiler
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Inventory

/-! The original inquiry engine activates the occurrence-generated calculation
query. Its registry uses the already paid raw-syntax/causal-depth ordinal;
the next frame configuration is computed by the actual answered or admission receipt. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
  (observation erasedDepth Before before_trans before_irrefl)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}

namespace Shared
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

theorem observation_source : observation (presentation frame configuration).erase =
    ⟨RootGeneratedDebtActivationJointSource.Native.Request.Registration.UniformRaw
      (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort), frame.rawRead⟩ := by
  have original := frame.observation_source
  rw [frame.presentation_erase] at original
  exact original

theorem depth_source : erasedDepth (presentation frame configuration).erase = frame.rank.2 := by
  have original := frame.rank_depth
  rw [frame.presentation_erase] at original
  exact original

theorem next_progress : Before frame.rank (next frame configuration).rank := by
  unfold next
  cases frame.action with
  | inr paid =>
      exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩
  | inl settled =>
      change Before frame.rank (remaining (request frame).input.expression, 1)
      apply Or.inl
      change remaining frame.rawRead.expression < remaining frame.request.input.expression
      rw [frame.request_budget]
      omega

def frames (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
    (configuration : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)) :
    Nat → M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)
  | 0 => initial
  | count + 1 => next (frames initial configuration count) configuration

variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable (configuration : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

theorem frames_forward (first distance : Nat) :
    Before (frames initial configuration first).rank (frames initial configuration (first + distance + 1)).rank := by
  induction distance with
  | zero => exact next_progress _ configuration
  | succ distance prior =>
      apply before_trans prior
      have count : first + (distance + 1) + 1 = (first + distance + 1) + 1 := by omega
      rw [count]
      exact next_progress _ configuration

theorem frames_erase_injective : Function.Injective (fun count => (presentation (frames initial configuration count) configuration).erase) := by
  intro first second same
  have reads := congrArg observation same
  rw [observation_source _ configuration, observation_source _ configuration] at reads
  have raws := eq_of_heq (Sigma.mk.inj reads).2
  have ranks : (frames initial configuration first).rank = (frames initial configuration second).rank := Prod.ext
    (congrArg (fun raw : RootGeneratedDebtActivationJointSource.Native.Request.Registration.UniformRaw
      (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) => remaining raw.expression) raws)
    ((depth_source _ configuration).symm.trans ((congrArg erasedDepth same).trans (depth_source _ configuration)))
  rcases lt_trichotomy first second with less | equal | greater
  · obtain ⟨distance, index⟩ := Nat.exists_eq_add_of_lt less
    have progress := frames_forward initial configuration first distance
    rw [← index, ranks] at progress
    exact False.elim (before_irrefl _ progress)
  · exact equal
  · obtain ⟨distance, index⟩ := Nat.exists_eq_add_of_lt greater
    have progress := frames_forward initial configuration second distance
    rw [← index, ranks] at progress
    exact False.elim (before_irrefl _ progress)

def process : SourceNativeInquiryEngineProcess.{u} where
  State := ULift.{u} Nat
  stateAt := fun count => .active (presentation (frames initial configuration count.down) configuration)
  erase_injective := by
    intro first second firstState secondState firstActive secondActive same
    cases firstActive
    cases secondActive
    exact congrArg ULift.up (frames_erase_injective initial configuration same)
  initial := .up 0
  successorAt := fun count candidate => ⟨.up (count.down + 1), successor_valid _ configuration candidate⟩

def runtime : SourceNativeInquiryRuntime (process initial configuration) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (query initial configuration) (query_unique initial configuration)
    (fun count _ => query (frames initial configuration (count.down + 1)) configuration)
    (fun count _ => query_unique (frames initial configuration (count.down + 1)) configuration)

private theorem next_node (count : Nat) (engine : Engine (process initial configuration))
    (same : engine.node = .active (presentation (frames initial configuration count) configuration))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    (engine.ask activation).next.node = .active (presentation (frames initial configuration (count + 1)) configuration) := by
  rcases engine with ⟨registered⟩
  have registeredEq : registered = .up count := (process initial configuration).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst registered
  rfl

theorem actual_node (count : Nat) : ((runtime initial configuration).stateAt count).engine.node =
    .active (presentation (frames initial configuration count) configuration) := by
  induction count with
  | zero => rfl
  | succ count prior =>
      exact next_node initial configuration count ((runtime initial configuration).stateAt count).engine prior
        ((runtime initial configuration).stateAt count).activation

theorem actual_next (count : Nat) : ((runtime initial configuration).tickAt count).next.node =
    .active (presentation (frames initial configuration (count + 1)) configuration) := actual_node initial configuration (count + 1)

private theorem query_at_node (count : Nat) (engine : Engine (process initial configuration))
    (same : engine.node = .active (presentation (frames initial configuration count) configuration))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    HEq activation.query (query (frames initial configuration count) configuration) := by
  rcases engine with ⟨registered⟩
  have registeredEq : registered = .up count := (process initial configuration).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst registered
  exact heq_of_eq (query_unique (frames initial configuration count) configuration activation.query)

theorem actual_query (count : Nat) : HEq ((runtime initial configuration).stateAt count).activation.query
    (query (frames initial configuration count) configuration) := query_at_node initial configuration count ((runtime initial configuration).stateAt count).engine
      (actual_node initial configuration count) ((runtime initial configuration).stateAt count).activation

private theorem answer_at_node (count : Nat) (engine : Engine (process initial configuration))
    (same : engine.node = .active (presentation (frames initial configuration count) configuration))
    (activation : Engine.SourceNativeInquiryActivationAt engine) :
    HEq (engine.ask activation).answer ((state (frames initial configuration count) configuration).compileInquiry
      (query (frames initial configuration count) configuration)).answerReadout := by
  rcases engine with ⟨registered⟩
  have registeredEq : registered = .up count := (process initial configuration).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst registered
  rcases activation with ⟨candidate, origin⟩
  have queryEq := query_unique (frames initial configuration count) configuration candidate
  subst candidate
  cases actual : (frames initial configuration count).action with
  | inr paid =>
      have read := RootInquiryProcessNode.active_answer_heq_directlyAnswered
        (presentation (frames initial configuration count) configuration) (query (frames initial configuration count) configuration)
        (resultFace (frames initial configuration count) configuration) (consumer (frames initial configuration count) configuration)
        (compiles_paid _ configuration paid actual)
      apply read.trans
      rw [compiles_paid _ configuration paid actual]
      rfl
  | inl settled =>
      have read := RootInquiryProcessNode.active_answer_heq_debtAdmission
        (presentation (frames initial configuration count) configuration) (query (frames initial configuration count) configuration)
        ((birthProgram (frames initial configuration count) configuration).generate _)
        (compiles_settled _ configuration settled actual)
      apply read.trans
      rw [compiles_settled _ configuration settled actual]
      rfl

theorem actual_answer (count : Nat) : HEq ((runtime initial configuration).tickAt count).answer
    ((state (frames initial configuration count) configuration).compileInquiry (query (frames initial configuration count) configuration)).answerReadout :=
  answer_at_node initial configuration count ((runtime initial configuration).stateAt count).engine (actual_node initial configuration count)
    ((runtime initial configuration).stateAt count).activation

end Shared

variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
abbrev observation_source := Shared.observation_source frame originalProgramme
abbrev depth_source := Shared.depth_source frame originalProgramme
abbrev next_progress := Shared.next_progress frame originalProgramme
abbrev frames (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.frames initial originalProgramme
@[simp] theorem frames_zero (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) :
    frames initial 0 = initial := rfl
@[simp] theorem frames_succ (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) (count : Nat) :
    frames initial (count + 1) = next (frames initial count) := rfl

abbrev frames_forward (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.frames_forward initial originalProgramme
abbrev frames_erase_injective (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.frames_erase_injective initial originalProgramme
abbrev process (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.process initial originalProgramme
abbrev runtime (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.runtime initial originalProgramme
abbrev actual_node (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.actual_node initial originalProgramme
abbrev actual_next (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.actual_next initial originalProgramme
abbrev actual_query (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.actual_query initial originalProgramme
abbrev actual_answer (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)) := Shared.actual_answer initial originalProgramme
end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
