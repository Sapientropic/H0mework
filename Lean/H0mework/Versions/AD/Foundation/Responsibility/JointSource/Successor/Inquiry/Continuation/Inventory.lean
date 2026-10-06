import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Policy
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Inventory

/-! The actual source observer preserves complete raw syntax across root
births. Its syntax-depth ordinal identifies generated occurrences without cards. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open Native.Restructuring.Inquiry.Continuation (observation Before before_trans before_irrefl erasedDepth)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (first second : Frame (Value := Value) (Var := Var) (sort := sort))

theorem observation_source : observation first.presentation.erase =
    ⟨Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort), first.rawRead⟩ := by
  rw [first.presentation_erase]
  exact (Inquiry.Assembly.observer_preserved first.old first.registered first.packetAt
    (first.currentState.root.emitted first.currentState.visit.current)).trans
    (Restructuring.observation_generated first.old.root.toAuthoritativeRoot first.registered first.packetAt
      (first.currentState.root.emitted first.currentState.visit.current))

theorem raw_eq_of_erasure (same : first.presentation.erase = second.presentation.erase) :
    first.rawRead = second.rawRead := by
  have reads := congrArg observation same
  rw [first.observation_source, second.observation_source] at reads
  exact eq_of_heq (Sigma.mk.inj reads).2

theorem rank_eq_of_erasure (same : first.presentation.erase = second.presentation.erase) :
    first.rank = second.rank := by
  apply Prod.ext
  · exact congrArg (fun raw : Native.Request.Registration.UniformRaw
      (Value := Value) (Var := Var) (sort := sort) => remaining raw.expression)
      (first.raw_eq_of_erasure second same)
  · exact first.rank_depth.symm.trans ((congrArg erasedDepth same).trans second.rank_depth)

end Frame

variable (initial : Frame (Value := Value) (Var := Var) (sort := sort))

theorem frames_erase_injective : Function.Injective (fun count => (frames initial count).presentation.erase) := by
  intro first second same
  have ranks := (frames initial first).rank_eq_of_erasure (frames initial second) same
  rcases lt_trichotomy first second with less | same | greater
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt less
    have progresses := frames_forward initial first distance
    rw [← next, ranks] at progresses
    exact False.elim (before_irrefl _ progresses)
  · exact same
  · obtain ⟨distance, next⟩ := Nat.exists_eq_add_of_lt greater
    have progresses := frames_forward initial second distance
    rw [← next, ranks] at progresses
    exact False.elim (before_irrefl _ progresses)

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
