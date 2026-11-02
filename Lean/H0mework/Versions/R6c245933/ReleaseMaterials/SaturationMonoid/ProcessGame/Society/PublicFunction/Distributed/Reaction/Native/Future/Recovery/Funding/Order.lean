import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding

/-- Comparison reads optionality without discarding either source's typed failure. -/
abbrev NoWorse {New Previous : Type} (new : Option New) (previous : Option Previous) : Prop :=
  previous.isNone = true → new.isNone = true

def check {New Previous : Type} (new : Option New) (previous : Option Previous) : Bool :=
  decide (NoWorse new previous)

theorem check_exact {New Previous : Type} (new : Option New) (previous : Option Previous) :
    check new previous = true ↔ NoWorse new previous := by simp only [check,decide_eq_true_eq]

theorem mapping_payload_keeps_the_exact_decision {New Previous A B : Type}
    (new : Option New) (previous : Option Previous) (left : New → A) (right : Previous → B) :
    check (new.map left) (previous.map right) = check new previous := by
  cases new <;> cases previous <;> rfl

theorem a_new_actual_refusal_cannot_replace_a_funded_result {New Previous : Type}
    (failure : New) : ¬ NoWorse (some failure) (none : Option Previous) := by
  simp only [NoWorse,Option.isNone_none,Option.isNone_some,reduceCtorEq,forall_const,not_false_eq_true]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
