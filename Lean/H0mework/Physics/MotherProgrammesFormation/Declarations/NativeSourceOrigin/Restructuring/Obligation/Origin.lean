import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle
noncomputable section

variable (V : ResponsibilityLifecycle.Vocabulary.{0}) (source : V.SourceEvent) (content : V.Content)

abbrev OriginBody :=
  {obstruction : V.ObstructionAt source // V.demandContent obstruction = content} ⊕
    V.CommitmentAt source content ⊕ V.MandateOriginAt source content ⊕ V.AcceptedTaskAt source content ⊕
    V.ActiveDependencyAt source content ⊕ V.ProtectedRiskAt source content

def originBody : ObligationOrigin V source content → OriginBody V source content
  | .producerDemand ⟨_, obstruction⟩ sourceEq contentEq => by
      cases sourceEq
      exact .inl ⟨obstruction, contentEq⟩
  | .explicitCommitment value => .inr (.inl value)
  | .standingMandate value => .inr (.inr (.inl value))
  | .acceptedTask value => .inr (.inr (.inr (.inl value)))
  | .activeDependency value => .inr (.inr (.inr (.inr (.inl value))))
  | .protectedRisk value => .inr (.inr (.inr (.inr (.inr value))))

def originFromBody : OriginBody V source content → ObligationOrigin V source content
  | .inl ⟨obstruction, same⟩ => .producerDemand ⟨source, obstruction⟩ rfl same
  | .inr (.inl value) => .explicitCommitment value
  | .inr (.inr (.inl value)) => .standingMandate value
  | .inr (.inr (.inr (.inl value))) => .acceptedTask value
  | .inr (.inr (.inr (.inr (.inl value)))) => .activeDependency value
  | .inr (.inr (.inr (.inr (.inr value)))) => .protectedRisk value

def originBodyEquiv : ObligationOrigin V source content ≃ OriginBody V source content where
  toFun := originBody V source content
  invFun := originFromBody V source content
  left_inv := by
    intro origin
    cases origin with
    | producerDemand demand sourceEq contentEq =>
        rcases demand with ⟨event, obstruction⟩
        cases sourceEq
        rfl
    | explicitCommitment value => rfl
    | standingMandate value => rfl
    | acceptedTask value => rfl
    | activeDependency value => rfl
    | protectedRisk value => rfl
  right_inv := by
    intro body
    rcases body with a | b | c | d | e | f <;> rfl

def assumptionBodyEquiv (bearer : V.Bearer) (scope : V.Scope) :
    BearerAssumption V source bearer scope ≃ (V.AcceptedAt bearer source scope ⊕ V.StandingMandateAt bearer source scope) where
  toFun := fun assumption => match assumption with
    | .accepted receipt => .inl receipt
    | .mandated receipt => .inr receipt
  invFun := fun body => match body with
    | .inl receipt => .accepted receipt
    | .inr receipt => .mandated receipt
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by cases value <;> rfl

/-- Equality constraints on a generated result move with its original
member. This transports the complete producer-demand origin fibre. -/
def resultFibreEquiv {A B C D : Type} (input : A ≃ B) (output : C ≃ D)
    (f : A → C) (g : B → D) (commutes : ∀ a, g (input a) = output (f a)) (target : C) :
    {a : A // f a = target} ≃ {b : B // g b = output target} :=
  Equiv.subtypeEquiv input (by
    intro a
    constructor
    · intro same
      exact (commutes a).trans (congrArg output same)
    · intro same
      exact output.injective ((commutes a).symm.trans same))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
