import H0mework.Physics.MotherProgrammesFormation.Declarations.History.Continuation
import H0mework.Physics.MotherDeclarationsEvaluator.Functions

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherUnitSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherClosedRestrictions MotherStreamLaws

noncomputable section

abbrev Current := CanonicalUnitArithmeticRoot.Current
abbrev OccurrenceAt (current : Current) :=
  CanonicalUnitArithmeticRoot.ledgerSource.source.toRootSource.actual.OccurrenceAt current

def sourceOccurrence (current : Current) : OccurrenceAt current :=
  CanonicalUnitArithmeticRoot.emitted current

theorem occurrence_unique {current : Current} (occurrence : OccurrenceAt current) :
    occurrence = sourceOccurrence current := by
  rcases occurrence with ⟨support, event⟩
  change CanonicalUnitArithmeticRoot.RootNativeEventAt current support at event
  cases event.support_eq
  rfl

def currentRead (value : ℝ) : Current := ArithmeticGeneration.UnitHistory.generate (Nat.floor value)

theorem current_recovered (current : Current) : currentRead current.cardinalShadow = current := by
  apply ArithmeticGeneration.UnitHistory.eq_of_cardinalShadow_eq
  simp only [currentRead, Nat.floor_natCast, ArithmeticGeneration.UnitHistory.cardinalShadow_generate]

def tagged {A B : Type} (left : A → Stream) (right : B → Stream) : A ⊕ B → Stream
  | .inl value => pairStream (fun _ => 0) (left value)
  | .inr value => pairStream (fun _ => 1) (right value)

theorem tagged_injective {A B : Type} {left : A → Stream} {right : B → Stream}
    (leftFaithful : Function.Injective left) (rightFaithful : Function.Injective right) :
    Function.Injective (tagged left right) := by
  intro first last same
  have tags := congrFun (congrArg firstStream same) 0
  have values := congrArg lastStream same
  cases first <;> cases last
  · exact congrArg Sum.inl (leftFaithful (by simpa only [tagged, last_pair] using values))
  · simp only [tagged, first_pair, zero_ne_one] at tags
  · simp only [tagged, first_pair, one_ne_zero] at tags
  · exact congrArg Sum.inr (rightFaithful (by simpa only [tagged, last_pair] using values))

abbrev Body := Fin 4 ⊕ (MotherHistoryFormation.Input ⊕ MotherEvaluatorTreeFunctions.Input)
abbrev Input := Current × Body

def kindSamples (kind : Fin 4) : Stream := fun _ => (kind.val : ℝ)

def bodySamples : Body → Stream :=
  tagged kindSamples (tagged MotherHistoryFormation.inputSamples MotherEvaluatorTreeFunctions.inputSamples)

theorem bodySamples_injective : Function.Injective bodySamples := by
  apply tagged_injective
  · intro first last same
    apply Fin.ext
    exact Nat.cast_injective (congrFun same 0)
  · exact tagged_injective MotherHistoryFormation.inputSamples_injective
      MotherEvaluatorTreeFunctions.inputSamples_injective

def inputSamples (input : Input) : Stream :=
  pairStream (fun _ => (input.1.cardinalShadow : ℝ)) (bodySamples input.2)

theorem inputSamples_injective : Function.Injective inputSamples := by
  intro first last same
  have currents := congrFun (congrArg firstStream same) 0
  have bodies := congrArg lastStream same
  apply Prod.ext
  · apply ArithmeticGeneration.UnitHistory.eq_of_cardinalShadow_eq
    apply Nat.cast_injective (R := ℝ)
    simpa only [inputSamples, first_pair] using currents
  · apply bodySamples_injective
    simpa only [inputSamples, last_pair] using bodies

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherUnitSource
