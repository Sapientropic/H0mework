import H0mework.Versions.R2.Physics.ConstitutiveInterfacesQuantization.CheckCurrent
import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence

/-! A subordinate mathematical consumer of the already installed physical
occurrence. Both preparations come from the original macro answers. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.QuantizationCheck

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9DEF
open Stage9C.Material.SpinPair

noncomputable section

attribute [local instance] sourceIndexOrder

def currentPreparation (point : BasePoint) : Fermion.Fock Source.Index :=
  Fermion.oneParticle (Stage10.Runtime.tick.answer point)

def nextPreparation (point : BasePoint) : Fermion.Fock Source.Index :=
  Fermion.oneParticle (Stage10.Runtime.nextTick.answer point)

def currentEvaluation (point : BasePoint) (observable : State.Observable) : ℂ :=
  Fermion.pairing (currentPreparation point)
    (Fermion.secondQuantize observable (currentPreparation point))

def nextEvaluation (point : BasePoint) (observable : State.Observable) : ℂ :=
  Fermion.pairing (nextPreparation point)
    (Fermion.secondQuantize observable (nextPreparation point))

theorem currentPreparation_eq (point : BasePoint) :
    currentPreparation point = preparedFock point := by
  simp only [currentPreparation, Stage10.Runtime.tick_vector, preparedFock]

theorem nextPreparation_eq (point : BasePoint) :
    nextPreparation point = preparedFock point := by
  simp only [nextPreparation, Stage10.Runtime.nextTick_vector, preparedFock]

theorem currentEvaluation_eq (point : BasePoint) (observable : State.Observable) :
    currentEvaluation point observable = fockEvaluation point observable := by
  simp only [currentEvaluation, currentPreparation_eq, fockEvaluation]

theorem nextEvaluation_eq (point : BasePoint) (observable : State.Observable) :
    nextEvaluation point observable = fockEvaluation point observable := by
  simp only [nextEvaluation, nextPreparation_eq, fockEvaluation]

/-- The specified quantization preserves every observable of the same current and next answers. -/
theorem sameOccurrence_quantization_check (point : BasePoint) (observable : State.Observable) :
    currentEvaluation point observable = State.evaluation point observable ∧
      nextEvaluation point observable = State.evaluation point observable := by
  simp only [currentEvaluation_eq, nextEvaluation_eq, fockEvaluation_eq_source, and_self]

theorem sameOccurrence_current_prediction (point : BasePoint) (direction generator : Fin 3) :
    currentEvaluation point
        (Compatibility.physicalCurrent direction.succ (sourceColorP286Generator generator)) =
        (if direction = generator then 1 / 2 else 0) ∧
      nextEvaluation point
        (Compatibility.physicalCurrent direction.succ (sourceColorP286Generator generator)) =
        (if direction = generator then 1 / 2 else 0) := by
  simp only [currentEvaluation_eq, nextEvaluation_eq, source_generator_prediction, and_self]

end
end SaturationMonoid.PhysicsCore.QuantizationCheck
