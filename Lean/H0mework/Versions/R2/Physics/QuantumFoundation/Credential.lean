import H0mework.Versions.R2.Physics.QuantumFoundation.FoundationAcceptance
import H0mework.Versions.R2.Physics.QuantumFoundation.Classical
import H0mework.Versions.R2.Physics.QuantumFoundation.RuntimeActivation

/-! Stage 9's final output is tied to the fixed source and its current
classical/quantum occurrence. The already generated foundation, active
form-native action, complete unique actual and quantum closure are consumed
together. No physical object or certificate is a caller premise. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineCClassicalWorldAcceptance StageNineEnrichedProofFreeSource
open Stage9DEF.State Stage9DEF.Dynamics
open scoped Matrix ComplexOrder

noncomputable section

/-- The complete fixed-source Stage-9 credential, produced after D/E/F. -/
structure SourceGeneratedContinuousQuantumUnifiedTheoryCredential where
  sourceFoundation : Foundation.SourceFoundation
  actualFoundation : Foundation.ActualFoundation
  sourceExact : Runtime.source = positiveSmoothUnifiedSource
  actualGenerated : Runtime.configuration = Stage9C.Material.SpinPair.actual
  admitted : LawfulClassicalActual Runtime.configuration
  classical : ClassicalWorldAcceptance Runtime.source Runtime.configuration
  uniqueActual : ∀ alternative, LawfulClassicalActual alternative →
    alternative = Runtime.configuration
  quantumClosure : Stage9DEF.Runtime.ActivatedQuantumClosure
  quantumGenerated : Runtime.quantum = Stage9DEF.Source.restrict Runtime.configuration
  normalized : ∀ point, (∑ index, Complex.normSq (Runtime.quantum point index)) = 1
  positive : ∀ point (effect : Observable), effect.PosSemidef →
    0 ≤ vectorEvaluation (Runtime.quantum point) effect
  noncommuting : Stage9DEF.Algebra.colorAction 0 * Stage9DEF.Algebra.colorAction 1 ≠
    Stage9DEF.Algebra.colorAction 1 * Stage9DEF.Algebra.colorAction 0
  actualInterference :
    (vectorEvaluation (Runtime.tick.answer 0) (sourceEffect 0).matrix).re = 1 ∧
      Stage9DEF.Observation.exclusiveWeight 0 = 1 / 2
  actualUnitaryEvolution : ∀ point displacement,
    Runtime.nextTick.answer (point + displacement) =
      (unitary displacement : Observable) *ᵥ Runtime.tick.answer point
  normalizedObservation : ∀ point (effect : Effect),
    0 ≤ (vectorEvaluation (Runtime.tick.answer point) effect.matrix).re ∧
      (vectorEvaluation (Runtime.tick.answer point) effect.matrix).re +
        (vectorEvaluation (Runtime.tick.answer point) effect.complement.matrix).re = 1
  compatibility : Stage9DEF.Compatibility.PhysicalCompatibility
  predictionLaw : ∀ point,
    (vectorEvaluation (Runtime.tick.answer point) (sourceEffect 0).matrix).re =
      Real.cos (point 0 * Stage9C.Material.SpinPair.frequency) ^ 2
  predictionLock :
    (vectorEvaluation
      (Runtime.nextTick.answer (timeDisplacement Stage9DEF.Observation.darkTime))
      (sourceEffect 0).matrix).re = 0 ∧
    (vectorEvaluation
      (Runtime.nextTick.answer (timeDisplacement (2 * Stage9DEF.Observation.darkTime)))
      (sourceEffect 0).matrix).re = 1
  sameOccurrence : Runtime.SameOccurrenceActivation

/-- Directly generated value; every mathematical and runtime field is consumed. -/
def sourceGeneratedContinuousQuantumUnifiedTheoryCredential :
    SourceGeneratedContinuousQuantumUnifiedTheoryCredential := by
  refine
    { sourceFoundation := Foundation.sourceFoundation
      actualFoundation := Foundation.actualFoundation
      sourceExact := Runtime.source_eq
      actualGenerated := Runtime.configuration_eq
      admitted := ?_
      classical := ?_
      uniqueActual := ?_
      quantumClosure := Stage9DEF.Runtime.activatedQuantumClosure
      quantumGenerated := Runtime.quantum_restriction
      normalized := ?_
      positive := ?_
      noncommuting := Stage9DEF.Algebra.colorAction_noncommuting
      actualInterference := ?_
      actualUnitaryEvolution := Runtime.next_quantum_from_current
      normalizedObservation := ?_
      compatibility := Stage9DEF.Compatibility.physicalCompatibility
      predictionLaw := ?_
      predictionLock := ?_
      sameOccurrence := Runtime.sameOccurrenceActivation }
  · rw [Runtime.configuration_eq]
    exact original_actual_admitted
  · rw [Runtime.source_eq, Runtime.configuration_eq]
    exact Stage9C.Material.SpinPair.actual_classicalWorldAcceptance
  · intro alternative admitted
    exact (lawfulClassicalActual_eq_original admitted).trans Runtime.configuration_eq.symm
  · rw [Runtime.quantum_eq]
    exact Stage9DEF.Source.vector_normSq
  · rw [Runtime.quantum_eq]
    exact evaluation_positive
  · rw [Runtime.tick_answer, Runtime.quantum_eq]
    exact ⟨effectWeight_sourceEffect_self 0, Stage9DEF.Observation.exclusiveWeight_formula 0⟩
  · rw [Runtime.tick_answer, Runtime.quantum_eq]
    exact fun point effect =>
      ⟨effectWeight_nonnegative point effect, effectWeight_binary_normalized point effect⟩
  · rw [Runtime.tick_answer, Runtime.quantum_eq]
    exact Stage9DEF.Observation.coherentWeight_cos
  · rw [Runtime.nextTick_answer, Stage9DEF.Runtime.fieldAt_eq_vector]
    exact ⟨Stage9DEF.Observation.prediction_dark, Stage9DEF.Observation.prediction_return⟩

theorem sourceGeneratedContinuousQuantumUnifiedTheory :
    Nonempty SourceGeneratedContinuousQuantumUnifiedTheoryCredential :=
  ⟨sourceGeneratedContinuousQuantumUnifiedTheoryCredential⟩

end
end SaturationMonoid.PhysicsCore.Stage9G
