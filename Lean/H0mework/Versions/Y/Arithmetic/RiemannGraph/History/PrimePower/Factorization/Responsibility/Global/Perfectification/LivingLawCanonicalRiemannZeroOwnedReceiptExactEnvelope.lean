import Mathlib.LinearAlgebra.Dual.Basis
import H0mework.Realization.ScalarCofinal.ExactEnvelope
import H0mework.Versions.Y.Arithmetic.RiemannGraph.History.PrimePower.Factorization.Responsibility.Global.Cofinal.LivingLawCanonicalRiemannZeroOwnedReceiptCofinalCompletion

/-!
# Exact perfect envelope of the completed zero-owned receipt table

The cofinal completion is evaluated in the double dual of its full receipt
table.  The generic exact-envelope engine forms the coimage and its perfect
dual-image carrier without finite, projective, determinant, or descent
premises.  On the actual source table the generated envelope map is faithful;
any larger completion kernel remains an explicit representation residual.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
namespace MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofinal

open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarExactEnvelope
open SourceGeneratedScalarPerfectification

noncomputable section

def completionEvaluation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (receiptCofinalFace observation nontrivial).completion
        (receiptCofinalCalculation observation nontrivial) →ₗ[ℂ]
      Module.Dual ℂ (Module.Dual ℂ ReceiptTable) :=
  (Module.Dual.eval ℂ ReceiptTable).comp
    (completionToTable observation nontrivial)

def receiptExactEnvelope
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  SourceGeneratedScalarCofinalExactEnvelope.envelope
    (receiptCofinalFace observation nontrivial)
    (receiptCofinalCalculation observation nontrivial)
    (completionEvaluation observation nontrivial)

theorem receiptExactEnvelope_source_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ((dualInclusion (completionEvaluation observation nontrivial)).comp
      (generatedDualMap (completionEvaluation observation nontrivial))).comp
      (SourceGeneratedScalarCofinalExactEnvelope.sourceMap
        (receiptCofinalFace observation nontrivial)
        (receiptCofinalCalculation observation nontrivial)
        (completionEvaluation observation nontrivial)) =
    (completionEvaluation observation nontrivial).comp
      ((receiptCofinalFace observation nontrivial).completionMap
        (receiptCofinalCalculation observation nontrivial)).hom :=
  SourceGeneratedScalarCofinalExactEnvelope.source_evaluation_readback
    (receiptCofinalFace observation nontrivial)
    (receiptCofinalCalculation observation nontrivial)
    (completionEvaluation observation nontrivial)

abbrev ReceiptExactCarrier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :=
  SourceGeneratedScalarCofinalExactEnvelope.Carrier
    (receiptCofinalFace observation nontrivial)
    (receiptCofinalCalculation observation nontrivial)
    (completionEvaluation observation nontrivial)

def receiptEnvelopeSourceMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptTable →ₗ[ℂ] ReceiptExactCarrier observation nontrivial :=
  SourceGeneratedScalarCofinalExactEnvelope.sourceMap
    (receiptCofinalFace observation nontrivial)
    (receiptCofinalCalculation observation nontrivial)
    (completionEvaluation observation nontrivial)

theorem receiptEnvelopeSourceMap_eq_zero_iff
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (table : ReceiptTable) :
    receiptEnvelopeSourceMap observation nontrivial table = 0 ↔ table = 0 := by
  rw [receiptEnvelopeSourceMap,
    SourceGeneratedScalarCofinalExactEnvelope.sourceMap_eq_zero_iff]
  constructor
  · intro evaluationZero
    change Module.Dual.eval ℂ ReceiptTable
        (completionToTable observation nontrivial
          ((receiptCofinalFace observation nontrivial).completionMap
            (receiptCofinalCalculation observation nontrivial) table)) = 0
      at evaluationZero
    rw [completionToTable_source] at evaluationZero
    apply (Module.Free.chooseBasis ℂ ReceiptTable).eval_injective
    simpa using evaluationZero
  · intro tableZero
    subst table
    simp

theorem receiptEnvelopeSourceMap_injective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Injective (receiptEnvelopeSourceMap observation nontrivial) := by
  rw [← LinearMap.ker_eq_bot]
  ext table
  rw [LinearMap.mem_ker, Submodule.mem_bot,
    receiptEnvelopeSourceMap_eq_zero_iff]

theorem receiptEnvelopeSourceMap_doubleDual_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (table : ReceiptTable) :
    ((dualInclusion (completionEvaluation observation nontrivial)).comp
      (generatedDualMap (completionEvaluation observation nontrivial)))
        (receiptEnvelopeSourceMap observation nontrivial table) =
      Module.Dual.eval ℂ ReceiptTable table := by
  have readback := LinearMap.congr_fun
    (receiptExactEnvelope_source_readback observation nontrivial) table
  change _ = completionEvaluation observation nontrivial
      ((receiptCofinalFace observation nontrivial).completionMap
        (receiptCofinalCalculation observation nontrivial) table) at readback
  change _ = Module.Dual.eval ℂ ReceiptTable
      (completionToTable observation nontrivial
        ((receiptCofinalFace observation nontrivial).completionMap
          (receiptCofinalCalculation observation nontrivial) table)) at readback
  rw [completionToTable_source] at readback
  exact readback

theorem completionEvaluation_ker_le_completionToTable_ker
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    LinearMap.ker (completionEvaluation observation nontrivial) ≤
      LinearMap.ker (completionToTable observation nontrivial) := by
  intro completed evaluationZero
  rw [LinearMap.mem_ker] at evaluationZero ⊢
  change Module.Dual.eval ℂ ReceiptTable
      (completionToTable observation nontrivial completed) = 0 at evaluationZero
  apply (Module.Free.chooseBasis ℂ ReceiptTable).eval_injective
  simpa using evaluationZero

/-- Canonical readback from the exact envelope to the full source table. -/
def envelopeToTable
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial →ₗ[ℂ] ReceiptTable :=
  canonicalFactor (completionEvaluation observation nontrivial)
    (completionToTable observation nontrivial)
    (completionEvaluation_ker_le_completionToTable_ker observation nontrivial)

@[simp] theorem envelopeToTable_canonicalMap
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (completed : (receiptCofinalFace observation nontrivial).completion
      (receiptCofinalCalculation observation nontrivial)) :
    envelopeToTable observation nontrivial
        (canonicalMap (completionEvaluation observation nontrivial) completed) =
      completionToTable observation nontrivial completed :=
  rfl

theorem envelopeToTable_source
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (envelopeToTable observation nontrivial).comp
        (receiptEnvelopeSourceMap observation nontrivial) = LinearMap.id := by
  apply LinearMap.ext
  intro table
  change envelopeToTable observation nontrivial
      (canonicalMap (completionEvaluation observation nontrivial)
        ((receiptCofinalFace observation nontrivial).completionMap
          (receiptCofinalCalculation observation nontrivial) table)) = table
  rw [envelopeToTable_canonicalMap, completionToTable_source]

theorem envelopeToTable_bijective
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Function.Bijective (envelopeToTable observation nontrivial) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    ext value
    rw [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro valueZero
      obtain ⟨completed, rfl⟩ :=
        Submodule.mkQ_surjective
          (LinearMap.ker (completionEvaluation observation nontrivial)) value
      change envelopeToTable observation nontrivial
          (canonicalMap (completionEvaluation observation nontrivial) completed) = 0
        at valueZero
      rw [envelopeToTable_canonicalMap] at valueZero
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [LinearMap.mem_ker]
      change Module.Dual.eval ℂ ReceiptTable
        (completionToTable observation nontrivial completed) = 0
      rw [valueZero, map_zero]
    · intro valueZero
      rw [valueZero, map_zero]
  · intro table
    exact ⟨receiptEnvelopeSourceMap observation nontrivial table,
      LinearMap.congr_fun
        (envelopeToTable_source observation nontrivial) table⟩

/-- The exact envelope is canonically the full receipt table.  This does not
make the table finite, reflexive, or determinant-eligible. -/
noncomputable def exactCarrierEquivTable
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ReceiptExactCarrier observation nontrivial ≃ₗ[ℂ] ReceiptTable :=
  LinearEquiv.ofBijective (envelopeToTable observation nontrivial)
    (envelopeToTable_bijective observation nontrivial)

end
end MuntzGraph.Conductor.History.PrimePowerCurrent.ReceiptRelation.Cofinal
end NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
