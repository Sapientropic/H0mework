import H0mework.Realization.Logic.SourceScope
import H0mework.Fock.Cofinal.OperationDerivation

/-! The original source generates evidence within its complete coimage fibres. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationLogic

open ParticleWaveFock ParticleWaveFockRuntime ParticleWaveFockOperationPrefix
open ParticleWaveFockOperationEnvelope ParticleWaveFockOperationDerivation
open SourceOperationEffects SourceOperationDerivations SourceOperationPresentation
open SourceOperationInventoryLift SourceOperationLogic

noncomputable section

abbrev Model (depth : Nat) := Scope (sourceMap depth)

abbrev StageReduction (depth bound : Nat) (index : Fin (bound + 1)) (word : FormalCarrier) :=
  {certificate : RelationIndex
      (stageEnvironment ((materialHistory depth bound).stageAt index)) OperationSort.parent →₀ ℤ //
    relationMap (stageEnvironment ((materialHistory depth bound).stageAt index)) certificate =
      liftMap word - constantMap (valueMap
        (stageEnvironment ((materialHistory depth bound).stageAt index)) (liftMap word))}

abbrev WordEvidence (depth : Nat) (word : FormalCarrier) :=
  ∀ bound (index : Fin (bound + 1)), StageReduction depth bound index word

/-- The source algorithm generates the proof family from finite syntax at each actual stage. -/
def generatedWordEvidence (depth : Nat) (word : FormalCarrier) : WordEvidence depth word :=
  fun bound index =>
    ⟨normalizationCertificate (stageEnvironment ((materialHistory depth bound).stageAt index))
      (liftMap word), source_reduction _ _⟩

def allModelEvidence (depth : Nat) :
    (point : Model depth) → ForallEvidence (sourceMap depth) (WordEvidence depth) point :=
  (forallEvidenceElim (sourceMap depth) (WordEvidence depth)).symm (generatedWordEvidence depth)

theorem allModelEvidence_readback (depth : Nat) :
    forallEvidenceElim (sourceMap depth) (WordEvidence depth) (allModelEvidence depth) =
      generatedWordEvidence depth :=
  (forallEvidenceElim (sourceMap depth) (WordEvidence depth)).apply_symm_apply _

abbrev TermEvidence (depth : Nat) (word : FormalCarrier) :=
  Σ expression : Expr OperationValue OperationVar .parent,
    PLift (word = Finsupp.single expression 1) ×
    (∀ bound (index : Fin (bound + 1)),
      Derivation (stageEnvironment ((materialHistory depth bound).stageAt index))
        (liftExpr expression)
        (.const ((payloadAt ((runtimeAt depth).advance index.val)).sourceState,
          (payloadAt ((runtimeAt depth).advance index.val)).forcedTrace)))

/-- Reuse the installed original receipt in every generated material stage. -/
def actualTermEvidence (depth : Nat) : TermEvidence depth OperationRelations.operationWord :=
  ⟨fockOperation, ⟨rfl⟩, fun bound index =>
    stageDerivation ((materialHistory depth bound).stageAt index)⟩

def actualWitness (depth : Nat) :
    ExistsEvidence (sourceMap depth) (TermEvidence depth)
      (q (sourceMap depth) OperationRelations.operationWord) :=
  retainEvidence (sourceMap depth) (actualTermEvidence depth)

theorem actualWitness_elimination (depth : Nat) :
    existsEvidenceElim (sourceMap depth) (TermEvidence depth)
      ⟨q (sourceMap depth) OperationRelations.operationWord, actualWitness depth⟩ =
        ⟨OperationRelations.operationWord, actualTermEvidence depth⟩ := rfl

theorem model_fibre_generated (depth : Nat) (left right : FormalCarrier) :
    q (sourceMap depth) left = q (sourceMap depth) right ↔
      ∀ bound (index : Fin (bound + 1)),
        liftMap (left - right) ∈
          LinearMap.range (stageRelationMap ((materialHistory depth bound).stageAt index)) := by
  rw [q_eq_iff, LinearMap.mem_ker, map_sub, sub_eq_zero]
  exact envelope_fibre_generated depth left right

end
end NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockOperationLogic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
