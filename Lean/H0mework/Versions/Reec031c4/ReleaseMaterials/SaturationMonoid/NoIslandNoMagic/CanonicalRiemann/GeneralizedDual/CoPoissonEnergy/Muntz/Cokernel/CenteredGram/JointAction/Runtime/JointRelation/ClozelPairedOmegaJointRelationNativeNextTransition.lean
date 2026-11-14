import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextTrace
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationShiftAction
import H0mework.Realization.Completion.HistoryTransition

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistoryTransition

noncomputable section

theorem nativeNextJoint_generatorClosure_le (depth : Nat) :
    (nativeNextJointHistory (depth + 1)).generatorClosure ≤
      (nativeNextJointHistory depth).generatorClosure := by
  apply iSup_le
  intro stage
  exact (nativeNextJoint_generatorStage_le depth stage).trans
    ((nativeNextJointHistory depth).generatorStage_le_closure (stage + 1))

theorem nativeNextJoint_relationClosure_le (depth : Nat) :
    (nativeNextJointHistory (depth + 1)).relationClosure ≤
      (nativeNextJointHistory depth).relationClosure := by
  apply iSup_le
  intro stage
  exact (nativeNextJoint_relationStage_le depth stage).trans
    ((nativeNextJointHistory depth).relationStage_le_closure (stage + 1))

def nativeNextJointGeneratedTransition (depth : Nat) :
    CofinalHistoryTransition.GeneratedTransition
      (nativeNextJointHistory (depth + 1))
      (nativeNextJointHistory depth) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (nativeNextJoint_generatorClosure_le depth)
    (by
      intro relation relation_mem
      rw [LinearMap.mem_ker]
      apply (Submodule.Quotient.mk_eq_zero
        (nativeNextJointHistory depth).relationInGeneratorClosure).2
      exact nativeNextJoint_relationClosure_le depth relation_mem)

def nativeNextJointCompletionMap (depth : Nat) :
    (nativeNextJointHistory (depth + 1)).CompletionCarrier →ₗ[ℤ]
      (nativeNextJointHistory depth).CompletionCarrier :=
  CofinalHistoryTransition.GeneratedTransition.completionMap
    (nativeNextJointHistory (depth + 1))
    (nativeNextJointHistory depth)
    (nativeNextJointGeneratedTransition depth)

theorem nativeNextJoint_phase_generator_inclusion
    (depth stage : Nat) :
    CofinalHistoryTransition.GeneratedTransition.generatorMap
        (nativeNextJointHistory (depth + 1))
        (nativeNextJointHistory depth)
        (nativeNextJointGeneratedTransition depth)
        (rawJointPhaseGenerator
          (CanonicalUnitArithmeticRoot.emitted
            (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
          stage) =
      rawJointPhaseGenerator
        (CanonicalUnitArithmeticRoot.emitted
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
        (stage + 1) := by
  apply Subtype.ext
  change runtimeJointRelationAtom
      (currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current + stage)
      .phase =
    runtimeJointRelationAtom
      (currentEffectStage
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current + (stage + 1))
      .phase
  simp only [currentEffectStage_finiteVisit]
  congr 1
  omega

theorem nativeNextJoint_phase_transport_eq_sourceShift
    (depth stage : Nat) :
    nativeNextJointCompletionMap depth
        ((nativeNextJointHistory (depth + 1)).completionProjection
          (rawJointPhaseGenerator
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
            stage)) =
      rawJointShiftOnCompletion
        (CanonicalUnitArithmeticRoot.emitted
          (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
        ((nativeNextJointHistory depth).completionProjection
          (rawJointPhaseGenerator
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
            stage)) := by
  have transported :=
    CofinalHistoryTransition.GeneratedTransition.completionMap_projection
      (nativeNextJointHistory (depth + 1))
      (nativeNextJointHistory depth)
      (nativeNextJointGeneratedTransition depth)
      (rawJointPhaseGenerator
        (CanonicalUnitArithmeticRoot.emitted
          (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
        stage)
  have included := nativeNextJoint_phase_generator_inclusion depth stage
  have shifted := rawJointShift_phase_completion
    (CanonicalUnitArithmeticRoot.emitted
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current) stage
  calc
    _ = (nativeNextJointHistory depth).completionProjection
          (CofinalHistoryTransition.GeneratedTransition.generatorMap
            (nativeNextJointHistory (depth + 1))
            (nativeNextJointHistory depth)
            (nativeNextJointGeneratedTransition depth)
            (rawJointPhaseGenerator
              (CanonicalUnitArithmeticRoot.emitted
                (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current)
              stage)) := transported
    _ = (nativeNextJointHistory depth).completionProjection
          (rawJointPhaseGenerator
            (CanonicalUnitArithmeticRoot.emitted
              (CanonicalUnitArithmeticRoot.finiteVisit depth).current)
            (stage + 1)) := congrArg _ included
    _ = _ := shifted.symm

theorem nativeNextJoint_nativeWrite_receipt (depth : Nat) :
    (CanonicalUnitArithmeticRoot.nativeWriteAt
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current).target =
        (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ∧
      (CanonicalUnitArithmeticRoot.nativeWriteAt
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current).wholeWriteBack =
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current := by
  constructor
  · rfl
  · rfl

/-- The two histories are attached to distinct native visits; their
completion comparison is a genuine transition rather than occurrence
equality. -/
theorem nativeNextJoint_visits_distinct (depth : Nat) :
    (CanonicalUnitArithmeticRoot.finiteVisit (depth + 1)).current ≠
      (CanonicalUnitArithmeticRoot.finiteVisit depth).current := by
  intro equality
  exact (CanonicalUnitArithmeticRoot.nativeWriteAt
    (CanonicalUnitArithmeticRoot.finiteVisit depth).current).target_ne_source
      ((nativeNextJoint_nativeWrite_receipt depth).1.trans equality)

end
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
