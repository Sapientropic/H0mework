import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.JointRelation.ClozelPairedOmegaJointRelationNativeNextReverseSupport

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
open CofinalHistoryTransition

noncomputable section

def nativeNextJoint_reverseGeneratorResidual (depth : Nat) :
    CofinalHistoryTransition.GeneratorResidual
      (nativeNextJointHistory depth)
      (nativeNextJointHistory (depth + 1)) := by
  refine ⟨runtimeJointRelationAtom depth .phase, ?_, ?_⟩
  · have membership := (rawJointPhaseGenerator
      (CanonicalUnitArithmeticRoot.emitted
        (CanonicalUnitArithmeticRoot.finiteVisit depth).current) 0).property
    simpa only [rawJointPhaseGenerator, currentEffectStage_finiteVisit,
      Nat.add_zero] using membership
  · intro membership
    have future := reverseJoint_generatorClosure_future (depth + 1)
      membership
    change ((runtimeJointRelationAtom depth .phase).support :
      Set RuntimeJointRelationGenerator) ⊆
      {generator : RuntimeJointRelationGenerator | depth + 1 ≤ generator.1}
      at future
    have atom_mem : (depth, RuntimeJointRelationRole.phase) ∈
        (runtimeJointRelationAtom depth .phase).support := by
      simp [runtimeJointRelationAtom]
    have impossible := future atom_mem
    change depth + 1 ≤ depth at impossible
    omega

theorem nativeNextJoint_no_reverseGeneratorInclusion (depth : Nat) :
    ¬ (nativeNextJointHistory depth).generatorClosure ≤
      (nativeNextJointHistory (depth + 1)).generatorClosure := by
  intro inclusion
  let residual := nativeNextJoint_reverseGeneratorResidual depth
  exact residual.target_not_mem (inclusion residual.source_mem)

theorem nativeNextJoint_reverse_settle_generatorResidual (depth : Nat) :
    ∃ residual : CofinalHistoryTransition.GeneratorResidual
        (nativeNextJointHistory depth)
        (nativeNextJointHistory (depth + 1)),
      CofinalHistoryTransition.settle
        (nativeNextJointHistory depth)
        (nativeNextJointHistory (depth + 1)) =
          .generatorResidual residual :=
  CofinalHistoryTransition.settle_eq_generatorResidual_of_not_le
    (nativeNextJointHistory depth)
    (nativeNextJointHistory (depth + 1))
    (nativeNextJoint_no_reverseGeneratorInclusion depth)

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
