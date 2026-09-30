import H0mework.Realization.Coherent.OrbitClosedDefectPort
import H0mework.Versions.Y.Arithmetic.SonineGap.StageZeroResidualPrism

/-!
# Stage-zero orbit-closed conservative defect port

The selected and reversal integral graph orbits generate sibling complexified
closed ranges.  At the identity event, the actual stage-zero owner-free
isometry splits into a retained compression and the orthogonal projection of
the already installed coupling residual.  The residual itself is disposed as
canonical internal and external coordinates, with exact reconstruction and
Pythagorean energy accounting.

No target equality, critical-line, radial-zero, or residual-zero premise
enters.
-/

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

open Character.GlobalCoPoissonCurrent
open SourceGeneratedCompressedUnitaryDefectPort
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralOrbitClosedDefectPort
open scoped InnerProductSpace

noncomputable section

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

def selectedStageZeroOrbitClosedRange : ClosedSubmodule ℂ JointGraphTarget :=
  orbitClosedRange (selectedIntegralGraphOrbit observation nontrivial)

def reversalStageZeroOrbitClosedRange : ClosedSubmodule ℂ JointGraphTarget :=
  orbitClosedRange (reversalIntegralGraphOrbit observation nontrivial)

def selectedStageZeroOrbitIdentitySeed :
    selectedStageZeroOrbitClosedRange observation nontrivial :=
  orbitEvent (selectedIntegralGraphOrbit observation nontrivial) (delta 1)

def reversalStageZeroOrbitIdentitySeed :
    reversalStageZeroOrbitClosedRange observation nontrivial :=
  orbitEvent (reversalIntegralGraphOrbit observation nontrivial) (delta 1)

def selectedStageZeroOrbitDefectPort :=
  defectPort (selectedStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry

def reversalStageZeroOrbitDefectPort :=
  defectPort (reversalStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry

def selectedStageZeroOrbitNextPoint : JointGraphTarget :=
  selectedIntegralGraphOrbit observation nontrivial
    ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))

def reversalStageZeroOrbitNextPoint : JointGraphTarget :=
  reversalIntegralGraphOrbit observation nontrivial
    ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))

theorem selectedStageZeroOrbitNextPoint_mem :
    selectedStageZeroOrbitNextPoint observation nontrivial ∈
      selectedStageZeroOrbitClosedRange observation nontrivial :=
  feature_mem_orbitClosedRange
    (selectedIntegralGraphOrbit observation nontrivial)
    ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))

theorem reversalStageZeroOrbitNextPoint_mem :
    reversalStageZeroOrbitNextPoint observation nontrivial ∈
      reversalStageZeroOrbitClosedRange observation nontrivial :=
  feature_mem_orbitClosedRange
    (reversalIntegralGraphOrbit observation nontrivial)
    ((leftTranslation stageZeroQuarterScaleUnit).toLinearMap (delta 1))

theorem selectedStageZeroCouplingResidual_eq_action_sub_next :
    selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      stageZeroOwnerFreeGraphTargetAction
          (selectedIntegralGraphOrbit observation nontrivial (delta 1)) -
        selectedStageZeroOrbitNextPoint observation nontrivial := by
  rw [selectedOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rw [stageZeroQuarterScale_ownerFreeAction]
  rfl

theorem reversalStageZeroCouplingResidual_eq_action_sub_next :
    reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      stageZeroOwnerFreeGraphTargetAction
          (reversalIntegralGraphOrbit observation nontrivial (delta 1)) -
        reversalStageZeroOrbitNextPoint observation nontrivial := by
  rw [reversalOwnerFreeCouplingResidual, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.comp_apply]
  rw [stageZeroQuarterScale_ownerFreeAction]
  rfl

/-- Retained component of the selected coupling incidence. -/
def selectedStageZeroProjectedInternal :
    selectedStageZeroOrbitClosedRange observation nontrivial :=
  orbitProjectedInternal
    (selectedIntegralGraphOrbit observation nontrivial)
    (selectedOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

/-- Exposed component of the selected coupling incidence. -/
def selectedStageZeroProjectedExternal :
    Submodule.orthogonal
      (selectedStageZeroOrbitClosedRange observation nontrivial).toSubmodule :=
  orbitProjectedExternal
    (selectedIntegralGraphOrbit observation nontrivial)
    (selectedOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

def reversalStageZeroProjectedInternal :
    reversalStageZeroOrbitClosedRange observation nontrivial :=
  orbitProjectedInternal
    (reversalIntegralGraphOrbit observation nontrivial)
    (reversalOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

def reversalStageZeroProjectedExternal :
    Submodule.orthogonal
      (reversalStageZeroOrbitClosedRange observation nontrivial).toSubmodule :=
  orbitProjectedExternal
    (reversalIntegralGraphOrbit observation nontrivial)
    (reversalOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

theorem selectedStageZeroCouplingResidual_eq_projectedInternal_add_external :
    selectedOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      (selectedStageZeroProjectedInternal observation nontrivial : JointGraphTarget) +
        (selectedStageZeroProjectedExternal observation nontrivial : JointGraphTarget) := by
  exact incidence_eq_projectedInternal_add_projectedExternal
    (selectedIntegralGraphOrbit observation nontrivial)
    (selectedOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

theorem reversalStageZeroCouplingResidual_eq_projectedInternal_add_external :
    reversalOwnerFreeCouplingResidual observation nontrivial
        stageZeroQuarterScaleUnit (delta 1) =
      (reversalStageZeroProjectedInternal observation nontrivial : JointGraphTarget) +
        (reversalStageZeroProjectedExternal observation nontrivial : JointGraphTarget) := by
  exact incidence_eq_projectedInternal_add_projectedExternal
    (reversalIntegralGraphOrbit observation nontrivial)
    (reversalOwnerFreeCouplingResidual observation nontrivial
      stageZeroQuarterScaleUnit (delta 1))

theorem selectedStageZeroExternalDefect_eq_projectedExternal :
    externalDefect (selectedStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (selectedStageZeroOrbitIdentitySeed observation nontrivial) =
      selectedStageZeroProjectedExternal observation nontrivial := by
  unfold selectedStageZeroProjectedExternal
  rw [selectedStageZeroCouplingResidual_eq_action_sub_next]
  exact externalDefect_eq_projectedExternal_sub_of_mem
    (selectedIntegralGraphOrbit observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry (delta 1)
    (selectedStageZeroOrbitNextPoint observation nontrivial)
    (selectedStageZeroOrbitNextPoint_mem observation nontrivial)

theorem reversalStageZeroExternalDefect_eq_projectedExternal :
    externalDefect (reversalStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (reversalStageZeroOrbitIdentitySeed observation nontrivial) =
      reversalStageZeroProjectedExternal observation nontrivial := by
  unfold reversalStageZeroProjectedExternal
  rw [reversalStageZeroCouplingResidual_eq_action_sub_next]
  exact externalDefect_eq_projectedExternal_sub_of_mem
    (reversalIntegralGraphOrbit observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry (delta 1)
    (reversalStageZeroOrbitNextPoint observation nontrivial)
    (reversalStageZeroOrbitNextPoint_mem observation nontrivial)

@[simp] theorem selectedStageZeroOrbitDefectPort_seed_snd :
    (selectedStageZeroOrbitDefectPort observation nontrivial
      (selectedStageZeroOrbitIdentitySeed observation nontrivial)).snd =
      selectedStageZeroProjectedExternal observation nontrivial := by
  rw [selectedStageZeroOrbitDefectPort, defectPort_snd]
  exact selectedStageZeroExternalDefect_eq_projectedExternal
    observation nontrivial

@[simp] theorem reversalStageZeroOrbitDefectPort_seed_snd :
    (reversalStageZeroOrbitDefectPort observation nontrivial
      (reversalStageZeroOrbitIdentitySeed observation nontrivial)).snd =
      reversalStageZeroProjectedExternal observation nontrivial := by
  rw [reversalStageZeroOrbitDefectPort, defectPort_snd]
  exact reversalStageZeroExternalDefect_eq_projectedExternal
    observation nontrivial

theorem selectedStageZeroCompression_add_projectedExternal :
    (compression (selectedStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (selectedStageZeroOrbitIdentitySeed observation nontrivial) : JointGraphTarget) +
      (selectedStageZeroProjectedExternal observation nontrivial : JointGraphTarget) =
      stageZeroOwnerFreeGraphTargetAction
        (selectedIntegralGraphOrbit observation nontrivial (delta 1)) := by
  rw [← selectedStageZeroExternalDefect_eq_projectedExternal]
  exact compression_add_externalDefect
    (selectedStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
    (selectedStageZeroOrbitIdentitySeed observation nontrivial)

theorem reversalStageZeroCompression_add_projectedExternal :
    (compression (reversalStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (reversalStageZeroOrbitIdentitySeed observation nontrivial) : JointGraphTarget) +
      (reversalStageZeroProjectedExternal observation nontrivial : JointGraphTarget) =
      stageZeroOwnerFreeGraphTargetAction
        (reversalIntegralGraphOrbit observation nontrivial (delta 1)) := by
  rw [← reversalStageZeroExternalDefect_eq_projectedExternal]
  exact compression_add_externalDefect
    (reversalStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
    (reversalStageZeroOrbitIdentitySeed observation nontrivial)

theorem selectedStageZeroCompression_projectedExternal_pythagoras :
    ‖compression (selectedStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (selectedStageZeroOrbitIdentitySeed observation nontrivial)‖ ^ 2 +
      ‖selectedStageZeroProjectedExternal observation nontrivial‖ ^ 2 =
      ‖selectedIntegralGraphOrbit observation nontrivial (delta 1)‖ ^ 2 := by
  rw [← selectedStageZeroExternalDefect_eq_projectedExternal]
  exact norm_sq_compression_add_externalDefect
    (selectedStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
    (selectedStageZeroOrbitIdentitySeed observation nontrivial)

theorem reversalStageZeroCompression_projectedExternal_pythagoras :
    ‖compression (reversalStageZeroOrbitClosedRange observation nontrivial)
        stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
        (reversalStageZeroOrbitIdentitySeed observation nontrivial)‖ ^ 2 +
      ‖reversalStageZeroProjectedExternal observation nontrivial‖ ^ 2 =
      ‖reversalIntegralGraphOrbit observation nontrivial (delta 1)‖ ^ 2 := by
  rw [← reversalStageZeroExternalDefect_eq_projectedExternal]
  exact norm_sq_compression_add_externalDefect
    (reversalStageZeroOrbitClosedRange observation nontrivial)
    stageZeroOwnerFreeGraphTargetAction.toLinearIsometry
    (reversalStageZeroOrbitIdentitySeed observation nontrivial)

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
