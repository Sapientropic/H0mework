import H0mework.Versions.X.Fock.PrimeFieldJoint.CofinalSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceJointDecoderCofinal

open SourceJointFiniteDecoder SourceJointClockGraph
open scoped InnerProductSpace
noncomputable section

local instance finiteComplete (bound : Nat) : CompleteSpace (image bound) :=
  (source_antilipschitz bound).completeSpace_range_clm

local instance wholeComplete : CompleteSpace SourceJointClockGraph.action.range :=
  action_closed_range.isComplete.completeSpace_coe

private theorem subtype_transfer_projection {C : Type*}
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (space : Submodule ℂ C) [CompleteSpace space] (target : C) :
    space.starProjection target = space.subtypeₗᵢ
      (IsometricRetainedTransfer.transfer (Current := C) (Next := space) space.subtypeₗᵢ target) := by
  change space.subtypeL (space.orthogonalProjectionOnto target) = space.subtypeL (space.subtypeL.adjoint target)
  rw [Submodule.adjoint_subtypeL]

theorem finite_projection (bound : Nat) (target : SourceJointClockGraph.Carrier) :
    (image bound).starProjection target = SourceJointFiniteDecoder.action bound (decode bound target) := by
  exact (subtype_transfer_projection (image bound) target).trans (encoded_decode bound target).symm

theorem whole_orthogonal (target value : SourceJointClockGraph.Carrier) :
    inner ℂ (SourceJointClockGraph.residual target) (SourceJointClockGraph.action value) = 0 := by
  rw [residual_formula, action_apply, WithLp.prod_inner_apply]
  change inner ℂ (SourceJointTransfer.wholeResidual (joint target))
    (SourceMassCompletion.action (joint value)) + inner ℂ (0 : ℂ)
      (clock value + SourceMassCompletion.massRead (joint value)) = 0
  rw [inner_zero_left, add_zero]
  exact inner_eq_zero_symm.mp (IsometricRetainedTransfer.residual_orthogonal SourceMassCompletion.action
    (joint target) (joint value))

theorem whole_projection (target : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.action.range.starProjection target =
      SourceJointClockGraph.action (recover target) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨recover target, rfl⟩
  · rintro _ ⟨value, rfl⟩
    change inner ℂ (target - SourceJointClockGraph.action (recover target)) (SourceJointClockGraph.action value) = 0
    exact whole_orthogonal target value

end
end SourceJointDecoderCofinal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
