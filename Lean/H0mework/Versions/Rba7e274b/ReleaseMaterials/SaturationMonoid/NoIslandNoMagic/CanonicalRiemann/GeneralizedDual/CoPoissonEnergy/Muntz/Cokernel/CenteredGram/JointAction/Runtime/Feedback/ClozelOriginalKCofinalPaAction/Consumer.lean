import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalPaAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
section
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace Topology
local instance consumerComplete : CompleteSpace BurnolPaAmbientCarrier := physicalComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_native_p_Pa_split (ordinal : Nat) :
 (actualPa observation nontrivial half depth (ordinal+1) : BurnolL2) +
 (Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2) =
 (D.input observation nontrivial half depth (ordinal+1)).1 := by
 have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
  (burnolEvenAmbientProjection (P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal)))
 have ambient := congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) split
 have native := congrArg (fun pair : BurnolL2 × BurnolL2 => pair.1)
  (D.next_pair observation nontrivial half depth ordinal)
 change (E (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2) +
  (Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2) = _
 rw [D.raw_successor]
 exact ambient.trans native.symm

theorem actual_complete_reconstruction (ordinal : Nat) :
 ((actualPa observation nontrivial half depth (ordinal+1) : BurnolL2) +
  (Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)) +
 (D.input observation nontrivial half depth (ordinal+1)).2 =
 D.raw observation nontrivial half depth (ordinal+1) :=
 congrArg (fun value : BurnolL2 => value + (D.input observation nontrivial half depth (ordinal+1)).2)
  (actual_native_p_Pa_split observation nontrivial half depth ordinal)

-- The kernel read and forcing velocities are consumed at the same original generated cofinal packet.
theorem consume_actual_Pa_B (ordinal tick : Nat) (g : BurnolPaAmbientCarrier)
 (inside : g ∈ burnolCompactCoPoissonClosedRange) (other : BurnolL2)
 (history : List PUnit.{1}) (target : Nat) :
 type_of% (D.next_pair observation nontrivial half depth ordinal) ∧
 type_of% (actualPa_source_normal observation nontrivial half depth ordinal g inside) ∧
 type_of% (actualPa_mem observation nontrivial half depth (ordinal+1)) ∧
 type_of% (actual_defect_value observation nontrivial half depth ordinal) ∧
 type_of% (actual_defect_fibre observation nontrivial half depth ordinal) ∧
 type_of% (actual_joint_fibre observation nontrivial half depth ordinal other) ∧
 type_of% (actual_Pa_forcing observation nontrivial half depth ordinal) ∧
 type_of% (actual_complete_reconstruction observation nontrivial half depth ordinal) ∧
 type_of% (D.original_runtime_whole observation nontrivial half depth tick) ∧
 type_of% (D.original_root_future observation nontrivial half depth ordinal history target) :=
 ⟨D.next_pair _ _ _ _ _, actualPa_source_normal observation nontrivial half depth ordinal g inside, actualPa_mem _ _ _ _ _,
  actual_defect_value _ _ _ _ _, actual_defect_fibre _ _ _ _ _, actual_joint_fibre _ _ _ _ _ _,
  actual_Pa_forcing _ _ _ _ _, actual_complete_reconstruction _ _ _ _ _,
  D.original_runtime_whole _ _ _ _ _, D.original_root_future _ _ _ _ _ _ _⟩

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
