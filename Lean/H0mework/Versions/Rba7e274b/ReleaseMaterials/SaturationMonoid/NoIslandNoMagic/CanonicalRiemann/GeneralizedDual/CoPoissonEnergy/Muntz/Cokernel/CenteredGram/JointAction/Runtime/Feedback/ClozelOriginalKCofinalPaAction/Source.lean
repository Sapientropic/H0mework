import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaSourceKernel
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalRAction.Source
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
namespace D
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombFirstFullSourceDynamics
 (input raw raw_xi_source raw_successor next_pair original_runtime_whole original_root_future)
end D
namespace P
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombPhysicalAction (R)
end P
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalRAction (parameter_rightQuarter original_R_direct)
end Paid
local instance sourceComplete : CompleteSpace BurnolPaAmbientCarrier := physicalComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def actualPa (ordinal : Nat) : BurnolPaAmbientCarrier := E (D.raw observation nontrivial half depth ordinal)

theorem actualPa_mem (ordinal : Nat) : actualPa observation nontrivial half depth ordinal ∈
 burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _

theorem actualPa_source_normal (ordinal : Nat) (g : BurnolPaAmbientCarrier)
 (inside : g ∈ burnolCompactCoPoissonClosedRange) :
 inner ℂ g (actualPa observation nontrivial half depth (ordinal+1)) =
 -(∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (observation.coordinate/2) t *
  inner ℂ (g : BurnolL2) (burnolMultiplicativeDilation (-t/2)
   ((D.input observation nontrivial half depth ordinal).1 + (D.input observation nontrivial half depth ordinal).2))) := by
 change inner ℂ g (E (D.raw observation nontrivial half depth (ordinal+1))) = _
 rw [D.raw_successor, Paid.original_R_direct]
 exact ambient_R_normal (observation.coordinate/2) (Paid.parameter_rightQuarter observation half) _ g inside

-- This normal equation is tested on the whole original closed Pa space.
theorem actualPa_kernel_unique (ordinal : Nat) (candidate : BurnolPaAmbientCarrier)
 (belongs : candidate ∈ burnolCompactCoPoissonClosedRange)
 (normal : ∀ g : BurnolPaAmbientCarrier, g ∈ burnolCompactCoPoissonClosedRange →
  inner ℂ g candidate =
  -(∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (observation.coordinate/2) t *
   inner ℂ (g : BurnolL2) (burnolMultiplicativeDilation (-t/2)
    ((D.input observation nontrivial half depth ordinal).1 + (D.input observation nontrivial half depth ordinal).2)))) :
 candidate = actualPa observation nontrivial half depth (ordinal+1) := by
 have difference : candidate - actualPa observation nontrivial half depth (ordinal+1) ∈
  burnolCompactCoPoissonClosedRange :=
  burnolCompactCoPoissonClosedRange.toSubmodule.sub_mem belongs (actualPa_mem observation nontrivial half depth (ordinal+1))
 have same := (normal _ difference).trans (actualPa_source_normal observation nontrivial half depth ordinal _ difference).symm
 have zero : inner ℂ (candidate - actualPa observation nontrivial half depth (ordinal+1))
  (candidate - actualPa observation nontrivial half depth (ordinal+1)) = 0 := by
  rw [inner_sub_right, same, sub_self]
 exact sub_eq_zero.mp (inner_self_eq_zero.mp zero)

end

section
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open SourceGeneratedScalarDifferentialResidual SourceGeneratedObservationAction
open scoped InnerProductSpace Topology
local instance fibreComplete : CompleteSpace BurnolPaAmbientCarrier := physicalComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem E_retract (value : BurnolL2) : E ((E value : BurnolPaAmbientCarrier) : BurnolL2) = E value := by
 change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection ((E value : BurnolPaAmbientCarrier) : BurnolL2)) = E value
 have physical : burnolEvenAmbientProjection ((E value : BurnolPaAmbientCarrier) : BurnolL2) = E value :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 rw [physical]
 exact burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr
  (Submodule.starProjection_apply_mem _ _)

def invisible (value : BurnolL2) : BurnolL2 := value - (E value : BurnolL2)
theorem invisible_mem (value : BurnolL2) : invisible value ∈ E.toLinearMap.ker := by
 change E (value - (E value : BurnolL2)) = 0
 rw [map_sub, E_retract, sub_self]

theorem actual_defect_value (ordinal : Nat) :
 actualPa observation nontrivial half depth (ordinal+1) -
 E (P.R observation nontrivial half (actualPa observation nontrivial half depth ordinal : BurnolL2)) =
 E (P.R observation nontrivial half (invisible (D.raw observation nontrivial half depth ordinal))) := by
 change E (D.raw observation nontrivial half depth (ordinal+1)) -
  E (P.R observation nontrivial half (E (D.raw observation nontrivial half depth ordinal) : BurnolL2)) = _
 rw [D.raw_successor]
 exact (map_sub E _ _).symm.trans (congrArg E.toFun (map_sub (P.R observation nontrivial half) _ _).symm)

theorem actual_defect_fibre (ordinal : Nat) :
 canonicalResidual E.toLinearMap (D.raw observation nontrivial half depth (ordinal+1)) -
 canonicalResidual E.toLinearMap
  (P.R observation nontrivial half (actualPa observation nontrivial half depth ordinal : BurnolL2)) =
 actionDefect (P.R observation nontrivial half).toLinearMap E.toLinearMap
  ⟨invisible (D.raw observation nontrivial half depth ordinal), invisible_mem _⟩ := by
 rw [D.raw_successor]
 exact fibre_action_equation (P.R observation nontrivial half).toLinearMap E.toLinearMap
  (D.raw observation nontrivial half depth ordinal) (actualPa observation nontrivial half depth ordinal : BurnolL2)
  (E_retract _).symm

theorem actual_joint_fibre (ordinal : Nat) (other : BurnolL2) :
 canonicalResidual (jointObservation (P.R observation nontrivial half).toLinearMap E.toLinearMap)
  (D.raw observation nontrivial half depth ordinal) =
 canonicalResidual (jointObservation (P.R observation nontrivial half).toLinearMap E.toLinearMap) other ↔
 actualPa observation nontrivial half depth ordinal = E other ∧
 actualPa observation nontrivial half depth (ordinal+1) = E (P.R observation nontrivial half other) := by
 have generated := joint_fibre_iff (P.R observation nontrivial half).toLinearMap E.toLinearMap
  (D.raw observation nontrivial half depth ordinal) other
 exact generated.trans (and_congr Iff.rfl (by rw [actualPa, D.raw_successor]; rfl))

theorem actual_Pa_forcing (ordinal : Nat) :
 HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2)
  (paired (D.raw observation nontrivial half depth (ordinal+1)))))
  ((observation.coordinate/2-1/4) • Q (sibling (D.raw observation nontrivial half depth (ordinal+1))) +
   (1/2 : ℂ) • (Q (D.raw observation nontrivial half depth ordinal)-Q (fourierL2 (D.raw observation nontrivial half depth ordinal)))) 0 ∧
 HasDerivAt (fun h : ℝ => Q (burnolMultiplicativeDilation (-h/2)
  (sibling (D.raw observation nontrivial half depth (ordinal+1)))))
  ((observation.coordinate/2-1/4) • Q (paired (D.raw observation nontrivial half depth (ordinal+1))) +
   (1/2 : ℂ) • (Q (D.raw observation nontrivial half depth ordinal)+Q (fourierL2 (D.raw observation nontrivial half depth ordinal)))) 0 := by
 rw [D.raw_successor, Paid.original_R_direct]
 exact ambient_R_Pa_forcing (observation.coordinate/2) (Paid.parameter_rightQuarter observation half) _

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCofinalPaAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
