import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberPreparedSector

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberSector
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussDensityCore
open CanonicalPreparationCore CanonicalPreparationCore.Completed
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPreparedCurrent PreparationVacuumLocalizedYukawa PreparationVacuumNativeClosure
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open ActualDressedSourcePreparation
open GaussComposite.SourceGraph
open FullYSourceCutoffVolterra
open scoped Topology
attribute [local irreducible] numberTwoProjection sourceLeg sourceDressedUnit

/-- The original dense local source completion preserves the computed N2 creation sector. -/
theorem source_leg_N2 (x : sourceLocalSpace) :
    numberTwoProjection (sourceLeg true 1 0 x)=sourceLeg true 1 0 x := by
  refine localCore_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [sourceLeg_core,legTest_embed]
  exact source_creation_test_N2 f

/-- The actual existing creation normalization changes no occupation sector. -/
theorem actual_created_unit_N2 (epsilon : ℝ) (precision : 0<epsilon) :
    numberTwoProjection (sourceDressedUnit epsilon precision)=sourceDressedUnit epsilon precision := by
  have source : sourceLeg true 1 0 (sourcePreparation epsilon precision).point.val=
      completedLeg true 1 0 (sourceProfile epsilon precision) := by
    unfold sourceLeg sourceProfile
    rfl
  have sector : numberTwoProjection (completedLeg true 1 0 (sourceProfile epsilon precision))=
      completedLeg true 1 0 (sourceProfile epsilon precision) := by
    simpa only [source] using! source_leg_N2 (sourcePreparation epsilon precision).point.val
  rw [source_dressed_unit_original]
  simp only [sourceDressedAddition,map_smul,sector]

theorem actual_time_N2_projection_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    physicalTime p F t 0*numberTwoProjection=
      partialEvolution (actualC p F) (actualA p F) 2 t*numberTwoProjection := by
  have zero:=actual_time_N2_grade_return p F t 0
  have one:=actual_time_N2_grade_return p F t 1
  have two:=actual_time_N2_grade_return p F t 2
  have generated:=congrArg₂ (fun A B : H→L[ℂ]H=>A+B)
    (congrArg₂ (fun A B : H→L[ℂ]H=>A+B) zero one) two
  simpa only [numberTwoProjection,mul_add] using! generated

/-- The same original physicalTime now acts on the actual source unit through exactly three original Dyson prefixes. -/
theorem actual_time_created_unit (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ)
    (epsilon : ℝ) (precision : 0<epsilon) :
    physicalTime p F t 0 (sourceDressedUnit epsilon precision)=
      partialEvolution (actualC p F) (actualA p F) 2 t (sourceDressedUnit epsilon precision) := by
  have generated:=congrArg (fun A : H→L[ℂ]H=>A (sourceDressedUnit epsilon precision))
    (actual_time_N2_projection_return p F t)
  simpa only [mul_apply_eq_comp,actual_created_unit_N2] using! generated

end LowEnergy.GaussComposite.ActualDressedNumberSector
