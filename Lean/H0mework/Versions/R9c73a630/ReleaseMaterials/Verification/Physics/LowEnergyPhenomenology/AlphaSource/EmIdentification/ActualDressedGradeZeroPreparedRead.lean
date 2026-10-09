import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberNoetherRead
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualMixedSourceGrades

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberZero
open GaussCoreHilbert GaussCoreDifferential GaussDensityCore GaussYukawaGrade
open GaussComposite.SourceGraph PreparationVacuumActualPreparedMixed
open ActualDressedSourcePreparation ActualDressedNumberSector
open PreparationVacuumSourcePreparedResponse
open scoped Topology InnerProductSpace
attribute [local irreducible] sourceDressedUnit gradeZeroProjection

/-- The original graph completion preserves the canonical source seed's generated grade0. -/
theorem actual_background_grade_zero (profile : Profile) :
    GaussYukawaGrade.grade (prepared profile)=0 := by
  refine core_dense.induction_on profile (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [prepared_core,grade_core,original_seed_section_grade (seedSection f) _ (seedSection_apply f),map_zero]

theorem actual_background_grade_zero_fixed (profile : Profile) :
    gradeZeroProjection (prepared profile)=prepared profile :=
  grade_zero_fixed _ (actual_background_grade_zero profile)

/-- Consume the already generated completed-leg identity on the same Hilbert carrier. -/
theorem original_completed_leg_grade_zero_fixed (addition : Bool) (a s : Fin 2) (profile : Profile) :
    gradeZeroProjection (completedLeg addition a s profile)=completedLeg addition a s profile := by
  apply GaussUnitaryHistory.inclusion.injective
  rw [←GaussUnitaryHistory.reader_inclusion]
  exact completedLeg_gradeZero addition a s profile

/-- The actual norm normalization keeps the original created state in grade0. -/
theorem actual_created_unit_grade_zero_fixed (epsilon : ℝ) (precision : 0<epsilon) :
    gradeZeroProjection (sourceDressedUnit epsilon precision)=sourceDressedUnit epsilon precision := by
  rw [source_dressed_unit_original]
  simp only [map_smul,original_completed_leg_grade_zero_fixed]

theorem actual_created_unit_grade_zero (epsilon : ℝ) (precision : 0<epsilon) :
    GaussYukawaGrade.grade (sourceDressedUnit epsilon precision)=0 := by
  rw [←actual_created_unit_grade_zero_fixed epsilon precision]
  exact grade_zero_projected _

end LowEnergy.GaussComposite.ActualDressedNumberZero
