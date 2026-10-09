import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFiniteNoether

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNumberField
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumGradedTransport PreparationVacuumJointFieldResponse
open PreparationVacuumUncutYukawa
open ActualDressedNumberSector
open NativeHistoryGrade (Label projection)
open scoped BigOperators InnerProductSpace
local instance labelFinite : Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] physicalFrame sourceAssembly jointCompression jointY

private theorem source_frame_projection (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (g h : Label) (i : PhysicalBasisIndex p F) :
    projection g (physicalFrame p F (h,i))=if g=h then physicalFrame p F (h,i) else 0 := by
  have original:=congrArg (fun A : H→L[ℂ]H=>A ((physicalBasis p F i).val))
    (NativeHistoryGrade.projection_product g h)
  by_cases same : g=h
  · subst g
    simpa only [physicalFrame,mul_apply_eq_comp,if_true] using original
  · simpa only [physicalFrame,mul_apply_eq_comp,if_neg same,zero_apply] using original

private theorem source_frame_rank_one_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (g h : Label) (i j : PhysicalBasisIndex p F) :
    Commute (projection g) (InnerProductSpace.rankOne ℂ (physicalFrame p F (h,i)) (physicalFrame p F (h,j))) := by
  show projection g*InnerProductSpace.rankOne ℂ (physicalFrame p F (h,i)) (physicalFrame p F (h,j))=
    InnerProductSpace.rankOne ℂ (physicalFrame p F (h,i)) (physicalFrame p F (h,j))*projection g
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul]
  have paired:=NativeHistoryGrade.projection_symmetric g (physicalFrame p F (h,j)) x
  change inner ℂ (projection g (physicalFrame p F (h,j))) x=
    inner ℂ (physicalFrame p F (h,j)) (projection g x) at paired
  rw [←paired,source_frame_projection,source_frame_projection]
  by_cases same : g=h
  · simp only [if_pos same]
  · simp only [if_neg same,smul_zero,inner_zero_left,zero_smul]

/-- This is the original labelled sourceAssembly, with its original physical frame and arbitrary original entries. -/
theorem source_assembly_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (entries : PhysicalBasisIndex p F→PhysicalBasisIndex p F→ℂ) (g : Label) :
    Commute (projection g) (sourceAssembly p F entries) := by
  show projection g*sourceAssembly p F entries=sourceAssembly p F entries*projection g
  simp only [sourceAssembly,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun A : H→L[ℂ]H=>entries i j • A) (source_frame_rank_one_blocks p F g h i j).eq

/-- The actual full-field compression itself preserves every original number/grade block. -/
theorem actual_joint_compression_blocks (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : PreparationVacuumMixedFieldReturn.Field289) (g : Label) :
    Commute (projection g) (jointCompression p F h) := by
  unfold jointCompression
  exact source_assembly_blocks p F _ g

theorem actual_joint_Y_N2G0_range (h : PreparationVacuumMixedFieldReturn.Field289)
    (phi : CanonicalGradedSpatial.Localizer) :
    numberTwoGrade 1*jointY phi h*numberTwoGrade 0=jointY phi h*numberTwoGrade 0 := by
  rw [jointY_source]
  exact uncut_N2G0_range h phi 1

theorem actual_joint_Y_N2G1_range (h : PreparationVacuumMixedFieldReturn.Field289)
    (phi : CanonicalGradedSpatial.Localizer) :
    numberTwoGrade 2*jointY phi h*numberTwoGrade 1=jointY phi h*numberTwoGrade 1 := by
  rw [jointY_source]
  exact uncut_N2G1_range h phi 1

theorem actual_joint_Y_N2G2_zero (h : PreparationVacuumMixedFieldReturn.Field289)
    (phi : CanonicalGradedSpatial.Localizer) : jointY phi h*numberTwoGrade 2=0 := by
  rw [jointY_source]
  exact uncut_N2G2_zero h phi 1

theorem actual_joint_Y_raises (h : PreparationVacuumMixedFieldReturn.Field289)
    (phi : CanonicalGradedSpatial.Localizer) :
    GaussYukawaGrade.grade*jointY phi h=jointY phi h*GaussYukawaGrade.grade+jointY phi h := by
  rw [jointY_source]
  exact uncutOperator_raises h phi 1

end LowEnergy.GaussComposite.ActualDressedNumberField
