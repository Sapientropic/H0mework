import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFieldTimeSector
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparedTimePrice

set_option autoImplicit false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedN1Price
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumYukawaTransport
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalN1WardCollapse
open ActualDressedNumberField ActualDressedNumberZero ActualDressedFieldTime
open ActualDressedPreparedPrice FullYSourceCutoffVolterra
open scoped Topology
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] sourceN1Projection jointCompression jointY jointGenerator jointCurrent
  physicalTime actualC actualA

theorem actual_joint_current_number_one (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (force : Field289) :
    sourceN1Projection*(jointCurrent p F z 0 force)*sourceN1Projection=
      (jointCurrent p F z 0 force)*sourceN1Projection := by
  have source:=(jointGenerator_C2 p F z).differentiableAt (by norm_num) |>.hasFDerivAt
  have derivative:=source.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have left:=(derivative.const_mul sourceN1Projection).mul_const sourceN1Projection
  have right:=derivative.mul_const sourceN1Projection
  simpa only [jointCurrent] using (left.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun r=>(actual_joint_generator_number_one p F z (r • force)).symm))).unique right

private theorem actual_joint_C_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointCompression p F 0=actualC p F := by
  have source:=(jointCompression_ray (0:Field289) p F).self_of_nhds
  simpa only [zero_smul,PreparationVacuumGradedTransport.transportedCompression_zero,actualC] using source

private theorem actual_joint_Y_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    jointY (finiteRetainer p F) 0=actualA p F := by
  have zeroOp (A : H→L[ℂ]H) : (0:ℝ) • A=0 := by
    apply ContinuousLinearMap.ext
    intro x
    change (0:ℝ) • (A x)=(0:H)
    exact zero_smul ℝ (A x)
  simp only [jointY,Pi.zero_apply,zeroOp,Finset.sum_const_zero,add_zero,actualA]

theorem actual_time_N1_projection_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    physicalTime p F t 0*sourceN1Projection=
      partialEvolution (actualC p F) (actualA p F) 1 t*sourceN1Projection := by
  simpa only [actual_joint_C_zero,actual_joint_Y_zero] using actual_field_time_N1_projection_return p F 0 t

theorem actual_time_N1_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (v : H) (sector : sourceN1Projection v=v) :
    physicalTime p F t 0 v=partialEvolution (actualC p F) (actualA p F) 1 t v := by
  have source:=congrArg (fun A : H→L[ℂ]H=>A v) (actual_time_N1_projection_return p F t)
  simpa only [mul_apply_eq_comp,sector] using source

theorem actual_time_N1_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (t : ℝ) (v : H) (sector : sourceN1Projection v=v) :
    ‖physicalTime p F t 0 v‖ ≤ occupationPrice 1 ‖actualA p F‖ |t| *‖v‖ := by
  have source:=actual_time_N1_return p F t v sector
  have estimate:=((partialEvolution (actualC p F) (actualA p F) 1 t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (partialEvolution_bound _ _ (actualC_symmetric p F) 1 t) (norm_nonneg v))
  exact (congrArg norm source).le.trans estimate

end LowEnergy.GaussComposite.ActualDressedN1Price
