import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePhysicalPoleDressedReturn
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceJointSpectralBudget

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleAmputation
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumJointFieldResponse PreparationVacuumCurrentRegularAnchor
open PreparationVacuumMixedFieldReturn GaussCoreHilbert
open scoped Topology InnerProductSpace
attribute [local irreducible] jointGenerator jointResolvent sourcePolePrepared sourcePoleDual
  sourcePoleColumnDefect sourcePoleDualDefect

private theorem columnAmputation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C R : E→L[ℂ] E) (energy z : ℂ) (primal : E)
    (leftInverse : R*(C-z • 1)=1) :
    (energy-z) • R primal=primal-R (C primal-energy • primal) :=by
  have actual:=congrArg (fun A : E→L[ℂ] E=>A primal) leftInverse
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] at actual
  rw [map_sub,map_smul]
  have returned : R (C primal)=primal+z • R primal:=sub_eq_iff_eq_add.mp actual
  rw [returned]
  module

private theorem rowAmputation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C R : E→L[ℂ] E) (energy z : ℂ) (dual : E→L[ℂ] ℂ)
    (rightInverse : (C-z • 1)*R=1) :
    (energy-z) • dual.comp R=dual-(dual.comp C-energy • dual).comp R :=by
  ext primal
  have actual:=congrArg (fun A : E→L[ℂ] E=>A primal) rightInverse
  simp only [mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] at actual
  have read:=congrArg dual actual
  simp only [map_sub,map_smul] at read
  simp only [smul_apply,sub_apply,ContinuousLinearMap.comp_apply]
  linear_combination read

theorem sourceMaterialInverse_left (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (nonreal : z.im≠0) :
    jointResolvent p F z 0*(jointGenerator p F 0 0-z • 1)=1 :=by
  rw [←jointGenerator_spectral_shift,jointResolvent]
  exact Ring.inverse_mul_cancel _ (jointGenerator_unit p F z nonreal)

theorem sourceMaterialInverse_right (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ)
    (nonreal : z.im≠0) :
    (jointGenerator p F 0 0-z • 1)*jointResolvent p F z 0=1 :=by
  rw [←jointGenerator_spectral_shift,jointResolvent]
  exact Ring.mul_inverse_cancel _ (jointGenerator_unit p F z nonreal)

theorem sourcePolePrimal_amputated (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    ((sourceMovingPoleEnergy p state:ℂ)-z) •
        jointResolvent p F z 0 (sourcePolePrepared epsilon precision p state)=
      sourcePolePrepared epsilon precision p state-
        jointResolvent p F z 0 (sourcePoleColumnDefect epsilon precision p state F) :=by
  have actual:=columnAmputation (jointGenerator p F 0 0) (jointResolvent p F z 0)
    (sourceMovingPoleEnergy p state:ℂ) z (sourcePolePrepared epsilon precision p state)
    (sourceMaterialInverse_left p F z nonreal)
  simpa only [sourcePoleColumnDefect] using actual

theorem sourcePoleDual_amputated (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    ((sourceMovingPoleEnergy p state:ℂ)-z) •
        (sourcePoleDual epsilon precision p state).comp (jointResolvent p F z 0)=
      sourcePoleDual epsilon precision p state-
        (sourcePoleDualDefect epsilon precision p state F).comp (jointResolvent p F z 0) :=by
  have actual:=rowAmputation (jointGenerator p F 0 0) (jointResolvent p F z 0)
    (sourceMovingPoleEnergy p state:ℂ) z (sourcePoleDual epsilon precision p state)
    (sourceMaterialInverse_right p F z nonreal)
  simpa only [sourcePoleDualDefect] using actual

theorem sourcePoleMaterialGap_nonzero (p : PhysicalMomentum) (state : RestStateIndex)
    (z : ℂ) (nonreal : z.im≠0) : (sourceMovingPoleEnergy p state:ℂ)-z≠0 :=by
  intro equal
  have im:=congrArg Complex.im equal
  simp only [Complex.sub_im,Complex.ofReal_im,zero_sub,Complex.zero_im,neg_eq_zero] at im
  exact nonreal im

def sourcePoleAmputatedPrimal (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) : H:=
  sourcePolePrepared epsilon precision p state-
    jointResolvent p F z 0 (sourcePoleColumnDefect epsilon precision p state F)

def sourcePoleAmputatedDual (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) : H→L[ℂ] ℂ:=
  sourcePoleDual epsilon precision p state-
    (sourcePoleDualDefect epsilon precision p state F).comp (jointResolvent p F z 0)

theorem sourcePolePrimal_resolvent_return (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    jointResolvent p F z 0 (sourcePolePrepared epsilon precision p state)=
      ((sourceMovingPoleEnergy p state:ℂ)-z)⁻¹ • sourcePoleAmputatedPrimal epsilon precision p state F z :=by
  have actual:=sourcePolePrimal_amputated epsilon precision p state F z nonreal
  have read:=congrArg (fun v : H=>((sourceMovingPoleEnergy p state:ℂ)-z)⁻¹ • v) actual
  simpa only [smul_smul,inv_mul_cancel₀ (sourcePoleMaterialGap_nonzero p state z nonreal),one_smul,
    sourcePoleAmputatedPrimal] using read

theorem sourcePoleDual_resolvent_return (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) (nonreal : z.im≠0) :
    (sourcePoleDual epsilon precision p state).comp (jointResolvent p F z 0)=
      ((sourceMovingPoleEnergy p state:ℂ)-z)⁻¹ • sourcePoleAmputatedDual epsilon precision p state F z :=by
  have actual:=sourcePoleDual_amputated epsilon precision p state F z nonreal
  have read:=congrArg (fun v : H→L[ℂ] ℂ=>((sourceMovingPoleEnergy p state:ℂ)-z)⁻¹ • v) actual
  simpa only [smul_smul,inv_mul_cancel₀ (sourcePoleMaterialGap_nonzero p state z nonreal),one_smul,
    sourcePoleAmputatedDual] using read

theorem sourcePoleAmputatedPrimal_price (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖sourcePoleAmputatedPrimal epsilon precision p state F z‖ ≤
      1+‖jointResolvent p F z 0‖*‖sourcePoleColumnDefect epsilon precision p state F‖ :=by
  unfold sourcePoleAmputatedPrimal
  exact (norm_sub_le _ _).trans ((add_le_add (le_refl _)
    ((jointResolvent p F z 0).le_opNorm _)).trans_eq (by rw [sourcePolePrepared_unit]))

theorem sourcePoleAmputatedDual_price (epsilon : ℝ) (precision : 0 < epsilon) (p : PhysicalMomentum)
    (state : RestStateIndex) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    ‖sourcePoleAmputatedDual epsilon precision p state F z‖ ≤
      1+‖sourcePoleDualDefect epsilon precision p state F‖*‖jointResolvent p F z 0‖ :=by
  unfold sourcePoleAmputatedDual
  have unit : ‖sourcePoleDual epsilon precision p state‖=1 :=by
    rw [sourcePoleDual,innerSL_apply_norm,sourcePolePrepared_unit]
  exact (norm_sub_le _ _).trans ((add_le_add (le_refl _)
    (ContinuousLinearMap.opNorm_comp_le _ _)).trans_eq (by rw [unit]))

end LowEnergy.PreparationVacuumPhysicalPoleAmputation
