import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceConstrainedCurrentResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentRegularAnchor
open PreparationVacuumCurrentConstrainedInverse PreparationVacuumCurrentSignalOperator
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumJointFieldResponse PreparationVacuumUncutYukawa
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open scoped Topology BigOperators
attribute [local irreducible] jointGenerator jointCompression jointY jointResolvent jointCurrent

def sourceBaseGenerator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : SourceOp:=jointGenerator p F 0 0

attribute [local irreducible] sourceBaseGenerator

theorem jointGenerator_spectral_shift (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (field : Field289) :
    jointGenerator p F z field=jointGenerator p F 0 field-z • (1 : SourceOp) :=by
  simp only [jointGenerator]
  rw [show ((0 : ℂ) • (1 : SourceOp))=0 from zero_smul ℂ (1 : SourceOp),sub_zero]

theorem jointCurrent_spectral (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointCurrent p F z 0=jointCurrent p F 0 0 :=by
  apply ContinuousLinearMap.ext
  intro field
  exact (jointCurrent_source field p F z).trans (jointCurrent_source field p F 0).symm

def sourceMaterialRadius (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) : ℝ:=
  2*(1+‖sourceBaseGenerator p F‖+extra)

def sourceMaterialSpectrum (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) : ℂ:=
  Complex.I*(sourceMaterialRadius p F extra : ℂ)

theorem sourceMaterialRadius_positive (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    0<sourceMaterialRadius p F extra :=by
  unfold sourceMaterialRadius
  positivity

theorem sourceMaterialSpectrum_nonreal (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    (sourceMaterialSpectrum p F extra).im≠0 :=by
  simp only [sourceMaterialSpectrum,Complex.mul_im,Complex.I_re,Complex.ofReal_im,mul_zero,
    Complex.I_im,Complex.ofReal_re,one_mul,zero_add]
  exact ne_of_gt (sourceMaterialRadius_positive p F extra nonnegative)

private theorem rearrange_source_unit {A : Type*} [Ring A] (a b : A) (actual : a-b=1) : b=a-1 :=by
  apply eq_sub_iff_add_eq.mpr
  have equation:=sub_eq_iff_eq_add.mp actual
  exact (add_comm b 1).trans equation.symm

theorem sourceMaterialResolvent_equation (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    sourceMaterialSpectrum p F extra • jointResolvent p F (sourceMaterialSpectrum p F extra) 0=
      sourceBaseGenerator p F*jointResolvent p F (sourceMaterialSpectrum p F extra) 0-1 :=by
  have actual:=Ring.mul_inverse_cancel (jointGenerator p F (sourceMaterialSpectrum p F extra) 0)
    (jointGenerator_unit p F (sourceMaterialSpectrum p F extra) (sourceMaterialSpectrum_nonreal p F extra nonnegative))
  rw [←jointResolvent] at actual
  rw [jointGenerator_spectral_shift,sub_mul,smul_mul_assoc,one_mul] at actual
  unfold sourceBaseGenerator
  exact rearrange_source_unit _ _ actual

private theorem spectral_inverse_price {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (C R : A) (gamma : ℝ) (positive : 0<gamma) (gap : 2*‖C‖ ≤ gamma) (onePrice : ‖(1 : A)‖ ≤ 1)
    (actual : (Complex.I*(gamma : ℂ)) • R=C*R-1) : ‖R‖ ≤ 2/gamma :=by
  have normalized : ‖(Complex.I*(gamma : ℂ)) • R‖=gamma*‖R‖ :=by
    rw [norm_smul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  have source : gamma*‖R‖ ≤ ‖C‖*‖R‖+1:=by
    rw [←normalized,actual]
    exact (norm_sub_le _ _).trans (add_le_add (norm_mul_le C R) onePrice)
  apply (le_div_iff₀ positive).mpr
  nlinarith [norm_nonneg R]

theorem sourceMaterialResolvent_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (extra : ℝ) (nonnegative : 0 ≤ extra) :
    ‖jointResolvent p F (sourceMaterialSpectrum p F extra) 0‖ ≤ 2/sourceMaterialRadius p F extra :=by
  have gap : 2*‖sourceBaseGenerator p F‖ ≤ sourceMaterialRadius p F extra:=by
    unfold sourceMaterialRadius
    linarith
  have onePrice : ‖(1 : SourceOp)‖ ≤ 1:=by
    change ‖(ContinuousLinearMap.id ℂ _ : SourceOp)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  exact spectral_inverse_price (sourceBaseGenerator p F)
    (jointResolvent p F (sourceMaterialSpectrum p F extra) 0) (sourceMaterialRadius p F extra)
    (sourceMaterialRadius_positive p F extra nonnegative) gap onePrice
    (sourceMaterialResolvent_equation p F extra nonnegative)

end LowEnergy.PreparationVacuumCurrentRegularAnchor
