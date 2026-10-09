import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticMixedChannel
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationOriginalHessianReturn
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalFieldChannel
open PreparationVacuumOriginalGreenFeedback SourcePropagationNativeActionHessian
open scoped Matrix BigOperators Topology

def channelFactor (k : ℂ) : ℂ := 1+(7957/6120:ℂ)*k^2+(45/136:ℂ)*k^4
def channelDenominator (k : ℂ) : ℂ := k^2*channelFactor k

theorem channel_drive_generated (k : ℂ) :
    channelDrive k=channelDenominator k • (Pi.single 21 1 : Fin 289→ℂ) :=by
  ext i
  simp only [channelDrive,channelDenominatorTerms,sourceMatrix,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,SourceTerm.matrix,Matrix.add_apply,
    Matrix.single_apply,Powers.value,staticAxis,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,coefficientValue,
    Rat.cast_zero,Rat.cast_one,Rat.cast_div,zero_mul,add_zero,
    pow_zero,one_mul,mul_one,Pi.smul_apply,smul_eq_mul]
  by_cases h : i=21
  · subst i; simp [channelDenominator,channelFactor];ring
  · simp [h,Ne.symm h]

private theorem numerator_active_certificate :
    fastNormalizeTerms (productTerms (projectionTerms activeFlag) channelNumeratorTerms++
      negativeTerms channelNumeratorTerms)=[] :=by decide +kernel

theorem channel_active (k : ℂ) : activeProjection*ᵥchannelNumerator k=channelNumerator k :=by
  have actual:=normalization_equal (productTerms (projectionTerms activeFlag) channelNumeratorTerms)
    channelNumeratorTerms numerator_active_certificate (staticAxis k)
  rw [productTerms_value,projectionTerms_value] at actual
  exact congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>fun i=>A i 0) actual

/-- A generated mixed mode of the original nine-field action, including all non-gauge components. -/
def channelNativeNumerator (k : ℂ) : Fin 289→ℂ :=
  originalChange (staticAxis k)*ᵥchannelNumerator k

theorem channel_native_equation (k : ℂ) :
    nativeFourierHessian nativeHessian (staticAxis k)*ᵥchannelNativeNumerator k=
      channelDenominator k • (originalRowLift (staticAxis k)*ᵥ(Pi.single 21 1 : Fin 289→ℂ)) :=by
  rw [nativeActionFourierHessian_original,channelNativeNumerator]
  calc
    _=(originalJacobi (staticAxis k)*originalChange (staticAxis k)*activeProjection)*ᵥchannelNumerator k :=by
      rw [←Matrix.mulVec_mulVec,channel_active,Matrix.mulVec_mulVec]
    _=(originalRowLift (staticAxis k)*activeKernel (staticAxis k))*ᵥchannelNumerator k :=by
      rw [original_active_intertwiner]
    _= _ :=by rw [←Matrix.mulVec_mulVec,channel_actual_active,channel_drive_generated,Matrix.mulVec_smul]

theorem channel_factor_at_zero : channelFactor 0=1 :=by simp [channelFactor]
theorem channel_factor_continuous : Continuous channelFactor :=by unfold channelFactor;fun_prop

theorem channel_zero_native :
    nativeFourierHessian nativeHessian (staticAxis 0)*ᵥchannelNativeNumerator 0=0 :=by
  rw [channel_native_equation];simp [channelDenominator]

theorem channel_numerator21 : channelNumerator 0 21=-(9023/50000:ℂ)*rootTwo*rootFifteen :=by
  norm_num [channelNumerator,channelNumeratorTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    Powers.value,staticAxis,coefficientValue,Fin.ext_iff]

theorem channel_numerator_nonzero : channelNumerator 0≠0 :=by
  intro zero
  have at21:=congrFun zero 21
  rw [channel_numerator21] at at21
  have two : rootTwo≠0:=by unfold rootTwo;exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)))
  have fifteen : rootFifteen≠0:=by unfold rootFifteen;exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<15)))
  norm_num [two,fifteen] at at21

theorem channel_native_nonzero : channelNativeNumerator 0≠0 :=by
  intro zero
  have recover:=congrArg (fun v : Fin 289→ℂ=>originalInverse (staticAxis 0)*ᵥv) zero
  rw [channelNativeNumerator,Matrix.mulVec_mulVec,original_inverse_change,Matrix.one_mulVec,
    Matrix.mulVec_zero] at recover
  exact channel_numerator_nonzero recover

end LowEnergy.PreparationVacuumPhysicalFieldChannel
