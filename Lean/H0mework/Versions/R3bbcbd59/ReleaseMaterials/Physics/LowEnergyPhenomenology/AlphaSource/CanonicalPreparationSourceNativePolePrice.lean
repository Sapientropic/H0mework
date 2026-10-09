import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativePoleBalance

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPoleConstraintReturn
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumSharedPoleCarrier PreparationVacuumFullPoleContinuation
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumFullOriginResponse PreparationVacuumStaticPoleResponse
open PreparationVacuumPhysicalModeContact PreparationVacuumPhysicalHalfAxis PreparationVacuumPhysicalFeedback
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumGaugeSourceInjection
open MeasureTheory Filter
open scoped Topology BigOperators Matrix Matrix.Norms.Operator
attribute [local irreducible] actualC sourcePoleRead sourceDeviationReader

/-- Price of the actual configuration deviation reader with both original nonreal material resolvents. -/
def configurationDeviationPrice (q : PhysicalResponsePoint) : ℝ:=
  (1/|q.z.im|)*‖sourceDeviationReader 0 q.F‖*(1/|q.w.im|)

private theorem time_norm_le (F : GaussUnitaryHistory.Index) (t : ℝ) :
    ‖SourceFiniteUnitary.time (actualC 0 F) t‖≤1:=by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [SourceFiniteUnitary.time_norm _ (actualC_symmetric 0 F),one_mul]

theorem sourceDeviationKernel_price (q : PhysicalResponsePoint) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourceDeviationKernel q 0 0 t‖≤configurationDeviationPrice q:=by
  have left:=time_norm_le q.F (-t)
  have right:=time_norm_le q.F t
  have leftR:=CanonicalPhysicalResolvent.finite_bound 0 q.F q.z nonrealL
  have rightR:=CanonicalPhysicalResolvent.finite_bound 0 q.F q.w nonrealR
  unfold sourceDeviationKernel configurationDeviationPrice
  calc
    _≤‖SourceFiniteUnitary.time (actualC 0 q.F) (-t)‖*
        ‖CanonicalPhysicalResolvent.finiteResolvent 0 q.F q.z‖*‖sourceDeviationReader 0 q.F‖*
        ‖CanonicalPhysicalResolvent.finiteResolvent 0 q.F q.w‖*‖SourceFiniteUnitary.time (actualC 0 q.F) t‖:=by
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact norm_mul_le _ _
    _≤1*(1/|q.z.im|)*‖sourceDeviationReader 0 q.F‖*(1/|q.w.im|)*1:=by gcongr
    _= _:=by ring

theorem sourceDeviationRead_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (t : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourcePoleRead q.epsilon q.precision 0 0 l r (sourceDeviationKernel q 0 0 t)‖≤configurationDeviationPrice q:=by
  calc
    _≤‖sourcePoleRead q.epsilon q.precision 0 0 l r‖*‖sourceDeviationKernel q 0 0 t‖:=
      (sourcePoleRead q.epsilon q.precision 0 0 l r).le_opNorm _
    _≤1*‖sourceDeviationKernel q 0 0 t‖:=mul_le_mul_of_nonneg_right
      (sourcePoleRead_price q.epsilon q.precision 0 0 l r) (norm_nonneg _)
    _≤_:=by simpa only [one_mul] using sourceDeviationKernel_price q t nonrealL nonrealR

theorem configurationDeviationWindow_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖configurationDeviationWindow q l r T‖≤configurationDeviationPrice q*|T|:=by
  simpa only [sub_zero,configurationDeviationWindow] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(0:ℝ)) (b:=T) (fun t _=>sourceDeviationRead_price q l r t nonrealL nonrealR)

theorem actualOriginWeight_native_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖actualOriginWeight q 0 0 l r 0 T-nativeContactWindow q l r T‖≤configurationDeviationPrice q*|T|:=by
  rw [actualOriginWeight_native q l r T nonrealL nonrealR]
  simpa only [sub_sub_cancel_left,norm_neg] using configurationDeviationWindow_price q l r T nonrealL nonrealR

/-- This complete native vector comes from the original five-channel Schur residue. -/
def sourcePoleVector : Fin 289→ℂ:=fullNativeOrigin*ᵥ
  (Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen)+Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen))

theorem actualResidue_sourcePoleVector (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ) :
    staticResidue (actualCurrent q 0 0 l r 0 T)=actualOriginWeight q 0 0 l r 0 T • sourcePoleVector:=by
  rw [actualCurrent_staticResidue]
  unfold sourcePoleVector
  rw [←Matrix.mulVec_smul]
  congr 1
  ext i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  split_ifs <;> ring

theorem actualResidue_native_price (q : PhysicalResponsePoint) (l r : RestStateIndex) (T : ℝ)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖staticResidue (actualCurrent q 0 0 l r 0 T)-nativeContactWindow q l r T • sourcePoleVector‖≤
      configurationDeviationPrice q*|T| *‖sourcePoleVector‖:=by
  rw [actualResidue_sourcePoleVector,←sub_smul,norm_smul]
  exact mul_le_mul_of_nonneg_right (actualOriginWeight_native_price q l r T nonrealL nonrealR) (norm_nonneg _)

end LowEnergy.PreparationVacuumPoleConstraintReturn
