import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMObservable
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginAction

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMasslessCurrent
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 Stage9C.Material.SpinPair CanonicalGradedSpatialSource
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open StageNineP286GaugeConnectionVariation
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumStaticPoleResponse PreparationVacuumFullPoleContinuation
open PreparationVacuumRestModeCoupling
open PreparationVacuumPhysicalConstraint114 PreparationVacuumRawJointFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalActualLegNormalization
open PreparationPhysicalNativePoleChargeReturn PreparationVacuumLowerClassical
open ActualEMObservable ActualElectronOwnerTest
open scoped Matrix BigOperators Topology
attribute [local irreducible] sourceActualPreparedCurrent actualRestNativeComplexForcingCovector
  fullNativeOrigin actualElectronFieldTest

private theorem origin_held_read (v : Fin 289→ℂ)
    (held : ∀i : Fin 289,PreparationVacuumPhysicalConstraint114.sourceHeldUnsupported i→v i=0) :
    fullNativeOrigin.transpose*ᵥv=
      Pi.single 0 ((3/10:ℂ)*rootTwo*(v 21-v 34))+
      Pi.single 1 ((3/10:ℂ)*rootTwo*(v 21-v 34)) := by
  let flag : Fin 289→Bool:=fun (i : Fin 289)=>
    !(decide (((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i))
  let terms : List SourceTerm:=[
    ⟨0,21,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨1,21,⟨0,0,0,0⟩,⟨⟨0,(3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨0,34,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩,
    ⟨1,34,⟨0,0,0,0⟩,⟨⟨0,(-3/10:ℚ)⟩,⟨0,0⟩⟩⟩]
  have selected : columnTerms flag (reflectedTerms fullNativeOriginTerms)=terms := by decide +kernel
  have supported : projectionMatrix flag*ᵥv=v := by
    funext i
    simp only [projectionMatrix,Matrix.mulVec_diagonal]
    by_cases h : PreparationVacuumPhysicalConstraint114.sourceHeldUnsupported i
    · have support:=held i h
      simp only [support,mul_zero]
    · have outside : ¬(((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i) := h
      have on : flag i=true := by
        have value : decide (((73:ℕ) ≤ Fin.val i ∧ Fin.val i < 121)  ∨  145 ≤ Fin.val i)=false :=
          decide_eq_false_iff_not.mpr outside
        dsimp only [flag]
        rw [value]
        rfl
      simp only [on,if_true,one_mul]
  have projected : fullNativeOrigin.transpose*projectionMatrix flag=sourceMatrix terms 0 := by
    calc
      _=sourceMatrix (reflectedTerms fullNativeOriginTerms) 0*projectionMatrix flag := by
        rw [reflectedTerms_value,neg_zero,←fullNativeOrigin_generated]
      _=sourceMatrix (columnTerms flag (reflectedTerms fullNativeOriginTerms)) 0 :=
        (columnTerms_value _ _ _).symm
      _=_ := by rw [selected]
  rw [←supported,Matrix.mulVec_mulVec,projected,supported]
  norm_num [terms,sourceMatrix,SourceTerm.matrix,Matrix.add_mulVec,Matrix.zero_mulVec,
    Matrix.single_mulVec,Powers.value,coefficientValue]
  ext i
  simp only [Pi.single_apply,Function.update_apply,Pi.zero_apply,Pi.add_apply]
  split_ifs  <;> ring

/-- Every native gauge current is read against the entire original five-mode static carrier. -/
def actualBareMasslessWeight (point : BasePoint) (left right : RestStateIndex) : ℂ :=
  (3/10:ℂ)*rootTwo*(actualRestNativeComplexForcingCovector point left right 21-
    actualRestNativeComplexForcingCovector point left right 34)

theorem actualBareMasslessCurrent_generated (point : BasePoint) (left right : RestStateIndex) :
    fullNativeOrigin.transpose*ᵥactualRestNativeComplexForcingCovector point left right=
      Pi.single 0 (actualBareMasslessWeight point left right)+
      Pi.single 1 (actualBareMasslessWeight point left right) := by
  apply origin_held_read
  intro i hi
  have outside : i.val < 9  ∨  57 ≤ i.val := by
    unfold PreparationVacuumPhysicalConstraint114.sourceHeldUnsupported at hi
    omega
  simp only [actualRestNativeComplexForcingCovector,
    actualRestNativeForcingCovector_supported _ _ _ _ _ outside,
    Complex.ofReal_zero,mul_zero,add_zero]

private theorem gaugeDensity_smul (mu : Fin 4) (a : ℝ) (direction : P286LieBlockData) :
    sourceGaugeDensityAction mu (a • direction)=(a:ℂ) • sourceGaugeDensityAction mu direction := by
  unfold sourceGaugeDensityAction
  rw [p286LieBlockEmbed_real_smul,diracExteriorMotherLieAction_real_smul,LinearMap.comp_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- The native massless gauge coupling is generated by the actual spatial current, including the source coframe weight. -/
theorem actualBareMasslessWeight_current (point : BasePoint) (left right : RestStateIndex) :
    actualBareMasslessWeight point left right=
      (3/10:ℂ)*rootTwo*(ActionNormalization.phaseMomentum:ℂ)*(lapse:ℂ)*
        sourceKernelCurrentMixing left right := by
  have first : actualRestNativeComplexForcingCovector point left right 21=
      (2:ℂ)*(lapse:ℂ)*(ActionNormalization.phaseMomentum:ℂ)*sourceRestSpatialMixing 1 1 left right := by
    change actualRestNativeComplexForcingCovector point left right (gaugeSlot 1 0)=_
    rw [actualRestNativeComplexForcingCovector_gaugeSlot,sourceNativeOrigin_unit_zero,
      ←actualRestState_gaugeDensity_mixing 1 ((2:ℝ) • sourceColorP286Generator 1) point left right,
      gaugeDensity_smul,sourceGaugeDensityAction_normal]
    simp only [LinearMap.smul_apply,map_smul,sourceGaugeDensityWeight,Fin.reduceEq,if_false]
    rw [actualRestState_spatial_current]
    push_cast
    ring
  have second : actualRestNativeComplexForcingCovector point left right 34=
      (2:ℂ)*(lapse:ℂ)*(ActionNormalization.phaseMomentum:ℂ)*sourceRestSpatialMixing 2 0 left right := by
    change actualRestNativeComplexForcingCovector point left right (gaugeSlot 2 1)=_
    rw [actualRestNativeComplexForcingCovector_gaugeSlot,sourceNativeOrigin_unit_one,
      ←actualRestState_gaugeDensity_mixing 2 ((2:ℝ) • sourceColorP286Generator 0) point left right,
      gaugeDensity_smul,sourceGaugeDensityAction_normal]
    simp only [LinearMap.smul_apply,map_smul,sourceGaugeDensityWeight,Fin.reduceEq,if_false]
    rw [actualRestState_spatial_current]
    push_cast
    ring
  simp only [actualBareMasslessWeight,first,second,sourceKernelCurrentMixing,
    Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

theorem actualBareMasslessWeight_clock (point : BasePoint) (left right : RestStateIndex) :
    (frequency:ℂ)*actualBareMasslessWeight point left right=
      (3/5:ℂ)*rootTwo*(ActionNormalization.phaseMomentum:ℂ)*(lapse:ℂ)*Complex.I*
        (sourceRestPoleEnergy (sourceRestStatePole left)-sourceRestPoleEnergy (sourceRestStatePole right))*
        sourceRestChargeMixing 2 left right := by
  rw [actualBareMasslessWeight_current]
  have clock:=sourceKernelCurrent_charge_commutator left right
  linear_combination (3/10:ℂ)*rootTwo*(ActionNormalization.phaseMomentum:ℂ)*(lapse:ℂ)*clock

/-- Every bare diagonal rest state has the source's computed zero static gauge-pole coupling; prepared quantum corrections remain below. -/
theorem actualBareMasslessWeight_diagonal (point : BasePoint) (state : RestStateIndex) :
    actualBareMasslessWeight point state state=0 := by
  rw [actualBareMasslessWeight_current,sourceKernelCurrentMixing_generated]
  simp only [if_true]
  rcases state with ⟨side,state⟩
  fin_cases state  <;> norm_num [sourceKernelCurrentBlock]

def actualPreparedMasslessWeight (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) : ℂ :=
  ∑a : RestStateIndex,∑b : RestStateIndex,
    sourceActualPreparedWeight 0 0 sideL 0 sideR 0 a b*actualOriginWeight q 0 0 a b mu S

/-- All64 original preparations feed the same source-generated massless current carrier. -/
theorem actualPreparedMasslessCurrent_generated (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) :
    fullNativeOrigin.transpose*ᵥsourceActualPreparedCurrent q 0 0 sideL 0 sideR 0 mu S=
      Pi.single 0 (actualPreparedMasslessWeight q sideL sideR mu S)+
      Pi.single 1 (actualPreparedMasslessWeight q sideL sideR mu S) := by
  simp only [sourceActualPreparedCurrent,Matrix.mulVec_sum,Matrix.mulVec_smul,returnedCurrentWindow_zero,
    actual_origin_kernel_read,smul_add]
  ext i
  by_cases h0 : i=0
  · subst i
    simp only [actualPreparedMasslessWeight,actualOriginWeight,Pi.add_apply,Pi.single_apply,
      Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
    norm_num
  · by_cases h1 : i=1
    · subst i
      simp only [actualPreparedMasslessWeight,actualOriginWeight,Pi.add_apply,Pi.single_apply,
        Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
      norm_num
    · simp only [Pi.add_apply,Pi.single_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,if_neg h0,if_neg h1,mul_zero,add_zero,Finset.sum_const_zero]

/-- Independently normalized unit legs retain the full source correction in every massless coordinate. -/
theorem actualUnitMasslessCurrent_generated (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    fullNativeOrigin.transpose*ᵥemUnitSourceCurrent q sideL sideR mu S=
      sourceActualLegNormalization q sideL 0 sideR 0 •
        ((Pi.single 0 (actualPreparedMasslessWeight q sideL sideR mu S)+
          Pi.single 1 (actualPreparedMasslessWeight q sideL sideR mu S))-
          fullNativeOrigin.transpose*ᵥemUnitSourceCorrection q sideL sideR mu S) := by
  rw [em_unit_source_current_return q sideL sideR mu S hz hw,Matrix.mulVec_smul,
    Matrix.mulVec_sub,actualPreparedMasslessCurrent_generated]

/-- This is one static inverse on the raw unit source; both endpoints keep their original corrections. -/
theorem actualUnitStaticResidue_generated (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    staticResidue (emUnitSourceCurrent q sideL sideR mu S)=
      fullNativeOrigin*ᵥ(staticInverse*ᵥ(sourceActualLegNormalization q sideL 0 sideR 0 •
        ((Pi.single 0 (actualPreparedMasslessWeight q sideL sideR mu S)+
          Pi.single 1 (actualPreparedMasslessWeight q sideL sideR mu S))-
          fullNativeOrigin.transpose*ᵥemUnitSourceCorrection q sideL sideR mu S))) := by
  rw [staticResidue,actualUnitMasslessCurrent_generated q sideL sideR mu S hz hw]

private theorem unit_current_unsupported (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (i : Fin 289) (held : sourceHeldUnsupported i) :
    emUnitSourceCurrent q sideL sideR mu S i=0 := by
  have kernel (age : ℝ) : actualJointKernel q 0 0 age i=0 := by
    simp only [actualJointKernel,sourceHeld_rawReader_zero i held,mul_zero,zero_mul]
  have fieldKernel : actualElectronFieldKernel q mu S (Pi.single i 1)=0 := by
    simp only [actualElectronFieldKernel,sum_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply,Pi.single_apply,ite_smul,one_smul,zero_smul,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    have vanish (t : ℝ) : laplaceWeight mu t • (0 : H→L[ℂ]H)=0 := by
      exact @smul_zero ℂ (H→L[ℂ]H) _ _ (laplaceWeight mu t)
    simp only [kernel,vanish,intervalIntegral.integral_zero]
  rw [emUnitSourceCurrent,emUnitSourceTest,ContinuousLinearMap.comp_apply,fieldKernel,map_zero]

def actualUnitMasslessWeight (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) : ℂ :=
  (3/10:ℂ)*rootTwo*(emUnitSourceCurrent q sideL sideR mu S 21-emUnitSourceCurrent q sideL sideR mu S 34)

/-- The original full current has one generated coupling, even after both complete external-leg defects. -/
theorem actualUnitMasslessCurrent_complete (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) :
    fullNativeOrigin.transpose*ᵥemUnitSourceCurrent q sideL sideR mu S=
      Pi.single 0 (actualUnitMasslessWeight q sideL sideR mu S)+
      Pi.single 1 (actualUnitMasslessWeight q sideL sideR mu S) :=
  origin_held_read _ (unit_current_unsupported q sideL sideR mu S)

end LowEnergy.GaussComposite.ActualMasslessCurrent
