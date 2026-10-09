import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceWholeCurrent

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalConstraint114
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

/-- These slots are independent original matter/auxiliary restrictions of the held quantum insertion. -/
def sourceHeldUnsupported (i : Fin 289) : Prop := (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val

private theorem unsupported_scalar (i : Fin 289) (held : sourceHeldUnsupported i) (j : Fin 9) :
    scalarSlot j≠i := by
  intro same
  have h:=congrArg Fin.val same
  simp only [scalarSlot] at h
  unfold sourceHeldUnsupported at held
  have := j.isLt
  omega
private theorem unsupported_gauge (i : Fin 289) (held : sourceHeldUnsupported i) (mu : Fin 4) (a : Fin 12) :
    gaugeSlot mu a≠i := by
  intro same
  have h:=congrArg Fin.val same
  simp only [gaugeSlot] at h
  unfold sourceHeldUnsupported at held
  have := mu.isLt
  have := a.isLt
  omega
private theorem unsupported_coframe (i : Fin 289) (held : sourceHeldUnsupported i) (a mu : Fin 4) :
    coframeSlot a mu≠i := by
  intro same
  have h:=congrArg Fin.val same
  simp only [coframeSlot] at h
  unfold sourceHeldUnsupported at held
  have := a.isLt
  have := mu.isLt
  omega
private theorem unsupported_lorentz (i : Fin 289) (held : sourceHeldUnsupported i) (mu : Fin 4) (a : Fin 6) :
    lorentzSlot mu a≠i := by
  intro same
  have h:=congrArg Fin.val same
  simp only [lorentzSlot] at h
  unfold sourceHeldUnsupported at held
  have := mu.isLt
  have := a.isLt
  omega

theorem sourceHeld_fieldDirection_zero (i : Fin 289) (held : sourceHeldUnsupported i) :
    fieldDirection (fieldUnit i)=0 := by
  rw [←stateDirection_source]
  have scalar : fieldScalar (fieldUnit i)=0 := by
    simp only [fieldScalar,fieldUnit,Pi.single_apply,if_neg (unsupported_scalar i held _),zero_smul,Finset.sum_const_zero]
  have gauge : fieldGauge (fieldUnit i)=0 := by
    funext mu
    simp only [fieldGauge,fieldUnit,Pi.single_apply,if_neg (unsupported_gauge i held _ _),zero_smul,Finset.sum_const_zero,Pi.zero_apply]
  have coframe : fieldCoframe (fieldUnit i)=0 := by
    funext a mu
    simp only [fieldCoframe,fieldUnit,Pi.single_apply,if_neg (unsupported_coframe i held _ _),Matrix.zero_apply]
  have lorentz : fieldLorentz (fieldUnit i)=0 := by
    funext mu a
    simp only [fieldLorentz,fieldUnit,Pi.single_apply,if_neg (unsupported_lorentz i held _ _),Pi.zero_apply]
  have data : sourceData (fieldUnit i)=0 := by
    simp only [sourceData,scalar,gauge,coframe,lorentz]
    rfl
  rw [data,map_zero]

theorem sourceHeld_rawSymbol_zero (i : Fin 289) (held : sourceHeldUnsupported i)
    (p : PhysicalMomentum) (s : PreparationVacuumSourceFieldFamily.ActionState) :
    rawActionSymbol (fieldUnit i) p s=0 := by
  unfold rawActionSymbol
  have zero : (fun j=>densityActionMatrix*densityVariation (fieldUnit i) s j)=0 := by
    funext j
    unfold densityVariation lowerVariation principalVariation
    rw [sourceHeld_fieldDirection_zero i held]
    simp only [map_zero,smul_zero]
    cases j using Fin.cases <;> simp
  rw [zero,map_zero]

theorem sourceHeld_rawFiber_zero (i : Fin 289) (held : sourceHeldUnsupported i)
    (p : PhysicalMomentum) (u : JointParameter) :
    PreparationVacuumRawJointFeedback.rawFiber (fieldUnit i) p u=0 := by
  rw [PreparationVacuumRawJointFeedback.rawFiber,sourceHeld_rawSymbol_zero i held p _,map_zero]

theorem sourceHeld_rawForm_zero (i : Fin 289) (held : sourceHeldUnsupported i)
    (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) :
    rawForm (fieldUnit i) p a b h=0 := by
  unfold rawForm rawSample
  simp_rw [sourceHeld_rawFiber_zero i held p,zero_apply]
  have sample (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
      pairSample z (a z) 0=0 := by
    unfold pairSample
    simp only [WithLp.ofLp_zero,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  simp_rw [sample]
  exact integral_zero _ _

set_option backward.isDefEq.respectTransparency false in
theorem sourceHeld_rawReader_zero (i : Fin 289) (held : sourceHeldUnsupported i)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    rawReader (fieldUnit i) p F h=0 := by
  unfold rawReader finiteRiesz
  simp_rw [sourceHeld_rawForm_zero i held p]
  simp only [zero_smul,Finset.sum_const_zero]

theorem sourceHeld_actualEuler_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) (held : sourceHeldUnsupported i) :
    sourcePoleActionEuler q pL pR left right 0 t i=0 := by
  rw [sourcePoleActionEuler_source]
  unfold fiveKernel
  rw [sourceHeld_rawReader_zero i held]
  simp only [mul_zero,zero_mul,map_zero,neg_zero]

theorem sourceHeld_actualWindow_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (i : Fin 289) (held : sourceHeldUnsupported i) :
    sourcePoleCurrentWindow q pL pR left right lambda T i=0 := by
  unfold sourcePoleCurrentWindow
  simp_rw [sourceHeld_actualEuler_zero q pL pR left right _ i held,mul_zero]
  exact intervalIntegral.integral_zero

theorem sourceHeld_actualHalf_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (i : Fin 289) (held : sourceHeldUnsupported i) :
    sourcePoleCurrentHalf q pL pR left right lambda i=0 := by
  unfold sourcePoleCurrentHalf
  simp_rw [sourceHeld_actualEuler_zero q pL pR left right _ i held,mul_zero]
  exact integral_zero _ _

end LowEnergy.PreparationVacuumPhysicalConstraint114
