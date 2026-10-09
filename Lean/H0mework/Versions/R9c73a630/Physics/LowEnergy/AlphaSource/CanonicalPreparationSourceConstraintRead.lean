import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceCurrentSupport

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
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

open PreparationVacuumOriginalGreenFeedback

def constraint114Terms : List SourceTerm := [
  ⟨114,15,⟨1,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,16,⟨1,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,27,⟨0,1,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,28,⟨0,1,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,39,⟨0,0,1,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,40,⟨0,0,1,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,51,⟨0,0,0,1⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,52,⟨0,0,0,1⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,21,⟨0,0,0,0⟩,⟨⟨0,-3/10⟩,⟨0,0⟩⟩⟩,
  ⟨114,34,⟨0,0,0,0⟩,⟨⟨0,3/10⟩,⟨0,0⟩⟩⟩,
  ⟨114,86,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,88,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,92,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,94,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
  ⟨114,110,⟨0,0,0,0⟩,⟨⟨0,1/2⟩,⟨0,0⟩⟩⟩,
  ⟨114,112,⟨0,0,0,0⟩,⟨⟨0,1/2⟩,⟨0,0⟩⟩⟩,
  ⟨114,116,⟨0,0,0,0⟩,⟨⟨0,1/2⟩,⟨0,0⟩⟩⟩,
  ⟨114,118,⟨0,0,0,0⟩,⟨⟨0,1/2⟩,⟨0,0⟩⟩⟩,
  ⟨114,217,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1/5⟩⟩⟩,
  ⟨114,230,⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,1/5⟩⟩⟩]

private theorem constraint114_certificate :
    fastNormalizeTerms (rowTerms 114 (reflectedTerms originalChangeTerms)++negativeTerms constraint114Terms)=[] := by
  decide +kernel

theorem constraint114_row_generated (p : Fin 4→ℂ) (v : Fin 289→ℂ) :
    (originalReadback p*ᵥv) 114=(sourceMatrix constraint114Terms p*ᵥv) 114 := by
  have h := normalization_equal _ _ constraint114_certificate p
  have entries (i : Fin 289) : originalReadback p 114 i=sourceMatrix constraint114Terms p 114 i := by
    have e:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A 114 i) h
    rw [rowTerms_entry,reflectedTerms_value] at e
    exact e
  simp only [Matrix.mulVec,dotProduct,entries]

def constraintChargeRead (v : Fin 289→ℂ) : ℂ := (v 15-v 16)/2

def constraintCovariantRead (spatial : Fin 3→ℂ) (v : Fin 289→ℂ) : ℂ :=
  (spatial 0*(v 27-v 28)+spatial 1*(v 39-v 40)+spatial 2*(v 51-v 52))/2+
    (3/10 : ℂ)*rootTwo*(v 34-v 21)

def constraintUnsupportedRead (v : Fin 289→ℂ) : ℂ :=
  -(v 86+v 88+v 92+v 94)/2+rootTwo*(v 110+v 112+v 116+v 118)/2+
    (rootTwo*rootFifteen/5)*(v 230-v 217)

theorem constraint114_source_linear (spatial : Fin 3→ℂ) (lambda : ℂ) (v : Fin 289→ℂ) :
    (originalReadback (fullMomentum spatial lambda)*ᵥv) 114=
      lambda*constraintChargeRead v+constraintCovariantRead spatial v+constraintUnsupportedRead v := by
  rw [constraint114_row_generated,sourceMatrix_mulVec]
  norm_num only [constraint114Terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,coefficientValue,
    Powers.value,pow_zero,pow_one,fullMomentum,Fin.cases_zero,Fin.cases_succ,ite_true,mul_one]
  rw [show Fin.cases lambda spatial (1 : Fin 4)=spatial 0 from rfl,
    show Fin.cases lambda spatial (2 : Fin 4)=spatial 1 from rfl,
    show Fin.cases lambda spatial (3 : Fin 4)=spatial 2 from rfl]
  unfold constraintChargeRead constraintCovariantRead constraintUnsupportedRead
  ring

theorem constraintUnsupported_actualWindow_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    constraintUnsupportedRead (sourcePoleCurrentWindow q pL pR left right lambda T)=0 := by
  unfold constraintUnsupportedRead
  simp only [sourceHeld_actualWindow_zero q pL pR left right lambda T 86 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 88 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 92 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 94 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 110 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 112 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 116 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 118 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 217 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualWindow_zero q pL pR left right lambda T 230 (by norm_num [sourceHeldUnsupported]),
    add_zero,mul_zero,sub_zero,zero_div,neg_zero]

theorem constraintUnsupported_actualHalf_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) :
    constraintUnsupportedRead (sourcePoleCurrentHalf q pL pR left right lambda)=0 := by
  unfold constraintUnsupportedRead
  simp only [sourceHeld_actualHalf_zero q pL pR left right lambda 86 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 88 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 92 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 94 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 110 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 112 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 116 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 118 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 217 (by norm_num [sourceHeldUnsupported]),
    sourceHeld_actualHalf_zero q pL pR left right lambda 230 (by norm_num [sourceHeldUnsupported]),
    add_zero,mul_zero,sub_zero,zero_div,neg_zero]

theorem sourceActualCosource114_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      lambda*constraintChargeRead (sourcePoleCurrentWindow q pL pR left right lambda T)+
        constraintCovariantRead spatial (sourcePoleCurrentWindow q pL pR left right lambda T) := by
  have h:=congrArg (fun v : Fin 289→ℂ=>v 114) (sourceActualCurrentWindow_ward q pL pR left right spatial lambda T)
  rw [constraint114_source_linear,constraintUnsupported_actualWindow_zero,add_zero] at h
  exact h.symm

end LowEnergy.PreparationVacuumPhysicalConstraint114
