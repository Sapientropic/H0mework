import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceChargedFieldSlots
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceLockedStaticN1Read
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceObservedFieldVertex

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace LowEnergy.PreparationVacuumPhysicalChargedFieldFactor
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumPhysicalElectromagneticDirection
open PreparationVacuumPhysicalLockedGaussBalance PreparationVacuumPhysicalLockedN1Balance
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumObservedPoleTensor
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet
open PreparationVacuumElectromagneticIdentity PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumRawJointFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumNoetherChart
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumFullFieldRiesz
open PreparationVacuumSourceActionJets PreparationVacuumMixedFieldReturn
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussHistoryHilbert
open PreparationVacuumActionFieldLift PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalPoleAmputation
attribute [local irreducible] sourceModeGaussReader PreparationVacuumRawJointFeedback.rawReader
  sourceAmputatedFieldVertex sourceBareFieldVertex sourceFieldLegCorrection
  sourceAmputatedPoleVertex sourceBarePoleVertex sourcePoleEulerInitial sourcePoleMaterialPairGap
  noetherReader noetherTimeInsertion sourceHamiltonian sourceActualN1Primal
open scoped BigOperators Topology InnerProductSpace

private def fieldReaderLinear (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (Fin 289→ℂ)→L[ℂ](H→L[ℂ] H) :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (PreparationVacuumRawJointFeedback.rawReader (fieldUnit j) p F 0)

private theorem fieldReaderLinear_apply (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (V : Fin 289→ℂ) : fieldReaderLinear p F V=sourceModeGaussReader V p F := by
  simp only [fieldReaderLinear,sourceModeGaussReader,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

theorem sourceChargedGaussReader_generated (V : Fin 289→ℂ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceModeGaussReader V p F=
      (∑mu : Fin 4,sourceChargedCoefficient V mu •
        PreparationVacuumRawJointFeedback.rawReader (sourceLockedField mu 2) p F 0)+
      sourceModeGaussReader (sourceChargedFieldRemainder V) p F := by
  have split : V=sourceChargedFieldPart V+sourceChargedFieldRemainder V := by
    unfold sourceChargedFieldRemainder
    abel
  have h:=congrArg (fieldReaderLinear p F) split
  simp only [map_add,sourceChargedFieldPart,map_sum,map_smul,fieldReaderLinear_apply] at h
  unfold sourceChargedLockedField at h
  simp only [sourceModeGaussReader_real] at h
  exact h

/-- The remainder still contains the full CAR connection and every nonconnection density term. -/
theorem sourceChargedRemainder_fullDensity (V : Fin 289→ℂ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceModeGaussReader (sourceChargedFieldRemainder V) p F=
      ∑j : Fin 289,sourceChargedFieldRemainder V j • finiteRiesz F
        (fun a b=>∫z,pairSample z (frameTest F a z)
          ((GaussQuantumMultiplier.quantizer (sourceModeConnectionSymbol (fieldUnit j) p
            (sourceState z))+GaussQuantumMultiplier.quantizer (sourceModeRemainingSymbol
              (fieldUnit j) p (sourceState z))) (frameTest F b z))
                ∂GaussHistoryHilbert.configurationMeasure) :=
  sourceModeGaussReader_density _ p F

def sourceChargedFullInsertion (q : PhysicalResponsePoint) (V : Fin 289→ℂ) : H→L[ℂ] H :=
  sourceHamiltonian (q.p+q.k) q.F*sourceModeGaussReader V q.p q.F-
    sourceModeGaussReader V q.p q.F*sourceHamiltonian q.p q.F

/-- Both actual full generators act on the original Gauss reader, including the source remainder. -/
theorem sourceChargedInsertion_generated (q : PhysicalResponsePoint) (V : Fin 289→ℂ) :
    sourceChargedFullInsertion q V=
      (∑mu : Fin 4,sourceChargedCoefficient V mu • noetherTimeInsertion q (sourceLockedField mu 2))+
        sourceChargedFullInsertion q (sourceChargedFieldRemainder V) := by
  unfold sourceChargedFullInsertion noetherTimeInsertion
  rw [sourceChargedGaussReader_generated]
  simp only [noetherReader_source,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,smul_mul_assoc,mul_add,add_mul,smul_sub,Finset.sum_sub_distrib]
  abel

/-- The actual pole state consumes the source-generated N1 Ward return; every other Lorentz insertion remains explicit. -/
theorem sourceChargedActualN1_insertion (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (V : Fin 289→ℂ) (state : RestStateIndex) (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR) V
      (sourceActualN1Primal q pR state z t)=
      (∑mu : Fin 4,sourceChargedCoefficient V mu •
        (if mu=0 then sourceLockedN1WardReturn q pL pR (sourceActualN1Primal q pR state z t)
         else noetherTimeInsertion (sourcePhysicalMaterialPoint q pL pR) (sourceLockedField mu 2)
           (sourceActualN1Primal q pR state z t)))+
      sourceChargedFullInsertion (sourcePhysicalMaterialPoint q pL pR)
        (sourceChargedFieldRemainder V) (sourceActualN1Primal q pR state z t) := by
  rw [sourceChargedInsertion_generated]
  simp only [add_apply,sum_apply,smul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro mu _
  split_ifs with same
  · subst mu
    rw [sourceLockedActualN1_insertion q pL pR state z t nonreal]
  · rfl

def sourceChargedRemainderCurrentPrice (q : PhysicalResponsePoint) (V : Fin 289→ℂ)
    (pL pR : PhysicalMomentum) (t : ℝ) : ℝ :=
  ∑j : Fin 289,‖sourceChargedFieldRemainder V j‖*
    ‖fiveKernel (fieldUnit j) pR (pL-pR) q.F q.z q.w t 0‖

/-- This is a price for the non-EM response itself; it is independent of the external-leg correction price. -/
theorem sourceChargedRemainder_current_price (q : PhysicalResponsePoint) (V : Fin 289→ℂ)
    (pL pR : PhysicalMomentum) (l r : RestStateIndex) (t : ℝ) :
    ‖∑j : Fin 289,sourceChargedFieldRemainder V j*sourcePoleActionEuler q pL pR l r 0 t j‖≤
      sourceChargedRemainderCurrentPrice q V pL pR t := by
  rw [sourceModeGaussCurrent_generated,norm_neg]
  have read:=(sourcePoleRead q.epsilon q.precision pL pR l r).le_opNorm
    (sourceModeGaussKernel (sourceChargedFieldRemainder V) q pL pR t)
  have readPrice:=sourcePoleRead_price q.epsilon q.precision pL pR l r
  refine read.trans ?_
  calc
    _ ≤ 1*‖sourceModeGaussKernel (sourceChargedFieldRemainder V) q pL pR t‖ :=
      mul_le_mul_of_nonneg_right readPrice (norm_nonneg _)
    _ ≤ sourceChargedRemainderCurrentPrice q V pL pR t := by
      rw [one_mul,sourceModeGaussKernel_generated]
      exact (norm_sum_le _ _).trans (by simp only [norm_smul,sourceChargedRemainderCurrentPrice];rfl)

private def amputatedLinear (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) : (Fin 289→ℂ)→L[ℂ] ℂ :=
  ∑j : Fin 289,(ContinuousLinearMap.proj j : (Fin 289→ℂ)→L[ℂ] ℂ).smulRight
    (PreparationVacuumPhysicalPoleAmputation.sourceAmputatedPoleVertex q pL pR l r (fieldUnit j))

private theorem amputatedLinear_apply (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (V : Fin 289→ℂ) :
    amputatedLinear q pL pR l r V=sourceAmputatedFieldVertex q pL pR l r V := by
  simp only [amputatedLinear,sourceAmputatedFieldVertex,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]

theorem sourceChargedAmputatedField_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (V : Fin 289→ℂ) :
    sourceAmputatedFieldVertex q pL pR l r V=
      (∑mu : Fin 4,sourceChargedCoefficient V mu*
        sourceAmputatedFieldVertex q pL pR l r (sourceChargedLockedField mu))+
      sourceBareFieldVertex q pL pR l r (sourceChargedFieldRemainder V)+
      sourceFieldLegCorrection q pL pR l r (sourceChargedFieldRemainder V) := by
  have split : V=sourceChargedFieldPart V+sourceChargedFieldRemainder V := by
    unfold sourceChargedFieldRemainder
    abel
  have h:=congrArg (amputatedLinear q pL pR l r) split
  simp only [map_add,sourceChargedFieldPart,map_sum,map_smul,amputatedLinear_apply,smul_eq_mul] at h
  rw [sourceAmputatedFieldVertex_generated q pL pR l r (sourceChargedFieldRemainder V)] at h
  exact h.trans (add_assoc _ _ _).symm

def sourceChargedRemainderAmplitudePrice (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (V : Fin 289→ℂ) : ℝ :=
  ‖sourcePoleMaterialPairGap q pL pR l r‖*
    ∑j : Fin 289,‖sourceChargedFieldRemainder V j‖*‖sourcePoleEulerInitial q pL pR l r j‖

/-- The actual independent amputated legs price the entire remainder amplitude, with no caller budget. -/
theorem sourceChargedRemainder_amplitude_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (V : Fin 289→ℂ) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖sourceAmputatedFieldVertex q pL pR l r (sourceChargedFieldRemainder V)‖≤
      sourceChargedRemainderAmplitudePrice q pL pR l r V := by
  rw [sourceAmputatedFieldVertex_initial q pL pR l r nonrealL nonrealR,norm_mul,norm_neg]
  unfold sourceChargedRemainderAmplitudePrice
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_sum_le _ _).trans (by simp only [norm_mul];rfl)

theorem sourceChargedRemainder_externalLeg_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (l r : RestStateIndex) (V : Fin 289→ℂ) :
    ‖sourceAmputatedFieldVertex q pL pR l r (sourceChargedFieldRemainder V)-
      sourceBareFieldVertex q pL pR l r (sourceChargedFieldRemainder V)‖≤
      ∑j : Fin 289,‖sourceChargedFieldRemainder V j‖*
        PreparationVacuumPhysicalPoleAmputation.sourcePoleVertexLegPrice q pL pR l r (fieldUnit j) :=
  sourceObservedField_legs_price q pL pR l r _

end LowEnergy.PreparationVacuumPhysicalChargedFieldFactor
