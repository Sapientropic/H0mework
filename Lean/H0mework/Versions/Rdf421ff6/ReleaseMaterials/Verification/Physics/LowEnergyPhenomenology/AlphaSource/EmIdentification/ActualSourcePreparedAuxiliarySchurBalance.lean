import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliarySchurActualReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliarySchurBalance
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMTensorClock ActualEMAction
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryClockSchur
open ActualSourcePreparedAuxiliarySchurActualReturn ActualSourcePreparedAuxiliaryActualReturn
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedQuantumColumnClock ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedEMNativeRead ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open scoped Matrix BigOperators
attribute [local irreducible] sourceAuxiliaryClockSchurPencil sourceAuxiliaryReducedPencil
  sourceAuxiliaryClockInverse sourceTemporalCorrectedField Matrix.det Matrix.adjugate Matrix.mulVec

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_left (i : Fin 217) : wholeIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_right (i : Fin 6 × Fin 12) : wholeIndex (Sum.inr i)=gaugeAuxiliaryIndex i := by
  apply Fin.ext
  change 217+(i.2.val+12*i.1.val)=217+12*i.1.val+i.2.val
  omega

def sourceSchurDeterminant (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) : ℂ :=
  ((sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)).det

def sourceSchurRestNumerator (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) : Fin 217 → ℂ :=
  sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n) •
    (((sourceAuxiliaryClockSchurPencil event n).map (sourceClockEval eps sigma)).adjugate*ᵥemRestSlice sourceTemporalEMForce)

/-- All 289 source field coordinates are restored from the same Schur217
cofactor. The auxiliary inverse supplies the original constitutive field. -/
def sourceSchurFullFieldNumerator (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) : Fin 289 → ℂ :=
  Sum.elim (sourceSchurRestNumerator event n eps sigma)
    (-((sourceAuxiliaryClockInverse.map (sourceClockEval eps sigma))*ᵥ
      (((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex).map
        (sourceClockEval eps sigma)*ᵥsourceSchurRestNumerator event n eps sigma))) ∘ wholeIndex.symm

attribute [local irreducible] sourceSchurDeterminant sourceSchurRestNumerator sourceSchurFullFieldNumerator

theorem source_schur_determinant_nonzero (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    sourceSchurDeterminant event n eps sigma≠0 := by
  unfold sourceSchurDeterminant
  exact source_auxiliary_actual_schur_regular event n eps sigma positive regular

/-- The restored numerator clears the original full GE0, not a new field. -/
theorem source_schur_full_field_clear (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) :
    sourceSchurDeterminant event n eps sigma • sourceTemporalCorrectedField event eps sigma n=
      sourceSchurFullFieldNumerator event n eps sigma := by
  have rest : sourceSchurDeterminant event n eps sigma • emRestSlice (sourceTemporalCorrectedField event eps sigma n)=
    sourceSchurRestNumerator event n eps sigma := by
    unfold sourceSchurDeterminant sourceSchurRestNumerator
    exact source_auxiliary_actual_schur_cofactor event n eps sigma positive regular
  have aux := congrArg (fun v : (Fin 6 × Fin 12) → ℂ => sourceSchurDeterminant event n eps sigma • v)
    (source_auxiliary_actual_field_reconstruction event n eps sigma positive regular)
  rw [smul_neg,←Matrix.mulVec_smul,←Matrix.mulVec_smul,rest] at aux
  funext i
  obtain ⟨r,rfl⟩ := wholeIndex.surjective i
  cases r with
  | inl r =>
      change sourceSchurDeterminant event n eps sigma*sourceTemporalCorrectedField event eps sigma n (wholeIndex (Sum.inl r))=_
      simp only [sourceSchurFullFieldNumerator,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
      rw [whole_left]
      simpa only [emRestSlice,Pi.smul_apply,smul_eq_mul] using congrFun rest r
  | inr r =>
      change sourceSchurDeterminant event n eps sigma*sourceTemporalCorrectedField event eps sigma n (wholeIndex (Sum.inr r))=_
      simp only [sourceSchurFullFieldNumerator,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
      rw [whole_right]
      simpa only [emAuxiliarySlice,Pi.smul_apply,smul_eq_mul] using congrFun aux r

theorem source_schur_full_field_fraction (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ)
    (positive : 0<sigma) (regular : correctedDet event eps 0 sigma n≠0) (i : Fin 289) :
    sourceTemporalCorrectedField event eps sigma n i=
      sourceSchurFullFieldNumerator event n eps sigma i/sourceSchurDeterminant event n eps sigma := by
  apply (eq_div_iff (source_schur_determinant_nonzero event n eps sigma positive regular)).mpr
  have entry := congrFun (source_schur_full_field_clear event n eps sigma positive regular) i
  change sourceSchurDeterminant event n eps sigma*sourceTemporalCorrectedField event eps sigma n i=_ at entry
  exact (mul_comm _ _).trans entry

def sourceSchurDriverNumerator (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) : Fin 289 → ℂ :=
  emOriginalJacobi (frequencyRay eps 0 n)*ᵥsourceSchurFullFieldNumerator event n eps sigma-
    sourceSchurDeterminant event n eps sigma • sourceTemporalEMForce

/-- Complete original quantum/contact drive consumes the reconstructed field. -/
theorem source_schur_actual_driver_clear (event : DressedEvent) (n : PhysicalMomentum) (e : scaleDomain)
    (sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceSchurDeterminant event n e.val sigma • sourceTemporalActualQuantumDriver event e sigma n=
      sourceSchurDriverNumerator event n e.val sigma := by
  have driver := source_quantum_driver_em_column event e sigma n positive regular
  rw [←source_quantum_field_em_column event e.val sigma n positive regular] at driver
  rw [driver]
  unfold sourceSchurDriverNumerator
  rw [smul_sub,←Matrix.mulVec_smul,source_schur_full_field_clear event n e.val sigma positive regular]

/-- Shared full EM balance, now with Schur217 determinant. Every original
field, driver, background and lower term retains the same denominator. -/
def sourceSchurEMBalance (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) : ℂ :=
  (dotProduct sourceTemporalEMForce (sourceSchurDriverNumerator event n eps sigma)-
    sourceEMNativeBackgroundRead (sourceSchurFullFieldNumerator event n eps sigma)-
    (eps : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n)
      (sourceSchurFullFieldNumerator event n eps sigma))/sourceSchurDeterminant event n eps sigma

private theorem scalar_balance (d a b c x A B C : ℂ) (nonzero : d≠0)
    (drive : d*a=A) (background : d*b=B) (lower : d*c=C) : (A-B-x*C)/d=a-b-x*c := by
  apply (div_eq_iff nonzero).mpr
  rw [←drive,←background,←lower]
  ring

theorem source_schur_em_balance_actual (event : DressedEvent) (n : PhysicalMomentum) (e : scaleDomain)
    (sigma : ℝ) (positive : 0<sigma) (regular : correctedDet event e.val 0 sigma n≠0) :
    sourceSchurEMBalance event n e.val sigma=
      dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)-
      sourceEMNativeBackgroundRead (sourceTemporalCorrectedField event e.val sigma n)-
      (e.val : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n) (sourceTemporalCorrectedField event e.val sigma n) := by
  have field := source_schur_full_field_clear event n e.val sigma positive regular
  have drive := congrArg (dotProduct sourceTemporalEMForce) (source_schur_actual_driver_clear event n e sigma positive regular)
  simp only [dotProduct_smul,smul_eq_mul] at drive
  have background := congrArg sourceEMNativeBackgroundRead field
  simp only [sourceEMNativeBackgroundRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at background
  have lower := congrArg (sourceEMNativeLowerRead (frequencyRay 1 0 n)) field
  simp only [sourceEMNativeLowerRead,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul] at lower
  unfold sourceSchurEMBalance
  exact scalar_balance _ _ _ _ _ _ _ _ (source_schur_determinant_nonzero event n e.val sigma positive regular)
    drive background lower

/-- The same action/current coefficient consumes the complete Schur balance. -/
theorem source_em_schur_finite_return (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n=
      noetherPairScale^2/(2*(lapse : ℂ))*((3/4 : ℂ)+sourceSchurEMBalance event n e.val sigma) := by
  rw [source_em_native_scaled_finite_return event e sigma n unit positive regular,
    source_schur_em_balance_actual event n e sigma positive regular]
  congr 1
  ring

end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliarySchurBalance
