import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCanonicalMoyal

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCanonicalMoyal
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert
open PreparationVacuumEnergyTail PreparationVacuumLowerLeaves PreparationVacuumWeylOrdering
open PreparationActualFactor GaussDensityCore CanonicalPreparationCore
open CanonicalPreparationSquareCutoff PreparationScalarCoordinates GaussNativeEnergy
open PreparationVacuumLowerTensor
open PreparationVacuumFactor
open scoped BigOperators

def originalPrincipal14 (zp : Phase) : Fin 14 → ℝ :=
  Fin.snoc (fun j : Fin 13 => originalPrincipalLeaves (nativePhase zp).1 (nativePhase zp).2 j) 0

def originalLeaf (degree : Fin 3) (slot : Fin 14) : Symbol := fun zp =>
  match degree.val with
  | 0 => originalZeroLeaves (nativePhase zp).1 slot
  | 1 => originalFirstLeaves (nativePhase zp).1 (nativePhase zp).2 slot
  | _ => originalPrincipal14 zp slot

def originalN0Coefficient (r : ℕ) (d e : Fin 3) (j k : Fin 14) : Phase → ℂ :=
  coefficient r (originalLeaf d j) (originalLeaf e k)

theorem originalLeaf_zero (j : Fin 14) (zp : Phase) :
    originalLeaf 0 j zp=originalZeroLeaves (nativePhase zp).1 j := rfl

theorem originalLeaf_first (j : Fin 14) (zp : Phase) :
    originalLeaf 1 j zp=originalFirstLeaves (nativePhase zp).1 (nativePhase zp).2 j := rfl

theorem originalLeaf_principal (j : Fin 13) (zp : Phase) :
    originalLeaf 2 (Fin.castSucc j) zp=
      originalPrincipalLeaves (nativePhase zp).1 (nativePhase zp).2 j := by
  simp only [originalLeaf,originalPrincipal14,Fin.snoc_castSucc]

theorem originalLeaf_Y_zero (degree : Fin 3) : originalLeaf degree (Fin.last 13)=fun _ => 0 := by
  funext zp
  fin_cases degree
  · exact originalZeroLeaves_Y_vacuum _
  · simp [originalLeaf,originalFirstLeaves]
  · change originalPrincipal14 zp (Fin.last 13)=0
    unfold originalPrincipal14
    exact Fin.snoc_last _ _

theorem originalN0Coefficient_Y_left (r : ℕ) (d e : Fin 3) (k : Fin 14) (zp : Phase) :
    originalN0Coefficient r d e (Fin.last 13) k zp=0 := by
  unfold originalN0Coefficient
  rw [originalLeaf_Y_zero,coefficient_zero_left]

theorem originalN0Coefficient_Y_right (r : ℕ) (d e : Fin 3) (j : Fin 14) (zp : Phase) :
    originalN0Coefficient r d e j (Fin.last 13) zp=0 := by
  unfold originalN0Coefficient
  rw [originalLeaf_Y_zero,coefficient_zero_right]

theorem originalN0Coefficient_zero (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    originalN0Coefficient 0 d e j k zp=
      (originalLeaf d j zp : ℂ)*(originalLeaf e k zp : ℂ) :=
  coefficient_zero _ _ _

theorem originalN0Coefficient_one (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    originalN0Coefficient 1 d e j k zp=Complex.I/2*
      ((∑ i : Fin 100,(qD i (originalLeaf d j) zp*pD i (originalLeaf e k) zp-
        pD i (originalLeaf d j) zp*qD i (originalLeaf e k) zp) : ℝ) : ℂ) :=
  coefficient_one _ _ _

theorem originalN0Coefficient_two (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    originalN0Coefficient 2 d e j k zp=(-1/8 : ℂ)*
      ((∑ i : Fin 100,∑ a : Fin 100,
      (hessian (originalLeaf d j) zp (qDirection i) (qDirection a)*
        hessian (originalLeaf e k) zp (pDirection i) (pDirection a)-
      hessian (originalLeaf d j) zp (qDirection i) (pDirection a)*
        hessian (originalLeaf e k) zp (pDirection i) (qDirection a)-
      hessian (originalLeaf d j) zp (pDirection i) (qDirection a)*
        hessian (originalLeaf e k) zp (qDirection i) (pDirection a)+
      hessian (originalLeaf d j) zp (pDirection i) (pDirection a)*
        hessian (originalLeaf e k) zp (qDirection i) (qDirection a)) : ℝ) : ℂ) := by
  unfold originalN0Coefficient
  rw [coefficient_two,contraction_two]

theorem originalN0Coefficient_adjoint (r : ℕ) (d e : Fin 3) (j k : Fin 14) (zp : Phase) :
    star (originalN0Coefficient r d e j k zp)=originalN0Coefficient r e d k j zp :=
  coefficient_adjoint_swap _ _ _ _

theorem originalPrincipalTime_replay (n : ℝ) (b : Fin 3 → ℝ) (zp : Phase)
    (timeNonzero : n≠0) (timelike : n^2-∑ i : Fin 3,b i^2≠0) :
    (∑ j : Fin 13,originalTemporalWeights n b j*originalLeaf 2 (Fin.castSucc j) zp)=
      timelikePrincipal (nativePhase zp).1 (nativePhase zp).2 n b := by
  simp only [originalLeaf_principal]
  exact originalPrincipalTemporalReplay_native _ _ _ _ timeNonzero timelike

theorem originalFirstTime_replay (n : ℝ) (b : Fin 3 → ℝ) (zp : Phase) :
    (∑ j : Fin 13,originalTemporalWeights n b j*originalLeaf 1 (Fin.castSucc j) zp)=
      nativeFirstTime n b (nativePhase zp).1 (nativePhase zp).2 :=
  originalFirstTemporalReplay _ _ _ _

theorem originalZeroTime_replay (z : physicalChart) (p : PhysicalMomentum) :
    (∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
      (originalLeaf 0 (Fin.castSucc j) (fullCoordinates z.val,p) : ℂ))=
      sourceWeylZero z.val := by
  rw [sourceWeylZero_originalLeaves]
  simp only [originalLeaf_zero,nativePhase,ContinuousLinearEquiv.symm_apply_apply]

theorem originalZeroLeaf_action (f : ScalarTest) (z : physicalChart) (p : PhysicalMomentum) :
    sourceHalf z.val*scalarVacuumAction (inverseHalfCore f) z.val=
      sourceFourTermWeyl f z.val+
        (∑ j : Fin 13,(originalTemporalWeights (sourceTime 0) 0 j : ℂ)*
          (originalLeaf 0 (Fin.castSucc j) (fullCoordinates z.val,p) : ℂ))*f z.val := by
  rw [originalZeroTime_replay]
  exact originalHalfVacuum_fourTermWeyl f z

end LowEnergy.PreparationVacuumCanonicalMoyal
