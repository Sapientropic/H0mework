import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationEnergySeeds

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEnergyTail
open PreparationActualFactor PreparationVacuumWeyl PreparationPhaseSource
open PreparationScalarCoordinates CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates GaussNativeEnergy GaussHistoryHilbert
open scoped BigOperators

def originalPrincipalLeaves (z : SourceCoordinateSlice) (p : Cotangent) : Fin 13 → ℝ :=
  ![A z p,0,0,0,S z p 0 0,S z p 1 1,S z p 2 2,
    S z p 0 1,S z p 0 2,S z p 1 2,0,0,0]

def originalTemporalWeights (n : ℝ) (b : Fin 3 → ℝ) : Fin 13 → ℝ :=
  let delta:=n^2-∑ i : Fin 3,b i^2
  ![n,b 0,b 1,b 2,
    (n^2-b 0^2)/(2*n*delta),(n^2-b 1^2)/(2*n*delta),(n^2-b 2^2)/(2*n*delta),
    -b 0*b 1/(n*delta),-b 0*b 2/(n*delta),-b 1*b 2/(n*delta),
    -b 0/delta,-b 1/delta,-b 2/delta]

def originalPrincipalTemporalReplay (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) : ℝ :=
  ∑ j : Fin 13, originalTemporalWeights n b j*originalPrincipalLeaves z p j

theorem originalPrincipalTemporalReplay_native (n : ℝ) (b : Fin 3 → ℝ)
    (z : SourceCoordinateSlice) (p : Cotangent) (timeNonzero : n≠0)
    (timelike : n^2-∑ i : Fin 3,b i^2≠0) :
    originalPrincipalTemporalReplay n b z p=timelikePrincipal z p n b := by
  unfold originalPrincipalTemporalReplay originalTemporalWeights originalPrincipalLeaves timelikePrincipal
  norm_num [Fin.sum_univ_succ]
  rw [S_symmetric z p 1 0,S_symmetric z p 2 0,S_symmetric z p 2 1]
  have delta : n^2-(b 0^2+b 1^2+b 2^2)≠0 := by
    simpa only [Fin.sum_univ_three] using timelike
  have trace : T z p=S z p 0 0+S z p 1 1+S z p 2 2 := by
    rw [T,Fin.sum_univ_three]
  rw [trace]
  field_simp [timeNonzero,delta]
  ring

-- These are exactly Engine.source's degree2 slots, before any lower leaf is
-- evaluated. The common native C,T,S fields determine every principal slot.
def originalEnginePrincipalLeaves (z : SourceCoordinateSlice) (p : Cotangent) : Fin 13 → ℝ :=
  ![T z p/(2*C z p^2),0,0,0,S z p 0 0,S z p 1 1,T z p-S z p 0 0-S z p 1 1,
    S z p 0 1,S z p 0 2,S z p 1 2,0,0,0]

theorem originalEnginePrincipalLeaves_native (zp : Phase)
    (position : zp.1∈thetaPositionClosed)
    (direction : normalizedMomentum zp.2∈thetaDirectionClosed) (nonzero : zp.2≠0) :
    originalEnginePrincipalLeaves (nativePhase zp).1 (nativePhase zp).2=
      originalPrincipalLeaves (nativePhase zp).1 (nativePhase zp).2 := by
  have cone:=source_support_positiveCone zp.1 zp.2 position direction nonzero
  have cpos:=C_positive cone
  have relation:=C_equation cone
  have scalar : T (nativePhase zp).1 (nativePhase zp).2/
      (2*C (nativePhase zp).1 (nativePhase zp).2^2)=
      A (nativePhase zp).1 (nativePhase zp).2 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ)≠0)
      (pow_ne_zero 2 cpos.ne'))).mpr
    nlinarith [relation]
  have last : T (nativePhase zp).1 (nativePhase zp).2-
      S (nativePhase zp).1 (nativePhase zp).2 0 0-
      S (nativePhase zp).1 (nativePhase zp).2 1 1=
      S (nativePhase zp).1 (nativePhase zp).2 2 2 := by
    rw [T,Fin.sum_univ_three]
    ring
  ext j
  fin_cases j <;> simp [originalEnginePrincipalLeaves,originalPrincipalLeaves,scalar,last]

end LowEnergy.PreparationVacuumEnergyTail
