import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNumberHistory
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActualCurrentWard

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalNumberOneRead
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


private theorem read_right_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (K : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H)
    (zero : K*sourceProjection=0) : sourcePoleRead q.epsilon q.precision pL pR left right K=0 := by
  rw [sourcePoleRead_actual]
  have h := congrArg (fun A : GaussCoreHilbert.H→L[ℂ] GaussCoreHilbert.H=>
    A (sourcePolePrepared q.epsilon q.precision pR right)) zero
  simp only [mul_apply_eq_comp,zero_apply,
    sourcePolePrepared_sourceProjection q.epsilon q.precision pR right] at h
  rw [h,inner_zero_right]

private theorem word_right_zero {R : Type*} [MonoidWithZero R] (a b c d e p : R) (zero : e*p=0) :
    (a*b*c*d*e)*p=0 := by
  simp only [mul_assoc,zero,mul_zero]

theorem sourcePrincipalBlock_right_high_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (reader : Field289) (j k : Fin 57) (t : ℝ) (high : 1<k.val) :
    sourcePoleRead q.epsilon q.precision pL pR left right (sourcePrincipalBlock q pL pR reader j k t)=0 := by
  apply read_right_zero
  unfold sourcePrincipalBlock
  exact word_right_zero _ _ _ _ _ _ (actualPrefix_N1G0_high_zero pR q.F k.val t high)

set_option backward.isDefEq.respectTransparency false in
theorem sourcePrincipalWholeEuler_high_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (n : Fin 113) (t : ℝ) (i : Fin 289) (high : 1<n.val) :
    sourcePrincipalEulerSector q pL pR left right n t i=0 := by
  unfold sourcePrincipalEulerSector sourcePrincipalSector
  rw [map_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro j _
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  by_cases same : j.val+k.val=n.val
  · rw [if_pos same]
    by_cases leftPositive : 0<j.val
    · exact sourcePrincipalBlock_left_positive_zero q pL pR left right _ j k t leftPositive
    · exact sourcePrincipalBlock_right_high_zero q pL pR left right _ j k t (by omega)
  · rw [if_neg same,map_zero]

private theorem sum_two {E : Type*} [AddCommMonoid E] (f : Fin 113→E) (highZero : ∀n,1<n.val→f n=0) :
    ∑ n,f n=f 0+f 1 := by
  classical
  have h : ∑ n∈({0,1}:Finset (Fin 113)),f n=∑ n,f n := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro n _ outside
    apply highZero
    have hn0 : n≠0:=by intro h;apply outside;rw [h];simp
    have hn1 : n≠1:=by intro h;apply outside;rw [h];simp
    have v0 : n.val≠0:=fun h=>hn0 (Fin.ext h)
    have v1 : n.val≠1:=fun h=>hn1 (Fin.ext h)
    omega
  rw [←h]
  simp

theorem sourceActualEuler_twoSectors (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) (i : Fin 289) :
    sourcePoleActionEuler q pL pR left right 0 t i=
      sourcePrincipalEulerSector q pL pR left right 0 t i+
        sourcePrincipalEulerSector q pL pR left right 1 t i := by
  rw [sourcePrincipalEuler_generated]
  exact sum_two _ (fun n h=>sourcePrincipalWholeEuler_high_zero q pL pR left right n t i h)

theorem sourcePrincipalWholeHalf_high_zero (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (n : Fin 113) (i : Fin 289) (high : 1<n.val) :
    sourcePrincipalHalf q pL pR left right lambda n i=0 := by
  unfold sourcePrincipalHalf
  simp_rw [sourcePrincipalWholeEuler_high_zero q pL pR left right n _ i high,mul_zero]
  exact integral_zero _ _

theorem sourceActualHalf_twoSectors (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0<lambda.re) :
    sourcePoleCurrentHalf q pL pR left right lambda=
      sourcePrincipalHalf q pL pR left right lambda 0+sourcePrincipalHalf q pL pR left right lambda 1 := by
  funext i
  rw [sourcePrincipalHalf_generated q pL pR left right lambda off]
  exact sum_two _ (fun n h=>sourcePrincipalWholeHalf_high_zero q pL pR left right lambda n i h)

def sourcePrincipalWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (n : Fin 113) : SignalAmplitude :=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePrincipalEulerSector q pL pR left right n t i

theorem sourceActualWindow_twoSectors (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    sourcePoleCurrentWindow q pL pR left right lambda T=
      sourcePrincipalWindow q pL pR left right lambda T 0+sourcePrincipalWindow q pL pR left right lambda T 1 := by
  funext i
  unfold sourcePoleCurrentWindow sourcePrincipalWindow
  simp_rw [sourceActualEuler_twoSectors,mul_add]
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  exact intervalIntegral.integral_add
    ((weight.mul (sourcePrincipalEuler_continuous q pL pR left right 0 i)).intervalIntegrable 0 T)
    ((weight.mul (sourcePrincipalEuler_continuous q pL pR left right 1 i)).intervalIntegrable 0 T)

theorem sourceActualWindow_twoSectors_ward (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    originalReadback (fullMomentum spatial lambda)*ᵥ
      (sourcePrincipalWindow q pL pR left right lambda T 0+sourcePrincipalWindow q pL pR left right lambda T 1)=
      sourceActualCurrentCosource q pL pR left right spatial lambda T := by
  rw [←sourceActualWindow_twoSectors]
  exact sourceActualCurrentWindow_ward q pL pR left right spatial lambda T

end LowEnergy.PreparationVacuumPhysicalNumberOneRead
