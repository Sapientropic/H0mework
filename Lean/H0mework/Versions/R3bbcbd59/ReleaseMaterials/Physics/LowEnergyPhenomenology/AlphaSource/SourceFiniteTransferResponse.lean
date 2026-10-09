import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteTransferL2
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFinitePoleScattering

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteTransferWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalNativeSoftWardBoundary
open PreparationPhysicalFiniteOriginCovariance PreparationPhysicalFinitePoleVertices
open PreparationPhysicalChargedSoftObservable PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalNativePolarizationEmitter
open PreparationPhysicalJointGeneratorEnergyReturn PreparationVacuumSoftPoleSelection
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular CanonicalGradedSpatialSource
open GaussComposite.PhysicalFullFieldScattering MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators Matrix
attribute [local irreducible] sourceNativeOriginCanonicalFiber sourceWardGenerator sourceWardInsertion
  sourceTransferHamiltonian sourceFiniteOriginPhotonReader sourceFiniteOriginAmplitude sourcePhotonEmitter
  sourceChargedFilteredPacket sourceActualScatteringRead

private def onlyTime (A : FiberOperators) : Fin 4→FiberOperators := fun k=>if k=0 then A else 0

private theorem fiber_zero (c : ℂ) : c • (0:FiberOperators)=0 := @_root_.smul_zero ℂ FiberOperators _ _ c
private theorem fiber_neg (c : ℂ) (A : FiberOperators) : (-c) • A= -(c • A) := _root_.neg_smul c A
private theorem zero_compLpL : (0:FiberOperators).compLpL 2 volume=(0:FullMatterL2→L[ℂ]FullMatterL2) := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [norm_zero] using ((0:FiberOperators).norm_compLpL_le (p:=2) (μ:=volume))) (norm_nonneg _)
private theorem onlyTime_shift (A : FiberOperators) (q : PhysicalMomentum) : shiftCoefficients (onlyTime A) q=onlyTime A := by
  funext k
  cases k using Fin.cases <;> simp [shiftCoefficients,onlyTime,fiber_zero]

/-- The same source amplitude combines the current emitter with its generated finite-origin coordinate. -/
def sourceTransferAmplitude (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : ℂ :=
  sourcePhotonEmitter leg branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n

/-- Both complete flows carry their actual momentum, including the finite transfer between insertions. -/
def sourceTransferWord (A B : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  shiftFlow 0 (-time)*A.compLpL 2 volume*shiftFlow q (time-age)*B.compLpL 2 volume*shiftFlow 0 age

private theorem word_smul_left (c : ℂ) (A B : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord (c • A) B q time age=c • sourceTransferWord A B q time age := by
  simp only [sourceTransferWord,ContinuousLinearMap.smul_compLpL,mul_smul_comm,smul_mul_assoc]
private theorem word_smul_right (c : ℂ) (A B : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord A (c • B) q time age=c • sourceTransferWord A B q time age := by
  simp only [sourceTransferWord,ContinuousLinearMap.smul_compLpL,mul_smul_comm,smul_mul_assoc]
private theorem word_add_left (A C B : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord (A+C) B q time age=sourceTransferWord A B q time age+sourceTransferWord C B q time age := by
  simp only [sourceTransferWord,ContinuousLinearMap.add_compLpL,mul_add,add_mul]
private theorem word_add_right (A B C : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord A (B+C) q time age=sourceTransferWord A B q time age+sourceTransferWord A C q time age := by
  simp only [sourceTransferWord,ContinuousLinearMap.add_compLpL,mul_add,add_mul]

private theorem word_time (A B : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    orderedWord (onlyTime A) (onlyTime B) q time age=
      (coordinateLeg 0).adjoint*sourceTransferWord A B q time age*coordinateLeg 0 := by
  unfold orderedWord
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp only [orderedLeft,orderedRight,onlyTime_shift,onlyTime,ite_true,sourceTransferWord,
        sourceTransferShiftFlow_zeroShift,mul_assoc]
    · intro j _ different
      simp only [orderedRight,onlyTime,if_neg different,zero_compLpL,zero_mul,mul_zero]
    · simp
  · intro i _ different
    simp only [orderedLeft,onlyTime_shift,onlyTime,if_neg different,zero_compLpL,mul_zero,zero_mul,Finset.sum_const_zero]
  · simp

/-- This is the original Q/negative-Q-adjoint origin sector, with the actual nonzero momentum transfer. -/
def sourceTransferOriginOperator (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  Complex.I •
    (sourceTransferWord (((-sourceTransferAmplitude Bn branch epsilon s n) • sourceNativeOriginCanonicalFiber 0).adjoint)
      (sourceFiniteOriginPhotonReader Ap An branch epsilon s n) (-(epsilon^2 • n)) age time-
    sourceTransferWord (sourceFiniteOriginPhotonReader Ap An branch epsilon s n)
      ((-sourceTransferAmplitude Bp branch epsilon s n) • sourceNativeOriginCanonicalFiber 0) (epsilon^2 • n) time age)

def sourceTransferOriginKernel (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceTransferOriginOperator Ap An Bp Bn branch epsilon s n time age)

/-- The current correction has two source-generated terms: the original negative-frequency full-Y defect and the finite momentum current. -/
def sourceTransferDefect (dual : Bool) (q : PhysicalMomentum) : FiberOperators :=
  (if dual then sourceWardDualDefect else 0)-sourceTransferHamiltonian q*sourceWardGenerator dual

private theorem physical_current (dual : Bool) (q : PhysicalMomentum) :
    (if dual then (sourceNativeOriginCanonicalFiber 0).adjoint else sourceNativeOriginCanonicalFiber 0)=
      sourceTransferInsertion dual q+sourceTransferDefect dual q := by
  cases dual <;> simp only [sourceTransferInsertion,sourceTransferDefect,sourceWardInsertion,Bool.false_eq_true,↓reduceIte,zero_sub]
  all_goals abel

private def leftContext (J : FiberOperators) (q : PhysicalMomentum) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  shiftFlow 0 (-time)*J.compLpL 2 volume*shiftFlow q time
private def rightContext (J : FiberOperators) (q : PhysicalMomentum) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  shiftFlow (-q) (-time)*J.compLpL 2 volume*shiftFlow 0 time

private theorem current_left (J : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord (sourceTransferInsertion true q) J (-q) age time=
      sourceTransferCurrent true 0 (-q) age*rightContext J q time := by
  simp only [sourceTransferWord,sourceTransferCurrent,rightContext,zero_sub,neg_neg]
  rw [sub_eq_add_neg,←sourceTransferShiftFlow_group]
  simp only [mul_assoc]
private theorem current_right (J : FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    sourceTransferWord J (sourceTransferInsertion false q) q time age=
      leftContext J q time*sourceTransferCurrent false q 0 age := by
  simp only [sourceTransferWord,sourceTransferCurrent,leftContext,sub_zero]
  rw [sub_eq_add_neg,←sourceTransferShiftFlow_group]
  simp only [mul_assoc]

/-- Actual initial/final preparation variations on both distinct source momentum legs. -/
def sourceTransferOriginBoundary (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ :=
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceFiniteOriginPhotonReader Ap An branch epsilon s n
  let q:=epsilon^2 • n;
  -star (sourceTransferAmplitude Bn branch epsilon s n)*inner ℂ u
    (sourceTransferSpatial true 0 (-q) age (rightContext J q time v)-
      sourceTransferSpatial true 0 (-q) 0 (rightContext J q time v))+
  sourceTransferAmplitude Bp branch epsilon s n*inner ℂ u
    (leftContext J q time (sourceTransferSpatial false q 0 age v-sourceTransferSpatial false q 0 0 v))

def sourceTransferOriginRate (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ :=
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceFiniteOriginPhotonReader Ap An branch epsilon s n
  let q:=epsilon^2 • n
  Complex.I*((-star (sourceTransferAmplitude Bn branch epsilon s n))*inner ℂ u
    (sourceTransferCurrent true 0 (-q) age (rightContext J q time v))+
  sourceTransferAmplitude Bp branch epsilon s n*inner ℂ u
    (leftContext J q time (sourceTransferCurrent false q 0 age v)))

def sourceTransferOriginCorrection (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (Complex.I •
      (sourceTransferWord ((-star (sourceTransferAmplitude Bn branch epsilon s n)) • sourceTransferDefect true (epsilon^2 • n))
        (sourceFiniteOriginPhotonReader Ap An branch epsilon s n) (-(epsilon^2 • n)) age time+
       sourceTransferWord (sourceFiniteOriginPhotonReader Ap An branch epsilon s n)
        (sourceTransferAmplitude Bp branch epsilon s n • sourceTransferDefect false (epsilon^2 • n)) (epsilon^2 • n) time age))

/-- The actual finite-transfer origin response is the boundary rate plus its explicit spatial-current and full-Y correction. -/
theorem sourceTransferOrigin_split (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    sourceTransferOriginKernel sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age=
      sourceTransferOriginRate sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age+
        sourceTransferOriginCorrection sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age := by
  have positive:=physical_current false (epsilon^2 • n)
  have negative:=physical_current true (epsilon^2 • n)
  simp only [Bool.false_eq_true,↓reduceIte] at positive negative
  simp only [sourceTransferOriginKernel,sourceTransferOriginOperator,map_smulₛₗ,starRingEnd_apply,star_neg]
  rw [negative,positive]
  simp only [word_smul_left,word_smul_right,word_add_left,word_add_right,sourceChargedQuantumRead_generated,
    smul_apply,add_apply,sub_apply,inner_smul_right,inner_add_right,inner_sub_right,current_left,current_right]
  simp only [sourceTransferOriginRate,sourceTransferOriginCorrection,sourceChargedQuantumRead_generated,
    word_smul_left,word_smul_right,smul_apply,add_apply,mul_apply_eq_comp,inner_smul_right,inner_add_right]
  ring

/-- No zero-transfer substitution occurs: the derivative uses the (q,0) and (0,−q) source flows. -/
theorem sourceTransferOrigin_derivative (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    HasDerivAt (sourceTransferOriginBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time)
      (sourceTransferOriginRate sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age) age := by
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceFiniteOriginPhotonReader Ap An branch epsilon s n
  let q:=epsilon^2 • n
  have negative:=((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceTransferSpatial_derivative true 0 (-q) (rightContext J q time v) age).sub_const
      (sourceTransferSpatial true 0 (-q) 0 (rightContext J q time v)))
  have positive:=(((innerSL ℂ u).comp (leftContext J q time)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceTransferSpatial_derivative false q 0 v age).sub_const (sourceTransferSpatial false q 0 0 v))
  have generated:=(negative.const_mul (-star (sourceTransferAmplitude Bn branch epsilon s n))).add
    (positive.const_mul (sourceTransferAmplitude Bp branch epsilon s n))
  convert! generated using 1
  change sourceTransferOriginRate sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age=
    (-star (sourceTransferAmplitude Bn branch epsilon s n))*inner ℂ u
      (Complex.I • sourceTransferCurrent true 0 (-q) age (rightContext J q time v))+
    sourceTransferAmplitude Bp branch epsilon s n*inner ℂ u
      (leftContext J q time (Complex.I • sourceTransferCurrent false q 0 age v))
  simp only [sourceTransferOriginRate,inner_smul_right,map_smul,u,v,J,q]
  ring

private theorem rate_continuous (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time : ℝ) :
    Continuous (sourceTransferOriginRate sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time) := by
  exact (((continuous_const.inner (sourceTransferCurrent_continuous true 0 (-(epsilon^2 • n)) _)).const_mul
    (-star (sourceTransferAmplitude Bn branch epsilon s n))).add
      ((continuous_const.inner ((leftContext (sourceFiniteOriginPhotonReader Ap An branch epsilon s n) (epsilon^2 • n) time).continuous.comp
        (sourceTransferCurrent_continuous false (epsilon^2 • n) 0 _))).const_mul
          (sourceTransferAmplitude Bp branch epsilon s n))).const_mul Complex.I

/-- The finite-age return keeps its actual initial/final boundary and subtracts no source correction by assumption. -/
theorem sourceTransferOrigin_integral (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    (∫a in (0:ℝ)..age,
      sourceTransferOriginKernel sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time a-
      sourceTransferOriginCorrection sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time a)=
      sourceTransferOriginBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age := by
  simp_rw [sourceTransferOrigin_split,add_sub_cancel_right]
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _=>sourceTransferOrigin_derivative sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time a)
    ((rate_continuous sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time).intervalIntegrable (0:ℝ) age)
  have initial : sourceTransferOriginBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time 0=0 := by
    simp only [sourceTransferOriginBoundary,sub_self,map_zero,inner_zero_right,mul_zero,add_zero]
  simpa only [initial,sub_zero] using generated

private theorem shift_add (A B : Fin 4→FiberOperators) (q : PhysicalMomentum) :
    shiftCoefficients (A+B) q=shiftCoefficients A q+shiftCoefficients B q := by
  funext k
  cases k using Fin.cases
  · simp only [shiftCoefficients,Fin.cases_zero,Pi.add_apply,smul_add,Finset.sum_add_distrib]
    abel
  · simp only [shiftCoefficients,Fin.cases_succ,Pi.add_apply]
private theorem adjoint_add (A B : Fin 4→FiberOperators) :
    adjointCoefficients (A+B)=adjointCoefficients A+adjointCoefficients B := by
  funext k
  simp only [adjointCoefficients,Pi.add_apply,map_add]
private theorem onlyTime_smul (c : ℂ) (A : FiberOperators) : c • onlyTime A=onlyTime (c • A) := by
  funext k
  by_cases zero:k=0 <;> simp only [onlyTime,zero,if_true,if_false,Pi.smul_apply,fiber_zero]
private theorem onlyTime_add (A B : FiberOperators) : onlyTime A+onlyTime B=onlyTime (A+B) := by
  funext k
  by_cases zero:k=0 <;> simp only [onlyTime,zero,if_true,if_false,Pi.add_apply,add_zero]
private theorem onlyTime_adjoint (A : FiberOperators) : adjointCoefficients (onlyTime A)=onlyTime A.adjoint := by
  funext k
  by_cases zero:k=0 <;> simp only [adjointCoefficients,onlyTime,zero,if_true,if_false,map_zero]
private theorem ordered_add_left (A C B : Fin 4→FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    orderedWord (A+C) B q time age=orderedWord A B q time age+orderedWord C B q time age := by
  simp only [orderedWord,orderedLeft,shift_add,Pi.add_apply,ContinuousLinearMap.add_compLpL,
    mul_add,add_mul,Finset.sum_add_distrib]
private theorem ordered_add_right (A B C : Fin 4→FiberOperators) (q : PhysicalMomentum) (time age : ℝ) :
    orderedWord A (B+C) q time age=orderedWord A B q time age+orderedWord A C q time age := by
  simp only [orderedWord,orderedRight,Pi.add_apply,ContinuousLinearMap.add_compLpL,
    mul_add,add_mul,Finset.sum_add_distrib]

/-- Both non-origin components are the original epsilon-squared literal/fast jet and complete frame residual. -/
def sourceTransferDensityTail (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  fun k=>∑j : Fin 2,complexCoefficients (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n j.succ)) k

def sourceTransferFrequencyTail (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  fun k=>∑j : Fin 2,complexFrequencyCoefficients (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n j.succ)) k

private theorem density_split (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceFinitePoleDensity branch epsilon s n=
      onlyTime (sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginCanonicalFiber 0)+
      sourceTransferDensityTail branch epsilon s n := by
  funext k
  rw [sourceFinitePoleDensity,Fin.sum_univ_succ]
  change complexCoefficients (originalComplexDirection (PreparationPhysicalNativePoleChargeReturn.sourcePoleOriginField branch epsilon s n)) k+_= _
  rw [sourceFiniteOrigin_density]
  rfl
private theorem frequency_split (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceFinitePoleFrequency branch epsilon s n=
      onlyTime (sourceFiniteOriginAmplitude branch epsilon s n • (-sourceNativeOriginCanonicalFiber 0))+
      sourceTransferFrequencyTail branch epsilon s n := by
  funext k
  rw [sourceFinitePoleFrequency,Fin.sum_univ_succ]
  change complexFrequencyCoefficients (originalComplexDirection (PreparationPhysicalNativePoleChargeReturn.sourcePoleOriginField branch epsilon s n)) k+_= _
  rw [sourceFiniteOrigin_frequency]
  rfl

def sourceTransferReaderTail (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • (sourcePhotonEmitter An branch epsilon s n • sourceTransferDensityTail branch epsilon s n+
    adjointCoefficients (shiftCoefficients (sourcePhotonEmitter Ap branch epsilon s n • sourceTransferDensityTail branch epsilon s n) (-(epsilon^2 • n))))
def sourceTransferForceTail (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  sourcePhotonEmitter leg branch epsilon s n • sourceTransferFrequencyTail branch epsilon s n

def sourceTransferBackwardTail (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  shiftCoefficients (adjointCoefficients (sourceTransferForceTail leg branch epsilon s n)) (epsilon^2 • n)

private theorem reader_split (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceFinitePhotonReader Ap An branch epsilon s n=
      onlyTime (sourceFiniteOriginPhotonReader Ap An branch epsilon s n)+sourceTransferReaderTail Ap An branch epsilon s n := by
  have origin :
      (2:ℂ)⁻¹ • (sourcePhotonEmitter An branch epsilon s n •
        onlyTime (sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginCanonicalFiber 0)+
      adjointCoefficients (shiftCoefficients (sourcePhotonEmitter Ap branch epsilon s n •
        onlyTime (sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginCanonicalFiber 0)) (-(epsilon^2 • n))))=
      onlyTime (sourceFiniteOriginPhotonReader Ap An branch epsilon s n) := by
    rw [onlyTime_smul,onlyTime_smul,onlyTime_shift,onlyTime_adjoint,onlyTime_add,onlyTime_smul]
    congr 1
    rw [sourceFiniteOriginPhotonReader,sourceFiniteOrigin_density]
    rfl
  rw [sourceFinitePhotonReader]
  simp only [sourceFinitePhotonDensity,density_split,smul_add,shift_add,adjoint_add]
  rw [←origin]
  simp only [sourceTransferReaderTail]
  module

private theorem force_split (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    sourceFinitePhotonFrequency leg branch epsilon s n=
      onlyTime ((-sourceTransferAmplitude leg branch epsilon s n) • sourceNativeOriginCanonicalFiber 0)+
        sourceTransferForceTail leg branch epsilon s n := by
  rw [sourceFinitePhotonFrequency,frequency_split,smul_add,onlyTime_smul]
  simp only [sourceTransferAmplitude,sourceTransferForceTail,smul_neg,smul_smul,fiber_neg]

private theorem backward_split (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    shiftCoefficients (adjointCoefficients (sourceFinitePhotonFrequency leg branch epsilon s n)) (epsilon^2 • n)=
      onlyTime (((-sourceTransferAmplitude leg branch epsilon s n) • sourceNativeOriginCanonicalFiber 0).adjoint)+
        sourceTransferBackwardTail leg branch epsilon s n := by
  rw [force_split,adjoint_add,shift_add,onlyTime_adjoint,onlyTime_shift]
  rfl

/-- Six non-origin blocks retain all eight non-OO source crosses, since each tail contains both jet and residual. -/
def sourceTransferRemainderOperator (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  let Jo:=onlyTime (sourceFiniteOriginPhotonReader Ap An branch epsilon s n)
  let Jt:=sourceTransferReaderTail Ap An branch epsilon s n
  let Bo:=onlyTime (((-sourceTransferAmplitude Bn branch epsilon s n) • sourceNativeOriginCanonicalFiber 0).adjoint)
  let Bt:=sourceTransferBackwardTail Bn branch epsilon s n
  let Fo:=onlyTime ((-sourceTransferAmplitude Bp branch epsilon s n) • sourceNativeOriginCanonicalFiber 0)
  let Ft:=sourceTransferForceTail Bp branch epsilon s n
  let q:=epsilon^2 • n
  Complex.I • ((orderedWord Bo Jt (-q) age time+orderedWord Bt Jo (-q) age time+orderedWord Bt Jt (-q) age time)-
    (orderedWord Jo Ft q time age+orderedWord Jt Fo q time age+orderedWord Jt Ft q time age))

def sourceTransferFieldTail (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ :=
  sourceActualScatteringRead sideL edgeL sideR edgeR (sourceTransferRemainderOperator Ap An Bp Bn branch epsilon s n time age)

private theorem read_add (sideL edgeL sideR edgeR : Fin 2) (A B : FullMatterL2→L[ℂ]FullMatterL2) :
    sourceActualScatteringRead sideL edgeL sideR edgeR (A+B)=
      sourceActualScatteringRead sideL edgeL sideR edgeR A+sourceActualScatteringRead sideL edgeL sideR edgeR B := by
  simp only [sourceActualScatteringRead_source,add_apply,inner_add_right]

private theorem origin_read (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    sourceActualScatteringRead sideL edgeL sideR edgeR
      (Complex.I • (orderedWord
        (onlyTime (((-sourceTransferAmplitude Bn branch epsilon s n) • sourceNativeOriginCanonicalFiber 0).adjoint))
        (onlyTime (sourceFiniteOriginPhotonReader Ap An branch epsilon s n)) (-(epsilon^2 • n)) age time-
      orderedWord (onlyTime (sourceFiniteOriginPhotonReader Ap An branch epsilon s n))
        (onlyTime ((-sourceTransferAmplitude Bp branch epsilon s n) • sourceNativeOriginCanonicalFiber 0)) (epsilon^2 • n) time age))=
      sourceTransferOriginKernel sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age := by
  rw [word_time,word_time]
  have grouped (A B : FullMatterL2→L[ℂ]FullMatterL2) :
      Complex.I • ((coordinateLeg 0).adjoint*A*coordinateLeg 0-(coordinateLeg 0).adjoint*B*coordinateLeg 0)=
      (coordinateLeg 0).adjoint*(Complex.I • (A-B))*coordinateLeg 0 := by
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  rw [grouped]
  exact sourceActualScatteringRead_inserted sideL edgeL sideR edgeR _

/-- The complete finite response is consumed: the exact origin sector, every original non-origin field cross and independent full contact. -/
theorem sourceFinitePoleResponse_split (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) :
    sourceFinitePoleResponse sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age=
      (sourceTransferOriginKernel sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age+
        sourceTransferFieldTail sideL edgeL sideR edgeR Ap An Bp Bn branch epsilon s n time age,
      sourceActualScatteringRead sideL edgeL sideR edgeR
        (contactWord (sourceFinitePhotonContact Ap An Bp Bn branch epsilon s n) time)) := by
  unfold sourceFinitePoleResponse
  rw [backward_split,reader_split,force_split]
  apply Prod.ext
  · change sourceActualScatteringRead sideL edgeL sideR edgeR _=_
    have distribute (Bo Bt Jo Jt Fo Ft : Fin 4→FiberOperators) (q : PhysicalMomentum) :
        Complex.I • (orderedWord (Bo+Bt) (Jo+Jt) (-q) age time-orderedWord (Jo+Jt) (Fo+Ft) q time age)=
        Complex.I • (orderedWord Bo Jo (-q) age time-orderedWord Jo Fo q time age)+
        Complex.I • ((orderedWord Bo Jt (-q) age time+orderedWord Bt Jo (-q) age time+orderedWord Bt Jt (-q) age time)-
          (orderedWord Jo Ft q time age+orderedWord Jt Fo q time age+orderedWord Jt Ft q time age)) := by
      simp only [ordered_add_left,ordered_add_right,smul_add,smul_sub]
      abel
    rw [distribute,read_add,origin_read]
    rfl
  · rfl

/-- Actual physical-frequency scattering returns the true finite-transfer boundary derivative, both source corrections and all remaining fields/contact. -/
theorem sourcePhotonFrequencyResidue_boundary (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : PreparationVacuumPhysicalCharacteristic.spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in PreparationVacuumPhysicalCharacteristic.scaleApproach,
      sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val
        (PreparationVacuumPhysicalPoleSheet.sourceSheet branch n unit e.val) n time age=
      (deriv (sourceTransferOriginBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch e.val
        (PreparationVacuumPhysicalPoleSheet.sourceSheet branch n unit e.val) n time) age+
      sourceTransferOriginCorrection sideL edgeL sideR edgeR Ap An Bp Bn branch e.val
        (PreparationVacuumPhysicalPoleSheet.sourceSheet branch n unit e.val) n time age+
      sourceTransferFieldTail sideL edgeL sideR edgeR Ap An Bp Bn branch e.val
        (PreparationVacuumPhysicalPoleSheet.sourceSheet branch n unit e.val) n time age,
      sourceActualScatteringRead sideL edgeL sideR edgeR
        (contactWord (sourceFinitePhotonContact Ap An Bp Bn branch e.val
          (PreparationVacuumPhysicalPoleSheet.sourceSheet branch n unit e.val) n) time)) := by
  filter_upwards [sourcePhotonScatteringFrequencyResidue_finite sideL edgeL sideR edgeR Ap An Bp Bn branch n unit time age]
    with e actual
  rw [actual,sourceFinitePoleResponse_split,sourceTransferOrigin_split,
    (sourceTransferOrigin_derivative sideL edgeL sideR edgeR Ap An Bp Bn branch e.val _ n time age).deriv]

end LowEnergy.PreparationPhysicalFiniteTransferWard
