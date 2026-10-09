import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualCurrentWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualRetardedWard
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
open PreparationPhysicalFiniteTransferWard PreparationPhysicalFiniteObservationSoftReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationPhysicalChargedSoftScatteringReturn
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

/-- The original complete full-current field feeds all four density and frequency coordinates. -/
def sourceActualFullDensity (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  sourceActualSoftAmplitude leg branch n unit e • sourceFinitePoleDensity branch e.val (sourceSheet branch n unit e.val) n

def sourceActualFullFrequency (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  sourceActualSoftAmplitude leg branch n unit e • sourceFinitePoleFrequency branch e.val (sourceSheet branch n unit e.val) n

def sourceActualFullReader (Ap An : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • (sourceActualFullDensity An branch n unit e+
    adjointCoefficients (shiftCoefficients (sourceActualFullDensity Ap branch n unit e) (-(e.val^2 • n))))

/-- Every source mixed-density/shell cross is retained at the actual finite epsilon. -/
def sourceActualFullContact (Ap An Bp Bn : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • ((sourceActualSoftAmplitude An branch n unit e*sourceActualSoftAmplitude Bp branch n unit e) •
    sourceFinitePoleMixed branch e.val (sourceSheet branch n unit e.val) n+
    adjointCoefficients ((sourceActualSoftAmplitude Ap branch n unit e*sourceActualSoftAmplitude Bn branch n unit e) •
      sourceFinitePoleMixed branch e.val (sourceSheet branch n unit e.val) n))

def sourceActualFullResponse (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ × ℂ :=
  let J:=sourceActualFullReader Ap An branch n unit e
  let backward:=shiftCoefficients (adjointCoefficients (sourceActualFullFrequency Bn branch n unit e)) (e.val^2 • n)
  (sourceActualScatteringRead sideL edgeL sideR edgeR
    (Complex.I • (orderedWord backward J (-(e.val^2 • n)) age time-
      orderedWord J (sourceActualFullFrequency Bp branch n unit e) (e.val^2 • n) time age)),
    sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord (sourceActualFullContact Ap An Bp Bn branch n unit e) time))

/-- The actual full8x8-current family returns this same complete finite expression, simultaneously at every time and age. -/
theorem sourceActualFullResponse_return (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀time age : ℝ,
      sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit time age e=
        sourceActualFullResponse sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e time age := by
  filter_upwards [sourceActualSoftField_coefficients branch n unit] with e coefficients
  intro time age
  simp only [sourceChargedCoupledScattering,sourceChargedSoftFields,sourcePreparedScatteringPair,
    fieldTwoTimeKernel,fieldMixedContact,originalTransferPair]
  unfold Electromagnetic.CanonicalCoframe.realReaderCoefficients Electromagnetic.CanonicalCoframe.realMixedCoefficients
  simp only [(coefficients (legs 0) (legs 0)).1,(coefficients (legs 1) (legs 1)).1,
    (coefficients (legs 2) (legs 2)).2.1,(coefficients (legs 3) (legs 3)).2.1,
    (coefficients (legs 1) (legs 2)).2.2,(coefficients (legs 0) (legs 3)).2.2]
  rfl

def sourceActualReaderTail (Ap An : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • (sourceActualSoftAmplitude An branch n unit e • sourceTransferDensityTail branch e.val (sourceSheet branch n unit e.val) n+
    adjointCoefficients (shiftCoefficients (sourceActualSoftAmplitude Ap branch n unit e • sourceTransferDensityTail branch e.val (sourceSheet branch n unit e.val) n) (-(e.val^2 • n))))
def sourceActualForceTail (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  sourceActualSoftAmplitude leg branch n unit e • sourceTransferFrequencyTail branch e.val (sourceSheet branch n unit e.val) n

def sourceActualBackwardTail (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) : Fin 4→FiberOperators :=
  shiftCoefficients (adjointCoefficients (sourceActualForceTail leg branch n unit e)) (e.val^2 • n)

private theorem reader_split (Ap An : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) :
    sourceActualFullReader Ap An branch n unit e=
      onlyTime (sourceActualWardReader Ap An branch n unit e)+sourceActualReaderTail Ap An branch n unit e := by
  have origin :
      (2:ℂ)⁻¹ • (sourceActualSoftAmplitude An branch n unit e •
        onlyTime (sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n • sourceNativeOriginCanonicalFiber 0)+
      adjointCoefficients (shiftCoefficients (sourceActualSoftAmplitude Ap branch n unit e •
        onlyTime (sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n • sourceNativeOriginCanonicalFiber 0)) (-(e.val^2 • n))))=
      onlyTime (sourceActualWardReader Ap An branch n unit e) := by
    rw [onlyTime_smul,onlyTime_smul,onlyTime_shift,onlyTime_adjoint,onlyTime_add,onlyTime_smul]
    congr 1
    simp only [sourceActualWardReader,sourceActualWardAmplitude,sourceSoftNoetherReader,
      smul_smul,map_smulₛₗ,starRingEnd_apply]
  rw [sourceActualFullReader]
  simp only [sourceActualFullDensity,density_split,smul_add,shift_add,adjoint_add]
  rw [←origin]
  simp only [sourceActualReaderTail]
  module

private theorem force_split (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) :
    sourceActualFullFrequency leg branch n unit e=
      onlyTime ((-sourceActualWardAmplitude leg branch n unit e) • sourceNativeOriginCanonicalFiber 0)+
        sourceActualForceTail leg branch n unit e := by
  rw [sourceActualFullFrequency,frequency_split,smul_add,onlyTime_smul]
  simp only [sourceActualWardAmplitude,sourceActualForceTail,smul_neg,smul_smul,fiber_neg]

private theorem backward_split (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) :
    shiftCoefficients (adjointCoefficients (sourceActualFullFrequency leg branch n unit e)) (e.val^2 • n)=
      onlyTime (((-sourceActualWardAmplitude leg branch n unit e) • sourceNativeOriginCanonicalFiber 0).adjoint)+
        sourceActualBackwardTail leg branch n unit e := by
  rw [force_split,adjoint_add,shift_add,onlyTime_adjoint,onlyTime_shift]
  rfl

/-- Six non-origin blocks retain all eight non-OO source crosses, since each tail contains both jet and residual. -/
def sourceActualRemainderOperator (Ap An Bp Bn : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  let Jo:=onlyTime (sourceActualWardReader Ap An branch n unit e)
  let Jt:=sourceActualReaderTail Ap An branch n unit e
  let Bo:=onlyTime (((-sourceActualWardAmplitude Bn branch n unit e) • sourceNativeOriginCanonicalFiber 0).adjoint)
  let Bt:=sourceActualBackwardTail Bn branch n unit e
  let Fo:=onlyTime ((-sourceActualWardAmplitude Bp branch n unit e) • sourceNativeOriginCanonicalFiber 0)
  let Ft:=sourceActualForceTail Bp branch n unit e
  let q:=e.val^2 • n
  Complex.I • ((orderedWord Bo Jt (-q) age time+orderedWord Bt Jo (-q) age time+orderedWord Bt Jt (-q) age time)-
    (orderedWord Jo Ft q time age+orderedWord Jt Fo q time age+orderedWord Jt Ft q time age))

def sourceActualFieldTail (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ :=
  sourceActualScatteringRead sideL edgeL sideR edgeR (sourceActualRemainderOperator Ap An Bp Bn branch n unit e time age)

private theorem read_add (sideL edgeL sideR edgeR : Fin 2) (A B : FullMatterL2→L[ℂ]FullMatterL2) :
    sourceActualScatteringRead sideL edgeL sideR edgeR (A+B)=
      sourceActualScatteringRead sideL edgeL sideR edgeR A+sourceActualScatteringRead sideL edgeL sideR edgeR B := by
  simp only [sourceActualScatteringRead_source,add_apply,inner_add_right]

private theorem origin_read (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) :
    sourceActualScatteringRead sideL edgeL sideR edgeR
      (Complex.I • (orderedWord
        (onlyTime (((-sourceActualWardAmplitude Bn branch n unit e) • sourceNativeOriginCanonicalFiber 0).adjoint))
        (onlyTime (sourceActualWardReader Ap An branch n unit e)) (-(e.val^2 • n)) age time-
      orderedWord (onlyTime (sourceActualWardReader Ap An branch n unit e))
        (onlyTime ((-sourceActualWardAmplitude Bp branch n unit e) • sourceNativeOriginCanonicalFiber 0)) (e.val^2 • n) time age))=
      sourceActualWardKernel sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age := by
  rw [word_time,word_time]
  have grouped (A B : FullMatterL2→L[ℂ]FullMatterL2) :
      Complex.I • ((coordinateLeg 0).adjoint*A*coordinateLeg 0-(coordinateLeg 0).adjoint*B*coordinateLeg 0)=
      (coordinateLeg 0).adjoint*(Complex.I • (A-B))*coordinateLeg 0 := by
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
  rw [grouped]
  exact sourceActualScatteringRead_inserted sideL edgeL sideR edgeR _

/-- The complete finite response is consumed: the exact origin sector, every original non-origin field cross and independent full contact. -/
theorem sourceActualFullResponse_split (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) :
    sourceActualFullResponse sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age=
      (sourceActualWardKernel sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age+
        sourceActualFieldTail sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age,
      sourceActualScatteringRead sideL edgeL sideR edgeR
        (contactWord (sourceActualFullContact Ap An Bp Bn branch n unit e) time)) := by
  unfold sourceActualFullResponse
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

/-- The same actual normalized full response now consumes the true two-offset Ward boundary, explicit corrections, all non-origin fields and the independent contact. -/
theorem sourceActualFullWard_return (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀time age : ℝ,
      sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit time age e=
      (sourceActualWardRate sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e time age+
       sourceActualWardCorrection sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e time age+
       sourceActualFieldTail sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e time age,
       sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord
        (sourceActualFullContact (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e) time)) := by
  filter_upwards [sourceActualFullResponse_return sideL edgeL sideR edgeR legs branch n unit] with e returned
  intro time age
  rw [returned time age,sourceActualFullResponse_split,sourceActualWard_split]

end LowEnergy.PreparationPhysicalActualRetardedWard
