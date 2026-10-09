import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualSoftFiniteResponse
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteTransferResponse

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

/-- The complete full8x8 current keeps its own independent beta reader and original 2omega normalization. -/
def sourceActualWardAmplitude (leg : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : ℂ :=
  sourceActualSoftAmplitude leg branch n unit e*sourceFiniteOriginAmplitude branch e.val (sourceSheet branch n unit e.val) n

/-- The density reader is the actual full-current amplitude applied to the already generated whole252 Q, not the charge generator X. -/
def sourceActualWardReader (Ap An : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (e : scaleDomain) : FiberOperators :=
  sourceSoftNoetherReader 0 (sourceActualWardAmplitude Ap branch n unit e) (sourceActualWardAmplitude An branch n unit e)

/-- This is the original Q/negative-Q-adjoint origin sector, with the actual nonzero momentum transfer. -/
def sourceActualWardOperator (Ap An Bp Bn : SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  Complex.I •
    (sourceTransferWord (((-sourceActualWardAmplitude Bn branch n unit e) • sourceNativeOriginCanonicalFiber 0).adjoint)
      (sourceActualWardReader Ap An branch n unit e) (-(e.val^2 • n)) age time-
    sourceTransferWord (sourceActualWardReader Ap An branch n unit e)
      ((-sourceActualWardAmplitude Bp branch n unit e) • sourceNativeOriginCanonicalFiber 0) (e.val^2 • n) time age)

def sourceActualWardKernel (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceActualWardOperator Ap An Bp Bn branch n unit e time age)

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
def sourceActualWardBoundary (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ :=
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceActualWardReader Ap An branch n unit e
  let q:=e.val^2 • n;
  -star (sourceActualWardAmplitude Bn branch n unit e)*inner ℂ u
    (sourceTransferSpatial true 0 (-q) age (rightContext J q time v)-
      sourceTransferSpatial true 0 (-q) 0 (rightContext J q time v))+
  sourceActualWardAmplitude Bp branch n unit e*inner ℂ u
    (leftContext J q time (sourceTransferSpatial false q 0 age v-sourceTransferSpatial false q 0 0 v))

def sourceActualWardRate (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ :=
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceActualWardReader Ap An branch n unit e
  let q:=e.val^2 • n
  Complex.I*((-star (sourceActualWardAmplitude Bn branch n unit e))*inner ℂ u
    (sourceTransferCurrent true 0 (-q) age (rightContext J q time v))+
  sourceActualWardAmplitude Bp branch n unit e*inner ℂ u
    (leftContext J q time (sourceTransferCurrent false q 0 age v)))

def sourceActualWardCorrection (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (Complex.I •
      (sourceTransferWord ((-star (sourceActualWardAmplitude Bn branch n unit e)) • sourceTransferDefect true (e.val^2 • n))
        (sourceActualWardReader Ap An branch n unit e) (-(e.val^2 • n)) age time+
       sourceTransferWord (sourceActualWardReader Ap An branch n unit e)
        (sourceActualWardAmplitude Bp branch n unit e • sourceTransferDefect false (e.val^2 • n)) (e.val^2 • n) time age))

/-- The actual finite-transfer origin response is the boundary rate plus its explicit spatial-current and full-Y correction. -/
theorem sourceActualWard_split (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) :
    sourceActualWardKernel sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age=
      sourceActualWardRate sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age+
        sourceActualWardCorrection sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age := by
  have positive:=physical_current false (e.val^2 • n)
  have negative:=physical_current true (e.val^2 • n)
  simp only [Bool.false_eq_true,↓reduceIte] at positive negative
  simp only [sourceActualWardKernel,sourceActualWardOperator,map_smulₛₗ,starRingEnd_apply,star_neg]
  rw [negative,positive]
  simp only [word_smul_left,word_smul_right,word_add_left,word_add_right,sourceChargedQuantumRead_generated,
    smul_apply,add_apply,sub_apply,inner_smul_right,inner_add_right,inner_sub_right,current_left,current_right]
  simp only [sourceActualWardRate,sourceActualWardCorrection,sourceChargedQuantumRead_generated,
    word_smul_left,word_smul_right,smul_apply,add_apply,mul_apply_eq_comp,inner_smul_right,inner_add_right]
  ring

/-- No zero-transfer substitution occurs: the derivative uses the (q,0) and (0,−q) source flows. -/
theorem sourceActualWard_derivative (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) :
    HasDerivAt (sourceActualWardBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time)
      (sourceActualWardRate sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age) age := by
  let u:=sourceChargedFilteredPacket sideL edgeL
  let v:=sourceChargedFilteredPacket sideR edgeR
  let J:=sourceActualWardReader Ap An branch n unit e
  let q:=e.val^2 • n
  have negative:=((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceTransferSpatial_derivative true 0 (-q) (rightContext J q time v) age).sub_const
      (sourceTransferSpatial true 0 (-q) 0 (rightContext J q time v)))
  have positive:=(((innerSL ℂ u).comp (leftContext J q time)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceTransferSpatial_derivative false q 0 v age).sub_const (sourceTransferSpatial false q 0 0 v))
  have generated:=(negative.const_mul (-star (sourceActualWardAmplitude Bn branch n unit e))).add
    (positive.const_mul (sourceActualWardAmplitude Bp branch n unit e))
  convert! generated using 1
  change sourceActualWardRate sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age=
    (-star (sourceActualWardAmplitude Bn branch n unit e))*inner ℂ u
      (Complex.I • sourceTransferCurrent true 0 (-q) age (rightContext J q time v))+
    sourceActualWardAmplitude Bp branch n unit e*inner ℂ u
      (leftContext J q time (Complex.I • sourceTransferCurrent false q 0 age v))
  simp only [sourceActualWardRate,inner_smul_right,map_smul,u,v,J,q]
  ring

theorem sourceActualWardRate_continuous (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time : ℝ) :
    Continuous (sourceActualWardRate sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time) := by
  exact (((continuous_const.inner (sourceTransferCurrent_continuous true 0 (-(e.val^2 • n)) _)).const_mul
    (-star (sourceActualWardAmplitude Bn branch n unit e))).add
      ((continuous_const.inner ((leftContext (sourceActualWardReader Ap An branch n unit e) (e.val^2 • n) time).continuous.comp
        (sourceTransferCurrent_continuous false (e.val^2 • n) 0 _))).const_mul
          (sourceActualWardAmplitude Bp branch n unit e))).const_mul Complex.I

/-- The finite-age return keeps its actual initial/final boundary and subtracts no source correction by assumption. -/
theorem sourceActualWard_integral (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time age : ℝ) :
    (∫a in (0:ℝ)..age,
      sourceActualWardKernel sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time a-
      sourceActualWardCorrection sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time a)=
      sourceActualWardBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time age := by
  simp_rw [sourceActualWard_split,add_sub_cancel_right]
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _=>sourceActualWard_derivative sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time a)
    ((sourceActualWardRate_continuous sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time).intervalIntegrable (0:ℝ) age)
  have initial : sourceActualWardBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time 0=0 := by
    simp only [sourceActualWardBoundary,sub_self,map_zero,inner_zero_right,mul_zero,add_zero]
  simpa only [initial,sub_zero] using generated

theorem sourceActualWardBoundary_initial (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourceChargedSoftLeg)
    (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (e : scaleDomain) (time : ℝ) :
    sourceActualWardBoundary sideL edgeL sideR edgeR Ap An Bp Bn branch n unit e time 0=0 := by
  simp only [sourceActualWardBoundary,sub_self,map_zero,inner_zero_right,mul_zero,add_zero]

end LowEnergy.PreparationPhysicalActualRetardedWard
