import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyPoleIsolation
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceLockedChargeSoftWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance poleTensorQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationVacuumObservedBoundaryResidue PreparationVacuumPhysicalCharacteristic

open PreparationVacuumCurrentSignalOperator PreparationVacuumMovingPoleGaussReturn
open PreparationPhysicalFilteredLockedChargeReturn PreparationVacuumPhysicalElectromagneticDirection

def sourceEnergyPoleFrequency (shift : Position) (branch : Fin 2) : ℝ :=
  Real.sqrt ((if branch=0 then (594/1675:ℝ) else 18/25)*spatialSquare (physicalMomentum shift))

/-- Every nonzero spatial source momentum generates both genuine propagating frequencies. -/
theorem sourceEnergyPoleFrequency_generated (shift : Position)
    (spatial : (0:ℝ)<PreparationVacuumPhysicalCharacteristic.spatialSquare (physicalMomentum shift)) (branch : Fin 2) :
    0<sourceEnergyPoleFrequency shift branch ∧
      sourceChargedDenominator (physicalMomentum shift)
        (Complex.I*(sourceEnergyPoleFrequency shift branch:ℂ)) branch.succ=0 := by
  have coefficient : 0<(if branch=0 then (594/1675:ℝ) else 18/25):=by split_ifs <;> norm_num
  constructor
  · exact Real.sqrt_pos.mpr (mul_pos coefficient spatial)
  · rw [sourceEnergyDenominator_zero_iff,sourceEnergyPoleFrequency,Real.sq_sqrt (mul_pos coefficient spatial).le]
    fin_cases branch <;> norm_num [Fin.ext_iff]

/-- The complete source retainer current is contracted before either external source state is selected. -/
def sourceEnergyPoleEmitter (q : PhysicalResponsePoint) (n : PhysicalMomentum) (frequency : ℝ) (i : Fin 3) : SourceOp :=
  ∑j : Fin 289,(slowFastFrame.transpose*sourceNativeReaderFirst (fixedMomentum n (Complex.I*(frequency:ℂ))))
    (fiveIndex ⟨i.val,by omega⟩) j • (-sourceBaseNumerator q n frequency 0 j)

theorem sourceEnergyPoleEmitter_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (frequency : ℝ)
    (i : Fin 3) (left right : RestStateIndex) :
    sourceSlowRead (sourceNativeBoundaryResidue q n frequency left right) ⟨i.val,by omega⟩=
      sourcePoleRead q.epsilon q.precision 0 0 left right (sourceEnergyPoleEmitter q n frequency i) := by
  unfold sourceSlowRead sourceNativeBoundaryResidue
  rw [if_pos i.isLt,Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec,dotProduct,sourceWholeCurrentNumerator,sourceEnergyPoleEmitter,
    map_sum,map_smul,map_neg,smul_eq_mul]

/-- Every original W0/W1/W2 field component enters its actual source/observer residue tensor. -/
theorem sourcePhysicalEnergyBoundary_all_axes (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ∑i : Fin 3,sourceChargedDenominatorResidue (physicalMomentum shift) frequency i*
        sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
          (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency i)*
        (∑k : Fin 4,fixedMomentum (physicalMomentum shift) (Complex.I*(frequency:ℂ)) k*
          sourceChargedEnergyRead (fieldDirection (sourceEnergyAxisField i k)) shift sideL edgeL sideR edgeR) := by
  rw [sourcePhysicalEnergyBoundary_channels]
  simp only [sourceEnergyPoleEmitter_generated,sourcePhysicalEnergyChannel_axes]

/-- The spatial remainder is an actual same-Phi current tensor, rather than a prescribed detector defect. -/
def sourceEnergySpatialRemainder (shift : Position) (sideL edgeL sideR edgeR : Fin 2) : ℂ :=
  ((ActionNormalization.phaseMomentum:ℂ)*(Real.sqrt 30:ℂ)/5)*
    ∑j : Fin 3,(physicalMomentum shift j:ℂ)*sourcePhysicalCliffordSpatialCurrent j shift sideL edgeL sideR edgeR

attribute [local irreducible] sourceEnergyPoleEmitter sourceNativeReaderFirst sourceBaseNumerator
  sourcePoleRead slowFastFrame sourceNativeBoundaryResidue sourceSlowRead

/-- Both independent source states read the original retainer operator; the test states read their actual canonical and spatial currents. -/
theorem sourcePhysicalEnergyBoundary_two_charge_tensor (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ((sourceChargedTemporalCoefficient 2:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
        sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
          (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency 2)*
        ((frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR+
          sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR) := by
  have emitter:=sourceEnergyPoleEmitter_generated q (physicalMomentum shift) frequency 2
    (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
  have index : (⟨(2:Fin 3).val,by omega⟩:Fin 5)=(2:Fin 5):=rfl
  rw [index] at emitter
  rw [sourcePhysicalEnergyBoundary_two_isolated q shift frequency nonzero pole,emitter]
  have current:=sourcePhysicalEnergyChannel_two_charge shift frequency sideL edgeL sideR edgeR
  change (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
    (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR+sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR at current
  rw [←current]
  ring

private theorem temporalResidue_ne_zero (frequency : ℝ) (nonzero : frequency≠0) (i : Fin 3) :
    ((sourceChargedTemporalCoefficient i:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹≠0 := by
  apply inv_ne_zero
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sourceChargedTemporalCoefficient_nonzero i))
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr nonzero))

/-- Nonzero visibility is decided by the actual emitting matrix and the entire physical charge-plus-spatial current. -/
theorem sourcePhysicalEnergyBoundary_two_visible_iff (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency≠0 ↔
      sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
        (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency 2)≠0 ∧
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR+
        sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR≠0 := by
  have h : (ActionNormalization.phaseMomentum:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ActionNormalization.phaseMomentum_positive.ne'
  calc
    _ ↔ (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency≠0 := by simp [h]
    _ ↔ _ := by
      rw [sourcePhysicalEnergyBoundary_two_charge_tensor q shift frequency nonzero pole]
      constructor
      · intro visible
        exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp visible).1).2,(mul_ne_zero_iff.mp visible).2⟩
      · rintro ⟨emitting,reading⟩
        exact mul_ne_zero (mul_ne_zero (temporalResidue_ne_zero frequency nonzero 2) emitting) reading

/-- Both source labels are the actual charged rest indices; no preferred nonzero entry is selected. -/
def sourceEnergyEmitterMatrix (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ) (i : Fin 3) :
    Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ := fun left right=>
  sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex left.1 left.2) (sourceChargedRestIndex right.1 right.2)
    (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency i)

def sourceEnergyTestCurrentMatrix (shift : Position) (frequency : ℝ) : Matrix (Fin 2×Fin 2) (Fin 2×Fin 2) ℂ :=
  fun left right=>(frequency:ℂ)*sourceFilteredChargeFormFactor shift left.1 left.2 right.1 right.2+
    sourceEnergySpatialRemainder shift left.1 left.2 right.1 right.2

/-- The full source/test tensor contains all 256 independent combinations. -/
def sourceEnergyBoundaryTensor (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ) :
    Matrix ((Fin 2×Fin 2)×(Fin 2×Fin 2)) ((Fin 2×Fin 2)×(Fin 2×Fin 2)) ℂ :=
  fun source test=>sourcePhysicalEnergyBoundary q shift source.1.1 source.1.2 source.2.1 source.2.2
    test.1.1 test.1.2 test.2.1 test.2.2 frequency

private theorem matrix_nonzero_iff {α β : Type} (A : Matrix α β ℂ) : A≠0 ↔ ∃a b,A a b≠0 := by
  classical
  constructor
  · intro nonzero
    by_contra noEntry
    apply nonzero
    ext a b
    by_contra unequal
    exact noEntry ⟨a,b,unequal⟩
  · rintro ⟨a,b,nonzero⟩ zero
    exact nonzero (by rw [zero];rfl)

/-- Actual cubic-boundary visibility is a whole-matrix source criterion on both independent legs. -/
theorem sourceEnergyBoundaryTensor_two_visible_iff (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0) :
    sourceEnergyBoundaryTensor q shift frequency≠0 ↔
      sourceEnergyEmitterMatrix q shift frequency 2≠0 ∧ sourceEnergyTestCurrentMatrix shift frequency≠0 := by
  rw [matrix_nonzero_iff,matrix_nonzero_iff,matrix_nonzero_iff]
  constructor
  · rintro ⟨⟨sourceL,sourceR⟩,⟨testL,testR⟩,visible⟩
    have generated:=(sourcePhysicalEnergyBoundary_two_visible_iff q shift frequency nonzero pole
      sourceL.1 sourceL.2 sourceR.1 sourceR.2 testL.1 testL.2 testR.1 testR.2).mp visible
    exact ⟨⟨sourceL,sourceR,generated.1⟩,⟨testL,testR,generated.2⟩⟩
  · rintro ⟨⟨sourceL,sourceR,emitting⟩,⟨testL,testR,reading⟩⟩
    exact ⟨(sourceL,sourceR),(testL,testR),
      (sourcePhysicalEnergyBoundary_two_visible_iff q shift frequency nonzero pole
        sourceL.1 sourceL.2 sourceR.1 sourceR.2 testL.1 testL.2 testR.1 testR.2).mpr ⟨emitting,reading⟩⟩

/-- A charge-only residue read is exactly the vanishing of the generated spatial-current contribution on a nonzero emitter. -/
theorem sourcePhysicalEnergyBoundary_two_charge_condition (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2)
    (emitting : sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
      (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency 2)≠0) :
    ((ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ((sourceChargedTemporalCoefficient 2:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
        sourcePoleRead q.epsilon q.precision 0 0 (sourceChargedRestIndex a b) (sourceChargedRestIndex c d)
          (sourceEnergyPoleEmitter q (physicalMomentum shift) frequency 2)*
        ((frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR)) ↔
      sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR=0 := by
  rw [sourcePhysicalEnergyBoundary_two_charge_tensor q shift frequency nonzero pole]
  rw [mul_right_inj' (mul_ne_zero (temporalResidue_ne_zero frequency nonzero 2) emitting)]
  exact add_eq_left

/-- Charge-only factorization of the whole tensor is equivalent to the actual spatial-current matrix vanishing. -/
theorem sourceEnergyBoundaryTensor_two_charge_condition (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (emitting : sourceEnergyEmitterMatrix q shift frequency 2≠0) :
    (∀a b c d sideL edgeL sideR edgeR : Fin 2,
      (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
        ((sourceChargedTemporalCoefficient 2:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
          sourceEnergyEmitterMatrix q shift frequency 2 (a,b) (c,d)*
          ((frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR)) ↔
      (fun left right : Fin 2×Fin 2=>sourceEnergySpatialRemainder shift left.1 left.2 right.1 right.2)=0 := by
  obtain ⟨sourceL,sourceR,sourceNonzero⟩:=(matrix_nonzero_iff _).mp emitting
  constructor
  · intro factorization
    funext left right
    exact (sourcePhysicalEnergyBoundary_two_charge_condition q shift frequency nonzero pole
      sourceL.1 sourceL.2 sourceR.1 sourceR.2 left.1 left.2 right.1 right.2 sourceNonzero).mp
        (factorization sourceL.1 sourceL.2 sourceR.1 sourceR.2 left.1 left.2 right.1 right.2)
  · intro zero a b c d sideL edgeL sideR edgeR
    rw [sourcePhysicalEnergyBoundary_two_charge_tensor q shift frequency nonzero pole]
    have spatial : sourceEnergySpatialRemainder shift sideL edgeL sideR edgeR=0:=
      congrFun (congrFun zero (sideL,edgeL)) (sideR,edgeR)
    rw [spatial,add_zero]
    rfl

/-- The locked direction is another actual energy/current insertion; it is not substituted for a native propagation column. -/
theorem sourcePhysicalLockedEnergy_source (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourceChargedEnergyRead (fieldDirection (sourceLockedField 0 2)) shift sideL edgeL sideR edgeR=
      -( -(ActionNormalization.phaseMomentum:ℂ)*(sourceChargedPolarity edgeR:ℂ)*
        sourceChargedVoltageOverlap shift sideL edgeL sideR edgeR+
        (ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
          (PacketNoise.phaseShift shift (sourceFilteredLockedCorrection sideR edgeR))) := by
  rw [sourceLockedEnergy_current,sourceFilteredLockedFormFactor_generated]

end LowEnergy.PreparationPhysicalEnergyPoleChargeReturn
