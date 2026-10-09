import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstPoleChargeCubic

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalResponseChargeGrading
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationPhysicalPoleChargeMatrix PreparationPhysicalCurvatureSheetLimit
open PreparationPhysicalActualPhaseChargeReturn PreparationPhysicalActualNoetherVertexReturn
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalNativeOriginPhaseWard
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumOriginalGreenFeedback PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumNonlinearFieldCurve PreparationVacuumSourceFieldFamily PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumNativeSlowCoupling
open GaussNativeMatter GaussHistoryHilbert SourceQuantumFockGauge GaussQuantumMultiplier GaussFockLift
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open CanonicalGradedCharge CanonicalGradedSpatialSource
open Stage10.CanonicalMatter Stage9C.Material.SpinPair Electromagnetic.CanonicalCoframe
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open Filter Set
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _

/-- Full charge acts on both original independent branches. -/
def sourceResponseFullAd : FullMatrix→ₗ[ℂ]FullMatrix where
  toFun A:=sourceActualGaussChargeMatrix*A-A*sourceActualGaussChargeMatrix
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def opposite (A : SourceMatrix) : FullMatrix :=
  Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))

private theorem blocks_sub (A B C D : SourceMatrix) :
    Matrix.fromBlocks A 0 0 B-Matrix.fromBlocks C 0 0 D=Matrix.fromBlocks (A-C) 0 0 (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

private theorem ad_branch (A : SourceMatrix) :
    sourceResponseFullAd (SourceRealScalarFock.branches A)=opposite (sourceResponsePrimalAd A) := by
  let Q:=Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)
  change Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))*
    Matrix.fromBlocks A 0 0 (-(A.map (starRingEnd ℂ)))-
    Matrix.fromBlocks A 0 0 (-(A.map (starRingEnd ℂ)))*
      Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))=
    Matrix.fromBlocks (Q*A-A*Q) 0 0 ((Q*A-A*Q).map (starRingEnd ℂ))
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,blocks_sub,neg_mul_neg,
    Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul]

private theorem ad_opposite (A : SourceMatrix) :
    sourceResponseFullAd (opposite A)=SourceRealScalarFock.branches (sourceResponsePrimalAd A) := by
  let Q:=Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)
  change Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))*
    Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))-
    Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))*
      Matrix.fromBlocks Q 0 0 (-(Q.map (starRingEnd ℂ)))=
    Matrix.fromBlocks (Q*A-A*Q) 0 0 (-((Q*A-A*Q).map (starRingEnd ℂ)))
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,blocks_sub,neg_mul,mul_neg,neg_zero,
    Matrix.map_sub _ (fun a b=>map_sub (starRingEnd ℂ) a b),Matrix.map_mul]
  congr 1
  abel

private theorem branch_cube (k : Fin 4) :
    sourceResponseFullAd (sourceResponseFullAd (sourceResponseFullAd
      (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k)))))=
      sourceResponseFullAd (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))) := by
  rw [ad_branch,ad_opposite,ad_branch,sourceFirstEnergyPrimal_chargeCube]

/-- Complex physical momentum coefficients are outside the independent-branch map exactly as in the original full200 energy. -/
theorem sourceFirstEnergyFull_chargeCube (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceResponseFullAd (sourceResponseFullAd (sourceResponseFullAd
      (sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1)))=
      sourceResponseFullAd (sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1) := by
  rw [sourceFirstLiteralEnergy_generated]
  simp only [map_sum,map_smul,branch_cube]

/-- These three components are generated from the actual energy and its actual charge action; no projector is an input. -/
def sourceFirstEnergyGrade (g : Fin 3) (p : PhysicalMomentum) (v : Fin 4→ℂ) : FullMatrix :=
  let E:=sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1
  if g=0 then E-sourceResponseFullAd (sourceResponseFullAd E)
  else if g=1 then (1/2:ℂ) • (sourceResponseFullAd (sourceResponseFullAd E)+sourceResponseFullAd E)
  else (1/2:ℂ) • (sourceResponseFullAd (sourceResponseFullAd E)-sourceResponseFullAd E)

def sourcePoleGradeValue (g : Fin 3) : ℂ := ![0,1,-1] g

theorem sourceFirstEnergyGrade_total (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceFirstEnergyGrade 0 p v+sourceFirstEnergyGrade 1 p v+sourceFirstEnergyGrade 2 p v=
      sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1 := by
  simp only [sourceFirstEnergyGrade,ite_true,
    if_neg (show (1:Fin 3)≠0 by decide),if_neg (show (2:Fin 3)≠0 by decide),
    if_neg (show (2:Fin 3)≠1 by decide)]
  module

theorem sourceFirstEnergyGrade_degree (g : Fin 3) (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceResponseFullAd (sourceFirstEnergyGrade g p v)=
      sourcePoleGradeValue g • sourceFirstEnergyGrade g p v := by
  fin_cases g <;> norm_num [sourceFirstEnergyGrade,sourcePoleGradeValue,Fin.ext_iff,
    Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod,map_sub,map_add,map_smul,
    sourceFirstEnergyFull_chargeCube]
  all_goals module

/-- Complete CAR preserves each generated energy channel with the original independent dual signs. -/
theorem sourceFirstEnergyGrade_fiber (g : Fin 3) (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    quantized sourceActualGaussChargeMatrix*quantized (sourceFirstEnergyGrade g p v)-
      quantized (sourceFirstEnergyGrade g p v)*quantized sourceActualGaussChargeMatrix=
        sourcePoleGradeValue g • quantized (sourceFirstEnergyGrade g p v) := by
  have generated:=congrArg quantizer (sourceFirstEnergyGrade_degree g p v)
  change quantizer (sourceActualGaussChargeMatrix*sourceFirstEnergyGrade g p v-
    sourceFirstEnergyGrade g p v*sourceActualGaussChargeMatrix)=_ at generated
  rw [paidCoframeQuantizerComm%,map_smul] at generated
  exact generated

private def fullChargeValue : Mode→ℂ
  | .inl i=> -(sourceWholeWeight i:ℂ)
  | .inr i=> (sourceWholeWeight i:ℂ)

private theorem full_charge_diagonal :
    sourceActualGaussChargeMatrix=Matrix.diagonal fullChargeValue := by
  rw [sourceActualGaussChargeMatrix,sourcePhaseNoether_matrix]
  ext i j
  cases i <;> cases j <;>
    simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.diagonal_apply,fullChargeValue]

private theorem ad_entry (A : FullMatrix) (i j : Mode) :
    sourceResponseFullAd A i j=(fullChargeValue i-fullChargeValue j)*A i j := by
  simp only [sourceResponseFullAd,LinearMap.coe_mk,AddHom.coe_mk,full_charge_diagonal,
    Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

private theorem actual_charge (side edge : Fin 2) :
    fullChargeValue (Sum.inl (sourceChargedQuantumIndex side edge))=(sourceActualPhaseCharge edge:ℂ) := by
  simp only [fullChargeValue,sourceActualColumn_weight,neg_neg]

/-- The actual normalized Gauss preparations directly consume the full charge action. -/
theorem sourceEnergyPrepared_chargeRead (epsilon : ℝ) (precision : 0<epsilon)
    (A : FullMatrix) (i j : ActualPreparedIndex) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
      (lift (quantized (sourceResponseFullAd A)) (sourceChargedGaussPrepared epsilon precision j.1 j.2))=
      ((sourceActualPhaseCharge i.2:ℂ)-(sourceActualPhaseCharge j.2:ℂ))*
        inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
          (lift (quantized A) (sourceChargedGaussPrepared epsilon precision j.1 j.2)) := by
  simp only [sourceChargedEnergyRead_entry,ad_entry,actual_charge]

/-- This is a restriction of the generated full energy channels to the original actual four Gauss columns. -/
def sourceFirstEnergyGradeRead (g : Fin 3) (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (v : Fin 4→ℂ) : Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  fun i j=>inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
    (lift (quantized (sourceFirstEnergyGrade g p v)) (sourceChargedGaussPrepared epsilon precision j.1 j.2))

private theorem literal_entry (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : Fin 4→ℂ) (i j : ActualPreparedIndex) :
    sourceLiteralEnergyWeight p (sourceState sourcePoint.val) v 1
      (Sum.inl (sourceChargedQuantumIndex i.1 i.2)) (Sum.inl (sourceChargedQuantumIndex j.1 j.2))=
        Matrix.diagonal (sourceFirstPreparedCoefficient v) i j := by
  have generated:=congrArg (fun M : Matrix ActualPreparedIndex ActualPreparedIndex ℂ=>M i j)
    (sourceFirstEnergyFour_value epsilon precision p v)
  simpa only [sourceFirstEnergyFour,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry] using generated

/-- The charged full-carrier components have zero restriction here, while the neutral restriction returns the entire actual four-column energy. -/
theorem sourceFirstEnergyGradeRead_generated (g : Fin 3) (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    sourceFirstEnergyGradeRead g epsilon precision p v=
      if g=0 then sourceFirstEnergyFour epsilon precision p v else 0 := by
  ext i j
  simp only [sourceFirstEnergyGradeRead,sourceChargedEnergyRead_entry,sourceFirstEnergyGrade]
  split_ifs <;> simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    ad_entry,actual_charge,literal_entry epsilon precision,sourceFirstEnergyFour_value,
    Matrix.diagonal_apply,Matrix.zero_apply]
  all_goals (by_cases same : i=j <;> simp_all)

/-- The physical moving first-pole energy return is consumed by its source-generated neutral prepared channel, with the actual origin still explicit. -/
theorem sourceFirstPoleNeutral_limit (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (i j : ActualPreparedIndex) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 0 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourceNativeFrequencyPolarization 0 e.val (sourceSheet 0 n unit e.val) n)-
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 0 e.val (sourceSheet 0 n unit e.val) n))/(e.val:ℂ)^2)
      scaleApproach (𝓝 ((softCoefficient 0:ℂ)*sourceFirstEnergyGradeRead 0 epsilon precision p
        (physicalFrequencyMomentum (sourceSpeed 0) n) i j)) := by
  simpa only [sourceFirstEnergyGradeRead_generated,ite_true,sourceFirstEnergyFour_value] using
    sourceFirstPoleEnergy_limit epsilon precision p i j n unit

/-- The original full current and its nonconstant beta cofactor consume the same neutral energy restriction; no Green charge-commutation condition is imposed. -/
theorem sourceFirstPoleNeutral_current (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (i j : ActualPreparedIndex) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 0 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet 0 n unit e.val) n)-
       sourcePhotonLeftReader 0 e.val (sourceSheet 0 n unit e.val) n
         (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)*
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 0 e.val (sourceSheet 0 n unit e.val) n)))
      scaleApproach (𝓝 (sourceCurvatureEmitterInput
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) (residueIndex 0)*
        ((softCoefficient 0:ℂ)*sourceFirstEnergyGradeRead 0 epsilon precision p
          (physicalFrequencyMomentum (sourceSpeed 0) n) i j))) := by
  simpa only [sourceFirstEnergyGradeRead_generated,ite_true,sourceFirstEnergyFour_value] using
    sourceFirstPoleCurrent_energy q sL eL sR eR pL pR lambda T n unit epsilon precision p i j

end LowEnergy.PreparationPhysicalResponseChargeGrading
