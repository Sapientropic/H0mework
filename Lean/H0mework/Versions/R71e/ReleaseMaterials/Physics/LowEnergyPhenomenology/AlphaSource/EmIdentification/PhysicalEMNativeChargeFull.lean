import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMNativeChargePrimal

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMNativeChargeFull
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussNativeMatter CanonicalGradedCharge SourceQuantumConfigurationHilbert
open PreparationVacuumActualFieldQuantization CanonicalGradedSpatialSource
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalFirstPoleGaugeVertex
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalNormalizedFullField
open PreparationVacuumPhysicalFeedback PreparationVacuumSourceFieldFamily
open PreparationPhysicalResponseChargeGrading
open GaussComposite.PhysicalEMNativeChargePrimal
open FullQuantum.StateGreen
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index := Classical.decEq _

def emFullCharge : FullMatrix := chargeMatrix sourcePhaseGaugeLie

def emFullAd : FullMatrix →ₗ[ℂ] FullMatrix where
  toFun A:=emFullCharge*A-A*emFullCharge
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by
    simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def emDualPlus (A : SourceMatrix) : FullMatrix :=
  Matrix.fromBlocks A 0 0 (A.map (starRingEnd ℂ))

private theorem em_conj_two : (starRingEnd ℂ) (2 : ℂ)=(2 : ℂ) := by
  change star (2 : ℂ)=(2 : ℂ)
  norm_num
attribute [local simp] em_conj_two

/-- Native Lie action has a positive conjugate dual block; its Hermitian
charge therefore has the opposite dual charge. -/
theorem em_full_charge_generated :
    emFullCharge=Matrix.fromBlocks emPrimalCharge 0 0
      (-(emPrimalCharge.map (starRingEnd ℂ))) := by
  unfold emFullCharge chargeMatrix nativeFull emPrimalCharge
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.map_apply,Complex.conj_I]

attribute [local irreducible] emPrimalCharge emPrimalAd
  sourcePhaseGaugeLie sourceFirstEnergyAction emFullCharge emFullAd

private theorem em_full_ad_branches (A : SourceMatrix) :
    emFullAd (SourceRealScalarFock.branches A)=emDualPlus (emPrimalAd A) := by
  unfold emFullAd
  change emFullCharge*SourceRealScalarFock.branches A-
    SourceRealScalarFock.branches A*emFullCharge=_
  rw [em_full_charge_generated]
  unfold SourceRealScalarFock.branches emDualPlus
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,
    neg_mul_neg]
  have original : emPrimalAd A=emPrimalCharge*A-A*emPrimalCharge := by
    unfold emPrimalAd
    rfl
  rw [original]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.map_sub]

private theorem em_full_ad_plus (A : SourceMatrix) :
    emFullAd (emDualPlus A)=SourceRealScalarFock.branches (emPrimalAd A) := by
  unfold emFullAd
  change emFullCharge*emDualPlus A-emDualPlus A*emFullCharge=_
  rw [em_full_charge_generated]
  unfold SourceRealScalarFock.branches emDualPlus
  simp only [Matrix.fromBlocks_multiply,zero_mul,mul_zero,add_zero,zero_add,
    neg_mul,mul_neg]
  have original : emPrimalAd A=emPrimalCharge*A-A*emPrimalCharge := by
    unfold emPrimalAd
    rfl
  rw [original]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.map_sub,neg_sub]
  all_goals abel

theorem em_native_first_full_cube (k : Fin 4) :
    emFullAd (emFullAd (emFullAd
      (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k)))))=
      emFullAd (SourceRealScalarFock.branches
        (Quantum.operatorMatrix (sourceFirstEnergyAction k))) := by
  simp only [em_full_ad_branches,em_full_ad_plus,em_native_first_charge_cube]

theorem em_native_first_literal_full_cube
    (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    emFullAd (emFullAd (emFullAd
      (sourceLiteralEnergyWeight p
        (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val) v 1)))=
      emFullAd (sourceLiteralEnergyWeight p
        (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val) v 1) := by
  rw [sourceFirstLiteralEnergy_generated]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun A : FullMatrix=>v k • A) (em_native_first_full_cube k)

def emFullNeutral (A : FullMatrix) : FullMatrix :=
  A-emFullAd (emFullAd A)

def emFullPlus (A : FullMatrix) : FullMatrix :=
  (1/2:ℂ) • (emFullAd (emFullAd A)+emFullAd A)

def emFullMinus (A : FullMatrix) : FullMatrix :=
  (1/2:ℂ) • (emFullAd (emFullAd A)-emFullAd A)

theorem em_full_pieces_sum (A : FullMatrix) :
    emFullNeutral A+emFullPlus A+emFullMinus A=A := by
  unfold emFullNeutral emFullPlus emFullMinus
  module

private theorem em_full_neutral_eigen {A : FullMatrix}
    (cube : emFullAd (emFullAd (emFullAd A))=emFullAd A) :
    emFullAd (emFullNeutral A)=0 := by
  unfold emFullNeutral
  rw [map_sub,cube,sub_self]

private theorem em_full_plus_eigen {A : FullMatrix}
    (cube : emFullAd (emFullAd (emFullAd A))=emFullAd A) :
    emFullAd (emFullPlus A)=emFullPlus A := by
  unfold emFullPlus
  rw [map_smul,map_add,cube]
  module

private theorem em_full_minus_eigen {A : FullMatrix}
    (cube : emFullAd (emFullAd (emFullAd A))=emFullAd A) :
    emFullAd (emFullMinus A)=-emFullMinus A := by
  unfold emFullMinus
  rw [map_smul,map_sub,cube]
  module

/-- The independent dual exchanges the positive and negative primal
sectors; it is not a multiplicative `branches` transport. -/
theorem em_full_plus_blocks (A : SourceMatrix) :
    emFullPlus (SourceRealScalarFock.branches A)=
      Matrix.fromBlocks (emEmPlus A) 0 0 (-(emEmMinus A).map (starRingEnd ℂ)) := by
  unfold emFullPlus
  simp only [em_full_ad_branches,em_full_ad_plus]
  unfold SourceRealScalarFock.branches emDualPlus emEmPlus emEmMinus
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks]
  all_goals ring

theorem em_full_minus_blocks (A : SourceMatrix) :
    emFullMinus (SourceRealScalarFock.branches A)=
      Matrix.fromBlocks (emEmMinus A) 0 0 (-(emEmPlus A).map (starRingEnd ℂ)) := by
  unfold emFullMinus
  simp only [em_full_ad_branches,em_full_ad_plus]
  unfold SourceRealScalarFock.branches emDualPlus emEmPlus emEmMinus
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks]
  all_goals ring

theorem em_native_first_full_eigen (k : Fin 4) :
    emFullAd (emFullNeutral
      (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))))=0 ∧
    emFullAd (emFullPlus
      (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))))=
      emFullPlus (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))) ∧
    emFullAd (emFullMinus
      (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))))=
      -emFullMinus (SourceRealScalarFock.branches (Quantum.operatorMatrix (sourceFirstEnergyAction k))) :=
  ⟨em_full_neutral_eigen (em_native_first_full_cube k),
    em_full_plus_eigen (em_native_first_full_cube k),
    em_full_minus_eigen (em_native_first_full_cube k)⟩

theorem em_native_spin_full_neutral (A : DiracCliffordRepresentation.DiracMatrix) :
    emFullAd (SourceRealScalarFock.branches
      (FullQuantum.CoframeResponse.spinCoordinates A))=0 := by
  have original:=GaussMatterCore.spin_native_commute A sourcePhaseGaugeLie
  rw [←GaussCoframeSpin.spinLift_source] at original
  change FullQuantum.CoframeResponse.spinCoordinates A*nativePrimal sourcePhaseGaugeLie=
    nativePrimal sourcePhaseGaugeLie*FullQuantum.CoframeResponse.spinCoordinates A at original
  have primal : emPrimalAd (FullQuantum.CoframeResponse.spinCoordinates A)=0 := by
    unfold emPrimalAd emPrimalCharge
    change (Complex.I • nativePrimal sourcePhaseGaugeLie)*
        FullQuantum.CoframeResponse.spinCoordinates A-
      FullQuantum.CoframeResponse.spinCoordinates A*
        (Complex.I • nativePrimal sourcePhaseGaugeLie)=0
    rw [smul_mul_assoc,mul_smul_comm,original,sub_self]
  rw [em_full_ad_branches,primal]
  simp [emDualPlus]

theorem em_native_second_literal_full_neutral
    (p : PhysicalMomentum) (v : Fin 4→ℂ) :
    emFullAd (sourceLiteralEnergyWeight p
      (PreparationVacuumSourceFieldFamily.sourceState GaussHistoryHilbert.sourcePoint.val) v 2)=0 := by
  rw [sourceLiteralChannelTwoEnergy]
  simp only [map_sum,map_smul,em_native_spin_full_neutral,smul_zero,Finset.sum_const_zero]

end LowEnergy.GaussComposite.PhysicalEMNativeChargeFull
