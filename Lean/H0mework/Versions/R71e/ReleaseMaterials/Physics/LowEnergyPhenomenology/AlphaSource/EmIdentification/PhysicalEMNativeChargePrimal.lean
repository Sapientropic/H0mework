import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstPoleChargeCubic
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseGaugeGenerator
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceSecondPoleChargeNeutral

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMNativeChargePrimal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePhaseChargeInventory
open PreparationVacuumOriginalGreenFeedback PreparationVacuumLowerClassical
open PreparationVacuumNativeFieldInjection PreparationVacuumRestModeCoupling
open PreparationVacuumPhysicalConstraint114 PreparationCoordinates
open GaussNativeMatter SourceQuantumResidualGaugeSlice SourceQuantumFockGauge SourceQuantumScalarChart
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalResponseChargeGrading
open FullQuantum.CoframeResponse FullQuantum.StateGreen
open Stage10 Stage10.CanonicalMatter DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open Stage9C.Material.SpinPair StageNineHolonomicField
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index := Classical.decEq _

/-- The fixed electromagnetic primal charge on the original full252
carrier: the phase-gauge Lie direction, not a caller generator. -/
def emPrimalCharge : SourceMatrix :=
  Complex.I • nativePrimal sourcePhaseGaugeLie

/-- The retained full252 hypercharge/identity difference between the
original phase charge and the electromagnetic direction. -/
def emPrimalDefect : SourceMatrix :=
  Complex.I • Quantum.operatorMatrix sourcePhaseGaugeDifference

/-- Electromagnetic adjoint with the same sign convention as
`sourceResponsePrimalAd`. -/
def emPrimalAd : SourceMatrix →ₗ[ℂ] SourceMatrix where
  toFun A:=emPrimalCharge*A-A*emPrimalCharge
  map_add' A B:=by simp only [mul_add,add_mul];abel
  map_smul' c A:=by
    simp only [mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

/-- The original phase charge is literally the EM charge plus the
retained defect. -/
theorem em_original_phase_charge_generated :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
      emPrimalCharge+emPrimalDefect :=
  sourceCoframeCharge_nativeDifference

attribute [local irreducible]
  sourcePhaseGaugeLie sourcePhaseGaugeDifference sourcePhaseGaugeGenerator
  sourceHyperchargeMother nativePrimal nativeFull sourceResponsePrimalAd
  sourceFirstEnergyAction sourceFirstGaugeConnection sourceFirstGaugeCoefficients
  principalMatrix coefficientMatrix nativeY
  StageNineP286GaugeAuxiliaryVariation.p286CoordinateLieBracket

/-- The hypercharge block of `p286LieBracket` vanishes and the
`chargeDirection` su3/su2 entries are literally zero, so the hypercharge
direction is central in the original P286 block data. -/
private theorem em_chargeDirection_bracket
    (x : SU7MotherLieAlgebra.P286LieBlockData) :
    SU7MotherGaugeTheory.p286LieBracket
      Stage10.HyperchargeResponse.chargeDirection x=0 := by
  simp [Stage10.HyperchargeResponse.chargeDirection,
    SU7MotherGaugeTheory.p286LieBracket,SU7MotherGaugeTheory.suLieBracket]

private theorem em_nativeY_central (a : NativeLie) :
    StageNineP286GaugeAuxiliaryVariation.p286CoordinateLieBracket nativeY a=0 := by
  unfold StageNineP286GaugeAuxiliaryVariation.p286CoordinateLieBracket nativeY
  rw [p286CoordinateEquiv.symm_apply_apply,em_chargeDirection_bracket,map_zero]

private theorem em_nativePrimal_Y_commute (a : NativeLie) :
    Commute (nativePrimal nativeY) (nativePrimal a) := by
  have commutator:=originalGauge_commutator nativeY a
  change nativePrimal (StageNineP286GaugeAuxiliaryVariation.p286CoordinateLieBracket nativeY a)=
    nativePrimal nativeY*nativePrimal a-nativePrimal a*nativePrimal nativeY at commutator
  rw [em_nativeY_central a,map_zero] at commutator
  exact sub_eq_zero.mp commutator.symm

/-- Dirac spin commutes with every native primal matrix. -/
private theorem em_nativePrimal_spin (a : NativeLie) (A : DiracMatrix) :
    Commute (nativePrimal a) (spinCoordinates A) := by
  have native:=GaussMatterCore.spin_native_commute A a
  rw [←GaussCoframeSpin.spinLift_source] at native
  change spinCoordinates A*nativePrimal a=nativePrimal a*spinCoordinates A at native
  exact native.symm

private theorem em_commute_mul {D A B : SourceMatrix}
    (hA : Commute D A) (hB : Commute D B) : Commute D (A*B) := by
  show D*(A*B)=(A*B)*D
  calc D*(A*B)=(D*A)*B:=by rw [←mul_assoc]
    _=(A*D)*B:=by rw [hA.eq]
    _=A*(D*B):=by rw [mul_assoc]
    _=A*(B*D):=by rw [hB.eq]
    _=(A*B)*D:=by rw [←mul_assoc]

private theorem em_commute_sub_left {A B Z : SourceMatrix}
    (hA : Commute A Z) (hB : Commute B Z) : Commute (A-B) Z := by
  show (A-B)*Z=Z*(A-B)
  rw [sub_mul,mul_sub,hA.eq,hB.eq]

private theorem em_commute_sub_right {A B Z : SourceMatrix}
    (hA : Commute Z A) (hB : Commute Z B) : Commute Z (A-B) := by
  show Z*(A-B)=(A-B)*Z
  rw [mul_sub,sub_mul,hA.eq,hB.eq]

private theorem em_commute_add_right {A B Z : SourceMatrix}
    (hA : Commute Z A) (hB : Commute Z B) : Commute Z (A+B) := by
  show Z*(A+B)=(A+B)*Z
  rw [mul_add,add_mul,hA.eq,hB.eq]

private theorem em_commute_neg_left {A Z : SourceMatrix}
    (h : Commute A Z) : Commute (-A) Z := by
  show (-A)*Z=Z*(-A)
  rw [neg_mul,mul_neg,h.eq]

private theorem em_commute_smul_left {A Z : SourceMatrix} (h : Commute A Z) (c : ℂ) :
    Commute (c•A) Z := by
  show (c•A)*Z=Z*(c•A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem em_commute_smul_left_real {A Z : SourceMatrix} (h : Commute A Z) (r : ℝ) :
    Commute (r•A) Z := by
  show (r•A)*Z=Z*(r•A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem em_commute_smul_right {A Z : SourceMatrix} (h : Commute A Z) (c : ℂ) :
    Commute A (c•Z) := by
  show A*(c•Z)=(c•Z)*A
  rw [mul_smul_comm,smul_mul_assoc,h.eq]

private theorem em_commute_sum {D : SourceMatrix} {ι : Type*} [Fintype ι]
    {f : ι → SourceMatrix} (h : ∀ i, Commute D (f i)) :
    Commute D (∑i : ι,f i) := by
  show D*(∑i,f i)=(∑i,f i)*D
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact (h i).eq

/-- The native phase-gauge Lie direction decomposes as
`-colorGenerator2-(1/2)*nativeY`, so its primal matrix commutes with
anything commuting with both summands. -/
private theorem em_nativePrimal_lie_commutes {Z : SourceMatrix}
    (hc : Commute (nativePrimal (SourceQuantumResidualGaugeSlice.colorGenerator 2)) Z)
    (hY : Commute (nativePrimal nativeY) Z) :
    Commute (nativePrimal sourcePhaseGaugeLie) Z := by
  unfold sourcePhaseGaugeLie
  simp only [map_neg,map_sub,map_smul]
  exact em_commute_sub_left (em_commute_neg_left hc)
    (em_commute_smul_left_real hY (1/2:ℝ))

private theorem em_nativePrimal_lie_spin (A : DiracMatrix) :
    Commute (nativePrimal sourcePhaseGaugeLie) (spinCoordinates A) :=
  em_nativePrimal_lie_commutes (em_nativePrimal_spin _ A) (em_nativePrimal_spin _ A)

/-- Local public read formula for `nativePrimal`: the private
`nativeRead` inside is the normed `NativeLie` wrapper's identity into
`P286CoordinateCarrier`, so it is name-free by `rfl`. -/
private theorem em_nativePrimal_generated (a : NativeLie) :
    nativePrimal a=
      Quantum.operatorMatrix (diracExteriorMotherLieAction
        (SU7MotherLieAlgebra.p286LieBlockEmbed
          (StageNineHolonomicField.p286CoordinateEquiv.symm
            (show StageNineHolonomicField.P286CoordinateCarrier from a)))) := by
  unfold nativePrimal
  rfl

/-- The normed read of `nativeY` is the original hypercharge direction's
P286 coordinates. -/
private theorem em_nativeY_read :
    (show StageNineHolonomicField.P286CoordinateCarrier from nativeY)=
      p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection := by
  unfold nativeY
  rfl

private theorem em_hypercharge_native :
    Quantum.operatorMatrix sourceHyperchargeMother=nativePrimal nativeY := by
  unfold sourceHyperchargeMother
  rw [em_nativePrimal_generated nativeY,em_nativeY_read,
    p286CoordinateEquiv.symm_apply_apply]

private theorem em_operator_smul (c : ℂ) (A : Mother) :
    Quantum.operatorMatrix (c • A)=c • Quantum.operatorMatrix A :=
  Quantum.operatorMatrix.toLinearEquiv.map_smul c A

private theorem em_operator_sub (A B : Mother) :
    Quantum.operatorMatrix (A-B)=Quantum.operatorMatrix A-Quantum.operatorMatrix B := by
  ext i j
  simp only [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.sub_apply,map_sub,Finsupp.sub_apply,Matrix.sub_apply]

private theorem em_operator_one :
    Quantum.operatorMatrix (1 : Mother)=(1 : SourceMatrix) :=
  map_one Quantum.operatorMatrix

/-- The defect decomposes as `(I/2)*(natP Y - I*1)` on the full252
carrier, so its commutation reduces to nativeY centrality. -/
private theorem em_defect_decomposed :
    emPrimalDefect=
      (Complex.I/2) • (nativePrimal nativeY-Complex.I • (1:SourceMatrix)) := by
  unfold emPrimalDefect sourcePhaseGaugeDifference
  rw [em_operator_smul,em_operator_sub,em_hypercharge_native,
    em_operator_smul,em_operator_one]
  rw [smul_smul]
  congr 1
  ring

/-- Every matrix commuting with `nativePrimal nativeY` commutes with the
retained defect, since `I*1` is central. -/
private theorem em_defect_commutes_of {Z : SourceMatrix}
    (hY : Commute (nativePrimal nativeY) Z) : Commute emPrimalDefect Z := by
  rw [em_defect_decomposed]
  apply em_commute_smul_left
  apply em_commute_sub_left hY
  apply em_commute_smul_left
  exact Commute.one_left Z

/-- The retained defect commutes with the electromagnetic charge. -/
theorem em_native_charge_defect_commutes : Commute emPrimalDefect emPrimalCharge := by
  apply em_defect_commutes_of
  apply em_commute_smul_right
  exact em_nativePrimal_Y_commute sourcePhaseGaugeLie

/-- The retained defect commutes with each actual first-energy axis on
the original full252 carrier. -/
theorem em_native_first_defect_commutes (k : Fin 4) :
    Commute emPrimalDefect (Quantum.operatorMatrix (sourceFirstEnergyAction k)) := by
  apply em_defect_commutes_of
  rw [sourceFirstEnergyAction_matrix k]
  apply em_commute_smul_right
  apply em_commute_mul
  · rw [principal_inverse_original _ (FullQuantum.actual_noncharacteristic 0),actual_coframe,
      InducedQuantum.lapse_temporal_inverse lapse lapse_pos.ne',
      em_operator_smul]
    apply em_commute_smul_right
    change Commute (nativePrimal nativeY) (spinCoordinates diracGammaZero)
    exact em_nativePrimal_spin nativeY diracGammaZero
  · apply em_commute_sum
    intro mu
    apply em_commute_mul
    · unfold coefficientMatrix
      apply em_commute_smul_right
      exact em_nativePrimal_spin nativeY _
    · exact em_nativePrimal_Y_commute (sourceFirstGaugeConnection k mu)

private theorem em_ad_eq_response {A : SourceMatrix} (h : Commute emPrimalDefect A) :
    emPrimalAd A=sourceResponsePrimalAd A := by
  have unfold_ad : emPrimalAd A=emPrimalCharge*A-A*emPrimalCharge := rfl
  have unfold_resp : sourceResponsePrimalAd A=
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*A-
      A*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether) := by
    unfold sourceResponsePrimalAd
    rfl
  rw [unfold_ad,unfold_resp,em_original_phase_charge_generated,add_mul,mul_add,h.eq]
  noncomm_ring

private theorem em_commute_defect_response {A : SourceMatrix}
    (h : Commute emPrimalDefect A) :
    Commute emPrimalDefect (sourceResponsePrimalAd A) := by
  have hQ : Commute emPrimalDefect
      (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)) := by
    rw [em_original_phase_charge_generated]
    exact em_commute_add_right em_native_charge_defect_commutes (Commute.refl _)
  have unfold_resp : sourceResponsePrimalAd A=
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*A-
      A*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether) := by
    unfold sourceResponsePrimalAd
    rfl
  rw [unfold_resp]
  exact em_commute_sub_right (em_commute_mul hQ h) (em_commute_mul h hQ)

/-- EM adjoint equals the original phase adjoint on each actual
first-energy axis; the defect commutation is the only input. -/
theorem em_native_first_ad_source (k : Fin 4) :
    emPrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k))=
      sourceResponsePrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k)) :=
  em_ad_eq_response (em_native_first_defect_commutes k)

/-- The EM charge degree on each actual first-energy axis satisfies
`Ad^3=Ad`, so every axis lies in the `{0,+1,-1}` degree span. -/
theorem em_native_first_charge_cube (k : Fin 4) :
    emPrimalAd (emPrimalAd (emPrimalAd
      (Quantum.operatorMatrix (sourceFirstEnergyAction k))))=
        emPrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k)) := by
  have hA := em_native_first_defect_commutes k
  have h1 := em_ad_eq_response hA
  have hR := em_commute_defect_response hA
  have h2 := em_ad_eq_response hR
  have hRR := em_commute_defect_response hR
  have h3 := em_ad_eq_response hRR
  calc emPrimalAd (emPrimalAd (emPrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k))))
      =emPrimalAd (emPrimalAd (sourceResponsePrimalAd
        (Quantum.operatorMatrix (sourceFirstEnergyAction k)))) :=
        congrArg emPrimalAd (congrArg emPrimalAd h1)
    _ =emPrimalAd (sourceResponsePrimalAd (sourceResponsePrimalAd
        (Quantum.operatorMatrix (sourceFirstEnergyAction k)))) :=
        congrArg emPrimalAd h2
    _ =sourceResponsePrimalAd (sourceResponsePrimalAd (sourceResponsePrimalAd
        (Quantum.operatorMatrix (sourceFirstEnergyAction k)))) := h3
    _ =sourceResponsePrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k)) :=
        sourceFirstEnergyPrimal_chargeCube k
    _ =emPrimalAd (Quantum.operatorMatrix (sourceFirstEnergyAction k)) := h1.symm

/-- Linear extension of the charge cube to the actual weighted source
energy sum, keeping every mode term at its literal source weight. -/
theorem em_native_first_charge_cube_weighted (v : Fin 4→ℂ) :
    emPrimalAd (emPrimalAd (emPrimalAd
      (∑k : Fin 4,v k • Quantum.operatorMatrix (sourceFirstEnergyAction k))))=
        emPrimalAd (∑k : Fin 4,v k • Quantum.operatorMatrix (sourceFirstEnergyAction k)) := by
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [em_native_first_charge_cube k]

/-- Source-generated neutral piece of a mode under the EM grading. -/
def emEmNeutral (A : SourceMatrix) : SourceMatrix :=
  A-emPrimalAd (emPrimalAd A)

/-- Source-generated charge `+1` piece of a mode under the EM grading. -/
def emEmPlus (A : SourceMatrix) : SourceMatrix :=
  (1/2:ℂ) • (emPrimalAd (emPrimalAd A)+emPrimalAd A)

/-- Source-generated charge `-1` piece of a mode under the EM grading. -/
def emEmMinus (A : SourceMatrix) : SourceMatrix :=
  (1/2:ℂ) • (emPrimalAd (emPrimalAd A)-emPrimalAd A)

/-- The three generated pieces rebuild the whole mode. -/
theorem emEmPieces_sum (A : SourceMatrix) :
    emEmNeutral A+emEmPlus A+emEmMinus A=A := by
  unfold emEmNeutral emEmPlus emEmMinus
  module

theorem emEmNeutral_eigen {A : SourceMatrix}
    (hcube : emPrimalAd (emPrimalAd (emPrimalAd A))=emPrimalAd A) :
    emPrimalAd (emEmNeutral A)=0 := by
  unfold emEmNeutral
  rw [map_sub,hcube]
  exact sub_self _

theorem emEmPlus_eigen {A : SourceMatrix}
    (hcube : emPrimalAd (emPrimalAd (emPrimalAd A))=emPrimalAd A) :
    emPrimalAd (emEmPlus A)=emEmPlus A := by
  unfold emEmPlus
  rw [map_smul,map_add,hcube]
  module

theorem emEmMinus_eigen {A : SourceMatrix}
    (hcube : emPrimalAd (emPrimalAd (emPrimalAd A))=emPrimalAd A) :
    emPrimalAd (emEmMinus A)=-emEmMinus A := by
  unfold emEmMinus
  rw [map_smul,map_sub,hcube]
  module

/-- Every first-energy mode has the generated neutral/`+1`/`-1`
eigen-decomposition under the EM charge, all mode terms retained. -/
theorem em_native_first_mode_decomposed (k : Fin 4) :
    emEmNeutral (Quantum.operatorMatrix (sourceFirstEnergyAction k))+
      emEmPlus (Quantum.operatorMatrix (sourceFirstEnergyAction k))+
      emEmMinus (Quantum.operatorMatrix (sourceFirstEnergyAction k))=
        Quantum.operatorMatrix (sourceFirstEnergyAction k) :=
  emEmPieces_sum _

theorem em_native_first_neutral_eigen (k : Fin 4) :
    emPrimalAd (emEmNeutral (Quantum.operatorMatrix (sourceFirstEnergyAction k)))=0 :=
  emEmNeutral_eigen (em_native_first_charge_cube k)

theorem em_native_first_plus_eigen (k : Fin 4) :
    emPrimalAd (emEmPlus (Quantum.operatorMatrix (sourceFirstEnergyAction k)))=
      emEmPlus (Quantum.operatorMatrix (sourceFirstEnergyAction k)) :=
  emEmPlus_eigen (em_native_first_charge_cube k)

theorem em_native_first_minus_eigen (k : Fin 4) :
    emPrimalAd (emEmMinus (Quantum.operatorMatrix (sourceFirstEnergyAction k)))=
      -emEmMinus (Quantum.operatorMatrix (sourceFirstEnergyAction k)) :=
  emEmMinus_eigen (em_native_first_charge_cube k)

end LowEnergy.GaussComposite.PhysicalEMNativeChargePrimal
