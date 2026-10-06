import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaSpinRelativeForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaSpinClosure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralScalarCurrent
open SourceInverseMagneticForceCancellation SourceInverseCoframeNeutralSplice
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent GaussYukawaCoefficient
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum StageNineDiracDualYukawaSpinJurisdiction
open SourceInverseHamiltonianForceReduction SourceScalarPairedTransport SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceScalarForceBudget SourceJointScaleBudget
open scoped ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.InternalIndex := Classical.decEq _
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
open SourceInverseNeutralSpinCurrent SourceClockYukawaSpinRelativeForm SourcePhysicalKineticSquare SourceClockReflectedForm
attribute [local irreducible] SourceMixedNativeReturn.fullAction

private theorem even_commute {R : Type*} [Ring R] (G A B : R)
    (hA : G*A+A*G=0) (hB : G*B+B*G=0) : Commute (A*B) G := by
  change A*B*G=G*(A*B)
  linear_combination (norm := noncomm_ring) A*hB-hA*B

private theorem boost_anti {R : Type*} [Ring R] (A B : R) (h : A*B+B*A=0) :
    A*B*A+A*(A*B)=0 := by
  linear_combination (norm := noncomm_ring) A*h

private theorem boost_square {R : Type*} [Ring R] (A B : R)
    (ha : A*A= -1) (hb : B*B=1) (h : A*B+B*A=0) : (A*B)*(A*B)=1 := by
  linear_combination (norm := noncomm_ring) A*h*B-ha*(B*B)+hb

private theorem active_anti_gamma (j : Fin 4) :
    GaussCoframeSpin.sourceSpin (activeIndex j)*diracGammaZero+
      diracGammaZero*GaussCoframeSpin.sourceSpin (activeIndex j)=0 := by
  fin_cases j
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaOne))*diracGammaZero+
      diracGammaZero*((1/2 : ℂ) • (diracGammaZero*diracGammaOne))=0
    simp only [smul_mul_assoc,mul_smul_comm,←smul_add,boost_anti _ _ diracGammaZeroOne_anticommute,smul_zero]
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaTwo))*diracGammaZero+
      diracGammaZero*((1/2 : ℂ) • (diracGammaZero*diracGammaTwo))=0
    simp only [smul_mul_assoc,mul_smul_comm,←smul_add,boost_anti _ _ diracGammaZeroTwo_anticommute,smul_zero]
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaThree))*diracGammaZero+
      diracGammaZero*((1/2 : ℂ) • (diracGammaZero*diracGammaThree))=0
    simp only [smul_mul_assoc,mul_smul_comm,←smul_add,boost_anti _ _ diracGammaZeroThree_anticommute,smul_zero]
  · change ((-1/2 : ℂ) • diracGammaFive)*diracGammaZero+diracGammaZero*((-1/2 : ℂ) • diracGammaFive)=0
    have h5 : diracGammaFive*diracGammaZero+diracGammaZero*diracGammaFive=0 := diracGammaFive_anticommutes 0
    simp only [smul_mul_assoc,mul_smul_comm,←smul_add,h5,smul_zero]

private theorem active_chiral (j : Fin 4) :
    Commute (GaussCoframeSpin.sourceSpin (activeIndex j)) rightChiralityProjector := by
  have h0 := diracGammaFive_anticommutes 0
  have h1 := even_commute _ _ _ h0 (diracGammaFive_anticommutes 1)
  have h2 := even_commute _ _ _ h0 (diracGammaFive_anticommutes 2)
  have h3 := even_commute _ _ _ h0 (diracGammaFive_anticommutes 3)
  have hx : Commute (GaussCoframeSpin.sourceSpin (activeIndex j)) diracGammaFive := by
    fin_cases j
    · exact h1.smul_left (1/2 : ℂ)
    · exact h2.smul_left (1/2 : ℂ)
    · exact h3.smul_left (1/2 : ℂ)
    · exact (Commute.refl _).smul_left (-1/2 : ℂ)
  unfold rightChiralityProjector
  exact ((Commute.one_right _).add_right hx).smul_right _

private def diracMap : DiracMatrix →ₗ[ℂ] Module.End ℂ DiracExteriorMatterCarrier where
  toFun := diracMatrixMatterAction
  map_add' A B := by
    apply LinearMap.ext
    intro f
    funext i
    change (∑ j,(A i j+B i j) • f j)=(∑ j,A i j • f j)+(∑ j,B i j • f j)
    simp only [add_smul,Finset.sum_add_distrib]
  map_smul' c A := by
    apply LinearMap.ext
    intro f
    funext i
    change (∑ j,(c*A i j) • f j)=c • (∑ j,A i j • f j)
    simp only [mul_smul,Finset.smul_sum]

private theorem dirac_map_mul (A B : DiracMatrix) : diracMap (A*B)=diracMap A*diracMap B :=
  diracMatrixMatterAction_mul A B

private theorem dirac_map_one : diracMap 1=(1 : Module.End ℂ DiracExteriorMatterCarrier) := by
  apply LinearMap.ext
  intro f
  funext i
  change (∑ j,(1 : DiracMatrix) i j • f j)=f i
  simp [Matrix.one_apply]

private theorem anti_product {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (S D I P : R) (c : ℂ) (hd : S*D+D*S=0) (hi : Commute S I) (hp : Commute S P) :
    S*(c • (D*(I*P)))+(c • (D*(I*P)))*S=0 := by
  simp only [mul_smul_comm,smul_mul_assoc,←smul_add]
  have h : S*(D*(I*P))+(D*(I*P))*S=0 := by
    linear_combination (norm := noncomm_ring) hd*(I*P)-D*hi.eq*P-D*I*hp.eq
  rw [h,smul_zero]

private theorem active_yukawa_anti (j : Fin 4) (phi : ExteriorBreakingScalarCarrier) :
    diracMap (GaussCoframeSpin.sourceSpin (activeIndex j))*LowEnergy.FullQuantum.yukawaHamiltonian phi+
      LowEnergy.FullQuantum.yukawaHamiltonian phi*diracMap (GaussCoframeSpin.sourceSpin (activeIndex j))=0 := by
  have hd := congrArg diracMap (active_anti_gamma j)
  simp only [map_add,dirac_map_mul,map_zero] at hd
  have hc := congrArg diracMap (active_chiral j).eq
  simp only [dirac_map_mul] at hc
  have hi : Commute (diracMap (GaussCoframeSpin.sourceSpin (activeIndex j)))
      (diracExteriorYukawaInternalAction phi) :=
    diracMatrixMatterAction_commutes_internal _ (exteriorYukawaInternalAction phi)
  unfold LowEnergy.FullQuantum.yukawaHamiltonian diracDualRightChiralYukawaAction
  exact anti_product (R := Module.End ℂ DiracExteriorMatterCarrier) _ _ _ _ _ hd hi hc

private theorem primal_anti (j : Fin 4) (phi : Scalar) :
    GaussCoframeSpin.primal (activeIndex j)*GaussYukawaCoefficient.primal phi+
      GaussYukawaCoefficient.primal phi*GaussCoframeSpin.primal (activeIndex j)=0 := by
  have h := congrArg LowEnergy.Quantum.operatorMatrix (active_yukawa_anti j (scalarCoordinateEquiv.symm phi))
  have he (A : DiracMatrix) : LowEnergy.Quantum.operatorMatrix (diracMap A)=GaussCoframeSpin.spinLift A :=
    GaussCoframeSpin.spinLift_source A
  change GaussCoframeSpin.spinLift (GaussCoframeSpin.sourceSpin (activeIndex j))*
    LowEnergy.Quantum.operatorMatrix (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))+
    LowEnergy.Quantum.operatorMatrix (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))*
      GaussCoframeSpin.spinLift (GaussCoframeSpin.sourceSpin (activeIndex j))=0
  simpa only [map_add,map_mul,map_zero,he] using h

private theorem boost_cross {R : Type*} [Ring R] (A B C : R)
    (hB : A*B+B*A=0) (hC : A*C+C*A=0) (hBC : B*C+C*B=0) :
    (A*B)*(A*C)+(A*C)*(A*B)=0 := by
  linear_combination (norm := noncomm_ring) A*hB*C+A*hC*B-(A*A)*hBC
private theorem scaled_anti {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (A B : R) (c : ℂ) (h : A*B+B*A=0) : (c • A)*(c • B)+(c • B)*(c • A)=0 := by
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,←smul_add,h,smul_zero]

private theorem boost_source_anti (j k : Fin 3) (hjk : j≠k) :
    GaussCoframeSpin.sourceSpin ⟨j.val,by omega⟩*GaussCoframeSpin.sourceSpin ⟨k.val,by omega⟩+
      GaussCoframeSpin.sourceSpin ⟨k.val,by omega⟩*GaussCoframeSpin.sourceSpin ⟨j.val,by omega⟩=0 := by
  have h01 := scaled_anti _ _ (1/2:ℂ) (boost_cross _ _ _ diracGammaZeroOne_anticommute diracGammaZeroTwo_anticommute diracGammaOneTwo_anticommute)
  have h02 := scaled_anti _ _ (1/2:ℂ) (boost_cross _ _ _ diracGammaZeroOne_anticommute diracGammaZeroThree_anticommute diracGammaOneThree_anticommute)
  have h12 := scaled_anti _ _ (1/2:ℂ) (boost_cross _ _ _ diracGammaZeroTwo_anticommute diracGammaZeroThree_anticommute diracGammaTwoThree_anticommute)
  fin_cases j <;> fin_cases k <;> try contradiction
  · exact h01
  · exact h02
  · exact (add_comm _ _).trans h01
  · exact h12
  · exact (add_comm _ _).trans h02
  · exact (add_comm _ _).trans h12

private theorem boost_chiral_source (j : Fin 3) :
    Commute (GaussCoframeSpin.sourceSpin ⟨j.val,by omega⟩) (GaussCoframeSpin.sourceSpin 6) := by
  have hg : Commute (GaussCoframeSpin.sourceSpin ⟨j.val,by omega⟩) diracGammaFive := by
    have h0 := diracGammaFive_anticommutes 0
    fin_cases j
    · exact (even_commute _ _ _ h0 (diracGammaFive_anticommutes 1)).smul_left (1/2:ℂ)
    · exact (even_commute _ _ _ h0 (diracGammaFive_anticommutes 2)).smul_left (1/2:ℂ)
    · exact (even_commute _ _ _ h0 (diracGammaFive_anticommutes 3)).smul_left (1/2:ℂ)
  exact hg.smul_right (-1/2:ℂ)

private theorem lift_mul (A B : DiracMatrix) : GaussCoframeSpin.spinLift (A*B)=
    GaussCoframeSpin.spinLift A*GaussCoframeSpin.spinLift B := by
  have h := congrArg LowEnergy.Quantum.operatorMatrix (dirac_map_mul A B)
  have he (X : DiracMatrix) : LowEnergy.Quantum.operatorMatrix (diracMap X)=GaussCoframeSpin.spinLift X :=
    GaussCoframeSpin.spinLift_source X
  simpa only [map_mul,he] using h


private abbrev boost (j : Fin 3) : Fin 4 := ⟨j.val,by omega⟩
private abbrev S (j : Fin 4) : Matrix Mode Mode ℂ := GaussCoframeSpin.full (activeIndex j)
private theorem lift_anti (A B : DiracMatrix) (h : A*B+B*A=0) :
    GaussCoframeSpin.spinLift A*GaussCoframeSpin.spinLift B+
      GaussCoframeSpin.spinLift B*GaussCoframeSpin.spinLift A=0 := by
  rw [←lift_mul,←lift_mul]
  ext i j
  change (if i.2=j.2 then (A*B) i.1 j.1 else 0)+(if i.2=j.2 then (B*A) i.1 j.1 else 0)=0
  by_cases hij : i.2=j.2
  · simpa only [hij,ite_true,Matrix.add_apply,Matrix.zero_apply] using congrFun (congrFun h i.1) j.1
  · simp only [hij,ite_false,add_zero]

private theorem block_anti {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℂ) :
    Matrix.fromBlocks A 0 0 C*Matrix.fromBlocks B 0 0 D+
      Matrix.fromBlocks B 0 0 D*Matrix.fromBlocks A 0 0 C=
      Matrix.fromBlocks (A*B+B*A) 0 0 (C*D+D*C) := by
  simp only [Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,
    Matrix.fromBlocks_add]

private theorem full_anti (j : Fin 4) (phi : Scalar) : S j*fullMatrix phi+fullMatrix phi*S j=0 := by
  have hp := primal_anti j phi
  have hd := congrArg ((starRingEnd ℂ).mapMatrix : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ →+* _) hp
  simp only [map_add,map_mul,map_zero] at hd
  change (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)+
    (GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)=0 at hd
  change GaussCoframeSpin.full (activeIndex j)*
    Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))+
    Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))*
      GaussCoframeSpin.full (activeIndex j)=0
  unfold GaussCoframeSpin.full
  split_ifs
  · rw [block_anti,hp]
    have hz : (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*
        (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))+
        (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))*
          (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)=0 := by
      linear_combination (norm := noncomm_ring) -hd
    rw [hz]
    ext i k;cases i <;> cases k <;> rfl
  · rw [block_anti,hp]
    have hz : (-(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))*
        (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))+
        (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))*
          (-(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))=0 := by
      linear_combination (norm := noncomm_ring) hd
    rw [hz]
    ext i k;cases i <;> cases k <;> rfl

private theorem branch_anti (j : Fin 4) (sharp : Bool) (phi : Scalar) :
    S j*branchMatrix sharp phi+branchMatrix sharp phi*S j=0 := by
  cases sharp
  · exact full_anti j phi
  · have h := congrArg Matrix.conjTranspose (full_anti j phi)
    have hs : (S j).conjTranspose=S j := GaussCoframeSpin.full_hermitian _
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,hs,Matrix.conjTranspose_zero] at h
    change S j*(fullMatrix phi).conjTranspose+(fullMatrix phi).conjTranspose*S j=0
    rw [add_comm]
    exact h

private theorem boost_pair_anti (j k : Fin 3) (hjk : j≠k) : S (boost j)*S (boost k)+S (boost k)*S (boost j)=0 := by
  have hactive (i : Fin 3) : activeIndex (boost i)=⟨i.val,by omega⟩ := by simp [activeIndex,i.isLt]
  have hp : GaussCoframeSpin.primal (activeIndex (boost j))*GaussCoframeSpin.primal (activeIndex (boost k))+
      GaussCoframeSpin.primal (activeIndex (boost k))*GaussCoframeSpin.primal (activeIndex (boost j))=0 := by
    simp only [GaussCoframeSpin.primal,hactive]
    exact lift_anti _ _ (boost_source_anti j k hjk)
  have hd := congrArg ((starRingEnd ℂ).mapMatrix : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ →+* _) hp
  simp only [map_add,map_mul,map_zero] at hd
  change (GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex (boost k))).map (starRingEnd ℂ)+
    (GaussCoframeSpin.primal (activeIndex (boost k))).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ)=0 at hd
  have hj : (activeIndex (boost j)).val<3 := by simp [activeIndex,j.isLt]
  have hk : (activeIndex (boost k)).val<3 := by simp [activeIndex,k.isLt]
  simp only [S,GaussCoframeSpin.full,hj,hk,ite_true]
  rw [block_anti,hp,hd]
  ext i l;cases i <;> cases l <;> rfl

private theorem boost_chiral_matrix (j : Fin 3) : Commute (S (boost j)) (S 3) := by
  have hp : Commute (GaussCoframeSpin.primal (activeIndex (boost j))) (GaussCoframeSpin.primal 6) := by
    change GaussCoframeSpin.spinLift _*GaussCoframeSpin.spinLift _=GaussCoframeSpin.spinLift _*GaussCoframeSpin.spinLift _
    have hactive : activeIndex (boost j)=⟨j.val,by omega⟩ := by simp [activeIndex,j.isLt]
    rw [hactive,←lift_mul,←lift_mul,(boost_chiral_source j).eq]
  have hd := congrArg ((starRingEnd ℂ).mapMatrix : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ →+* _) hp.eq
  simp only [map_mul] at hd
  change (GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ)*(GaussCoframeSpin.primal 6).map (starRingEnd ℂ)=
    (GaussCoframeSpin.primal 6).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ) at hd
  have hj : (activeIndex (boost j)).val<3 := by simp [activeIndex,j.isLt]
  change GaussCoframeSpin.full (activeIndex (boost j))*GaussCoframeSpin.full 6=
    GaussCoframeSpin.full 6*GaussCoframeSpin.full (activeIndex (boost j))
  simp only [GaussCoframeSpin.full,hj,show ¬(6:Fin 7).val<3 by decide,ite_true,ite_false,
    Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero]
  have he : (GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ)*
      (-(GaussCoframeSpin.primal 6).map (starRingEnd ℂ))=
      (-(GaussCoframeSpin.primal 6).map (starRingEnd ℂ))*(GaussCoframeSpin.primal (activeIndex (boost j))).map (starRingEnd ℂ) := by
    linear_combination (norm := noncomm_ring) -hd
  rw [hp.eq,he]

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem mixed_matrix {R : Type*} [Ring R] (A B Y : R) (hAB : A*B+B*A=0) (hAY : A*Y+Y*A=0) :
    bracket A (bracket B Y)=0 := by
  unfold bracket
  linear_combination (norm := noncomm_ring) hAB*Y+Y*hAB-hAY*B-B*hAY

private theorem mixed_fiber (j k : Fin 3) (hjk : j≠k) (sharp : Bool) (phi : Scalar) :
    bracket (quantized (S (boost j))) (bracket (quantized (S (boost k))) (branchMap sharp phi))=0 := by
  rw [original_active_spin_matrix,quantized_bracket,
    mixed_matrix _ _ _ (boost_pair_anti j k hjk) (branch_anti (boost j) sharp phi)]
  exact map_zero quantizer

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp <;> rfl
private theorem spin_at (j : Fin 4) (f : QuantumTest) (z : SourceCoordinateSlice) : activeSpin j f z=quantized (S j) (f z) := rfl

private theorem core_ladder (j : Fin 4) (sharp : Bool) : bracket (activeSpin j) (spinVariation sharp j)=fullAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have h := congrArg (fun A : FiberEnd => A (f z)) (original_active_spin_ladder j sharp (scalarField z))
  simpa only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,
    spin_at,full_at,map_sub,mul_apply_eq_comp] using h

private theorem core_mixed (j k : Fin 3) (hjk : j≠k) (sharp : Bool) :
    bracket (activeSpin (boost j)) (spinVariation sharp (boost k))=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have h := congrArg (fun A : FiberEnd => A (f z)) (mixed_fiber j k hjk sharp (scalarField z))
  simpa only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,
    spin_at,full_at,map_sub,mul_apply_eq_comp,zero_apply,LinearMap.zero_apply] using h

private theorem core_chiral (j : Fin 3) : Commute (activeSpin (boost j)) (activeSpin 3) := by
  have hf : Commute (quantized (S (boost j))) (quantized (S 3)) := by
    change quantized (S (boost j))*quantized (S 3)=quantized (S 3)*quantized (S (boost j))
    apply sub_eq_zero.mp
    change bracket (quantized (S (boost j))) (quantized (S 3))=0
    rw [quantized_bracket,bracket,←(boost_chiral_matrix j).eq,sub_self]
    exact map_zero quantizer
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantized (S (boost j)) (quantized (S 3) (f z))=quantized (S 3) (quantized (S (boost j)) (f z))
  exact congrArg (fun A : FiberEnd => A (f z)) hf.eq

private theorem ad_commute {R : Type*} [Ring R] (A B Y : R) (h : Commute A B) :
    bracket A (bracket B Y)=bracket B (bracket A Y) := by
  unfold bracket
  linear_combination (norm := noncomm_ring) h.eq*Y-Y*h.eq


/-- The original eight source coefficients use one shared carrier. -/
abbrev spinClosureCoefficient := SourceClockYukawaSpinRelativeForm.spinCoefficient

def closureMatrix (j : Fin 4) (mu nu : Fin 8) : ℂ :=
  if j.val<3 then
    if (mu.val=0 ∧ nu.val=j.val+1) ∨ (nu.val=0 ∧ mu.val=j.val+1) ∨
      (mu.val=4 ∧ nu.val=j.val+5) ∨ (nu.val=4 ∧ mu.val=j.val+5) then 1 else 0
  else if (mu.val+4)%8=nu.val then 1 else 0

/-- The actual Clifford coefficient matrices are real and symmetric. -/
theorem original_closure_matrix_symmetric (j : Fin 4) (mu nu : Fin 8) :
    closureMatrix j mu nu=closureMatrix j nu mu := by
  fin_cases j <;> fin_cases mu <;> fin_cases nu <;> norm_num [closureMatrix]

private theorem coefficient_tuple (sharp : Bool) : spinClosureCoefficient sharp=
    ![fullAction sharp,spinVariation sharp 0,spinVariation sharp 1,spinVariation sharp 2,
      spinVariation sharp 3,bracket (activeSpin 0) (spinVariation sharp 3),
      bracket (activeSpin 1) (spinVariation sharp 3),bracket (activeSpin 2) (spinVariation sharp 3)] := by
  funext mu
  fin_cases mu <;> rfl

private theorem diagonal (j : Fin 4) (sharp : Bool) : bracket (activeSpin j) (bracket (activeSpin j) (fullAction sharp))=fullAction sharp :=
  core_ladder j sharp
private theorem cross_chiral (j : Fin 3) (sharp : Bool) :
    bracket (activeSpin 3) (spinVariation sharp (boost j))=
      bracket (activeSpin (boost j)) (spinVariation sharp 3) :=
  (ad_commute _ _ _ (core_chiral j)).symm
private theorem second_chiral (j : Fin 3) (sharp : Bool) :
    bracket (activeSpin 3) (bracket (activeSpin (boost j)) (spinVariation sharp 3))=spinVariation sharp (boost j) := by
  rw [ad_commute _ _ _ (core_chiral j).symm,core_ladder]
  rfl
private theorem boost_chiral_diagonal (j : Fin 3) (sharp : Bool) :
    bracket (activeSpin (boost j)) (bracket (activeSpin (boost j)) (spinVariation sharp 3))=spinVariation sharp 3 := by
  change bracket (activeSpin (boost j)) (bracket (activeSpin (boost j)) (bracket (activeSpin 3) (fullAction sharp)))=_
  rw [ad_commute _ _ _ (core_chiral j),ad_commute _ _ _ (core_chiral j),diagonal]
  rfl
private theorem boost_chiral_mixed (j k : Fin 3) (hjk : j≠k) (sharp : Bool) :
    bracket (activeSpin (boost j)) (bracket (activeSpin (boost k)) (spinVariation sharp 3))=0 := by
  change bracket (activeSpin (boost j)) (bracket (activeSpin (boost k)) (bracket (activeSpin 3) (fullAction sharp)))=0
  rw [ad_commute _ _ _ (core_chiral k),ad_commute _ _ _ (core_chiral j)]
  have h := core_mixed j k hjk sharp
  change bracket (activeSpin (boost j)) (bracket (activeSpin (boost k)) (fullAction sharp))=0 at h
  rw [h]
  simp only [bracket,mul_zero,zero_mul,sub_self]

attribute [local irreducible] activeSpin spinVariation

/-- Every active source spin acts on the same eight full-CAR coefficients. -/
theorem original_spin_closure (j : Fin 4) (sharp : Bool) (mu : Fin 8) :
    bracket (activeSpin j) (spinClosureCoefficient sharp mu)=
      ∑ nu : Fin 8,closureMatrix j mu nu • spinClosureCoefficient sharp nu := by
  rw [coefficient_tuple]
  fin_cases j <;> fin_cases mu
  all_goals simp [closureMatrix,Fin.sum_univ_succ]
  all_goals first
    | exact core_ladder _ sharp
    | exact core_mixed 0 1 (by decide) sharp
    | exact core_mixed 0 2 (by decide) sharp
    | exact core_mixed 1 0 (by decide) sharp
    | exact core_mixed 1 2 (by decide) sharp
    | exact core_mixed 2 0 (by decide) sharp
    | exact core_mixed 2 1 (by decide) sharp
    | exact cross_chiral 0 sharp
    | exact cross_chiral 1 sharp
    | exact cross_chiral 2 sharp
    | exact second_chiral 0 sharp
    | exact second_chiral 1 sharp
    | exact second_chiral 2 sharp
    | exact boost_chiral_diagonal 0 sharp
    | exact boost_chiral_diagonal 1 sharp
    | exact boost_chiral_diagonal 2 sharp
    | exact boost_chiral_mixed 0 1 (by decide) sharp
    | exact boost_chiral_mixed 0 2 (by decide) sharp
    | exact boost_chiral_mixed 1 0 (by decide) sharp
    | exact boost_chiral_mixed 1 2 (by decide) sharp
    | exact boost_chiral_mixed 2 0 (by decide) sharp
    | exact boost_chiral_mixed 2 1 (by decide) sharp
    | rfl
    | unfold spinVariation;rfl


private def daggerSign (mu : Fin 8) : ℂ := if 0 < mu.val ∧ mu.val < 5 then -1 else 1

def daggerCoefficient (sharp : Bool) (mu : Fin 8) : End := daggerSign mu • spinClosureCoefficient (!sharp) mu

/-- The complete positive CAR square retains both products of every original coefficient. -/
def Q8 (sharp : Bool) : End := ∑ mu : Fin 8,
  (daggerCoefficient sharp mu*spinClosureCoefficient sharp mu+
    spinClosureCoefficient sharp mu*daggerCoefficient sharp mu)

def closureGram (sharp : Bool) (q : QuantumTest) : ℝ :=
  SourceClockYukawaSpinRelativeForm.spinVariationGram sharp q+
    SourceClockYukawaSpinRelativeForm.spinVariationGram (!sharp) q

private theorem matrix_parity (j : Fin 4) (mu nu : Fin 8) :
    daggerSign mu*closureMatrix j mu nu=-(closureMatrix j mu nu*daggerSign nu) := by
  fin_cases j <;> fin_cases mu <;> fin_cases nu <;> norm_num [closureMatrix,daggerSign]

private theorem bracket_scalar {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (A B : R) (c : ℂ) : bracket A (c • B)=c • bracket A B := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bracket_add {R : Type*} [Ring R] (A B C : R) : bracket A (B+C)=bracket A B+bracket A C := by
  unfold bracket;noncomm_ring
private theorem bracket_product {R : Type*} [Ring R] (A B C : R) : bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket;noncomm_ring
private theorem bracket_sum {R : Type*} [Ring R] (A : R) (B : Fin 8 → R) : bracket A (∑ mu,B mu)=∑ mu,bracket A (B mu) := by
  simp only [bracket,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]

private theorem dagger_closure (j : Fin 4) (sharp : Bool) (mu : Fin 8) :
    bracket (activeSpin j) (daggerCoefficient sharp mu)=
      -(∑ nu : Fin 8,closureMatrix j mu nu • daggerCoefficient sharp nu) := by
  unfold daggerCoefficient
  rw [bracket_scalar,original_spin_closure]
  simp only [Finset.smul_sum,smul_smul]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro nu _
  rw [matrix_parity,neg_smul]

private theorem symmetric_square {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (J : R) (K D : Fin 8 → R) (C : Matrix (Fin 8) (Fin 8) ℂ)
    (hC : ∀ mu nu,C mu nu=C nu mu)
    (hK : ∀ mu,bracket J (K mu)=∑ nu,C mu nu • K nu)
    (hD : ∀ mu,bracket J (D mu)=-(∑ nu,C mu nu • D nu)) :
    bracket J (∑ mu,(D mu*K mu+K mu*D mu))=0 := by
  have h1 : (∑ mu : Fin 8,∑ nu : Fin 8,C mu nu • (D nu*K mu))=
      ∑ mu : Fin 8,∑ nu : Fin 8,C mu nu • (D mu*K nu) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro nu _
    rw [hC nu mu]
  have h2 : (∑ mu : Fin 8,∑ nu : Fin 8,C mu nu • (K mu*D nu))=
      ∑ mu : Fin 8,∑ nu : Fin 8,C mu nu • (K nu*D mu) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro nu _
    rw [hC nu mu]
  simp_rw [bracket_sum,bracket_add,bracket_product,hK,hD]
  simp only [neg_mul,mul_neg,Finset.sum_neg_distrib,Finset.sum_add_distrib,
    Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  linear_combination (norm := module) -h1-h2

/-- The full positive square commutes with each actual boost and chiral spin. -/
theorem original_Q8_active_commute (j : Fin 4) (sharp : Bool) : Commute (activeSpin j) (Q8 sharp) := by
  change activeSpin j*Q8 sharp=Q8 sharp*activeSpin j
  apply sub_eq_zero.mp
  exact symmetric_square (activeSpin j) (spinClosureCoefficient sharp) (daggerCoefficient sharp) (closureMatrix j)
    (original_closure_matrix_symmetric j) (original_spin_closure j sharp) (dagger_closure j sharp)


private theorem full_pair (sharp : Bool) : GaussCoframeForm.Paired (fullAction sharp) (fullAction (!sharp)) := by
  intro p q
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · change sourcePair p (GaussYukawaOperator.originalAction q)=sourcePair (GaussFullHamiltonian.adjointAction p) q
    have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm] using h.symm
  · change sourcePair p (GaussFullHamiltonian.adjointAction q)=sourcePair (GaussYukawaOperator.originalAction p) q
    exact GaussFullHamiltonian.yukawa_pair p q
private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm
private theorem bracket_paired (J A B : End) (hJ : GaussCoframeForm.Paired J J)
    (hA : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired (bracket J A) (-bracket J B) := by
  intro p q
  calc
    _=sourcePair p (J (A q))-sourcePair p (A (J q)) := by
      simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    _=sourcePair (B (J p)) q-sourcePair (J (B p)) q := by rw [hJ,hA,hA,hJ]
    _=_ := by
      simp only [bracket,LinearMap.neg_apply,LinearMap.sub_apply,Module.End.mul_apply,
        sourcePair,map_neg,map_sub,inner_neg_left,inner_sub_left]
      module

private theorem active_paired (j : Fin 4) : GaussCoframeForm.Paired (activeSpin j) (activeSpin j) := by
  unfold activeSpin
  exact GaussCoframeSpin.current_pair (activeIndex j)
private theorem variation_pair (j : Fin 4) (sharp : Bool) :
    GaussCoframeForm.Paired (spinVariation sharp j) (-spinVariation (!sharp) j) := by
  unfold spinVariation
  exact bracket_paired (activeSpin j) (fullAction sharp) (fullAction (!sharp)) (active_paired j) (full_pair sharp)
private theorem double_pair (j : Fin 3) (sharp : Bool) :
    GaussCoframeForm.Paired (bracket (activeSpin (boost j)) (spinVariation sharp 3))
      (bracket (activeSpin (boost j)) (spinVariation (!sharp) 3)) := by
  have h := bracket_paired (activeSpin (boost j)) (spinVariation sharp 3) (-spinVariation (!sharp) 3) (active_paired (boost j)) (variation_pair 3 sharp)
  have he : -bracket (activeSpin (boost j)) (-spinVariation (!sharp) 3)=
      bracket (activeSpin (boost j)) (spinVariation (!sharp) 3) := by unfold bracket;noncomm_ring
  rw [he] at h
  exact h

private theorem coefficient_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (spinClosureCoefficient sharp mu) (daggerCoefficient sharp mu) := by
  unfold daggerCoefficient
  rw [coefficient_tuple,coefficient_tuple]
  fin_cases mu
  · change GaussCoframeForm.Paired (fullAction sharp) ((1:ℂ) • fullAction (!sharp))
    rw [one_smul]
    exact full_pair sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 0) ((-1:ℂ) • spinVariation (!sharp) 0)
    rw [neg_one_smul]
    exact variation_pair 0 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 1) ((-1:ℂ) • spinVariation (!sharp) 1)
    rw [neg_one_smul]
    exact variation_pair 1 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 2) ((-1:ℂ) • spinVariation (!sharp) 2)
    rw [neg_one_smul]
    exact variation_pair 2 sharp
  · change GaussCoframeForm.Paired (spinVariation sharp 3) ((-1:ℂ) • spinVariation (!sharp) 3)
    rw [neg_one_smul]
    exact variation_pair 3 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 0) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 0) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 0 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 1) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 1) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 1 sharp
  · change GaussCoframeForm.Paired (bracket (activeSpin 2) (spinVariation sharp 3))
      ((1:ℂ) • bracket (activeSpin 2) (spinVariation (!sharp) 3))
    rw [one_smul]
    exact double_pair 2 sharp

private theorem dagger_norm (sharp : Bool) (mu : Fin 8) (q : QuantumTest) :
    ‖embed (daggerCoefficient sharp mu q)‖=‖embed (spinClosureCoefficient (!sharp) mu q)‖ := by
  have hs : ‖daggerSign mu‖=1 := by fin_cases mu <;> norm_num [daggerSign]
  simp only [daggerCoefficient,LinearMap.smul_apply,map_smul,norm_smul,hs,one_mul]

private theorem square_row (sharp : Bool) (mu : Fin 8) (q : QuantumTest) :
    (sourcePair q ((daggerCoefficient sharp mu*spinClosureCoefficient sharp mu+
      spinClosureCoefficient sharp mu*daggerCoefficient sharp mu) q)).re=
      ‖embed (spinClosureCoefficient sharp mu q)‖^2+‖embed (spinClosureCoefficient (!sharp) mu q)‖^2 := by
  have h := coefficient_pair sharp mu
  have hd := paired_symm h
  have ha : sourcePair q ((daggerCoefficient sharp mu) (spinClosureCoefficient sharp mu q))=
      sourcePair (spinClosureCoefficient sharp mu q) (spinClosureCoefficient sharp mu q) := hd q _
  have hb : sourcePair q ((spinClosureCoefficient sharp mu) (daggerCoefficient sharp mu q))=
      sourcePair (daggerCoefficient sharp mu q) (daggerCoefficient sharp mu q) := h q _
  simp only [LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_add,inner_add_right,Complex.add_re] at *
  rw [ha,hb]
  change RCLike.re (inner ℂ (embed (spinClosureCoefficient sharp mu q)) (embed (spinClosureCoefficient sharp mu q)))+
    RCLike.re (inner ℂ (embed (daggerCoefficient sharp mu q)) (embed (daggerCoefficient sharp mu q)))=_
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq,dagger_norm]

/-- The exact complete CAR square equals the original two-sharp positive Gram. -/
theorem original_Q8_gram (sharp : Bool) (q : QuantumTest) :
    (sourcePair q (Q8 sharp q)).re=closureGram sharp q := by
  simp only [Q8,LinearMap.sum_apply,sourcePair,map_sum,inner_sum,Complex.re_sum]
  change (∑ mu : Fin 8,(sourcePair q ((daggerCoefficient sharp mu*spinClosureCoefficient sharp mu+
    spinClosureCoefficient sharp mu*daggerCoefficient sharp mu) q)).re)=_
  simp_rw [square_row]
  rw [Finset.sum_add_distrib]
  rfl

theorem original_Q8_nonnegative (sharp : Bool) (q : QuantumTest) : 0 ≤ (sourcePair q (Q8 sharp q)).re := by
  rw [original_Q8_gram]
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))


/-- A fixed finite coefficient price generated by the original active CAR spins. -/
def closurePrice : ℝ := 1+(9/400:ℝ)+(3/2:ℝ)*∑ j : Fin 4,(spinNumberPrice j)^2

private theorem gram_tuple (sharp : Bool) (q : QuantumTest) :
    SourceClockYukawaSpinRelativeForm.spinVariationGram sharp q=
      ‖embed (fullAction sharp q)‖^2+(∑ j : Fin 4,‖embed (spinVariation sharp j q)‖^2)+
        ∑ j : Fin 3,‖embed (bracket (activeSpin (boost j)) (spinVariation sharp 3) q)‖^2 := by
  unfold SourceClockYukawaSpinRelativeForm.spinVariationGram
  change (∑ mu : Fin 8,‖embed (spinClosureCoefficient sharp mu q)‖^2)=_
  rw [coefficient_tuple]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change _=‖embed (fullAction sharp q)‖^2+
    (‖embed (spinVariation sharp 0 q)‖^2+(‖embed (spinVariation sharp 1 q)‖^2+
      (‖embed (spinVariation sharp 2 q)‖^2+‖embed (spinVariation sharp 3 q)‖^2)))+
    (‖embed (bracket (activeSpin 0) (spinVariation sharp 3) q)‖^2+
      (‖embed (bracket (activeSpin 1) (spinVariation sharp 3) q)‖^2+
        ‖embed (bracket (activeSpin 2) (spinVariation sharp 3) q)‖^2))
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

/-- The frozen signed spin price is paid by the actual complete positive source Gram. -/
theorem original_spin_relative_closure_price (sharp : Bool) (q : QuantumTest) :
    spinRelativePrice sharp q ≤ closurePrice*closureGram sharp q := by
  have hN : 0 ≤ ∑ j : Fin 4,(spinNumberPrice j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ closurePrice := by unfold closurePrice;nlinarith only [hN]
  have h0 : (9/400:ℝ) ≤ closurePrice := by unfold closurePrice;nlinarith only [hN]
  have h1 : (1:ℝ) ≤ closurePrice := by unfold closurePrice;nlinarith only [hN]
  have hJ (j : Fin 4) : (3/2:ℝ)*(spinNumberPrice j)^2 ≤ closurePrice := by
    have hj : (spinNumberPrice j)^2 ≤ ∑ i : Fin 4,(spinNumberPrice i)^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    unfold closurePrice
    nlinarith only [hj]
  have hs : (3/2:ℝ)*(∑ j : Fin 4,(spinNumberPrice j)^2*‖embed (spinVariation sharp j q)‖^2) ≤
      closurePrice*(∑ j : Fin 4,‖embed (spinVariation sharp j q)‖^2) := by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hJ j) (sq_nonneg ‖embed (spinVariation sharp j q)‖)
  have hY := mul_le_mul_of_nonneg_right h0 (sq_nonneg ‖embed (fullAction sharp q)‖)
  have hD := mul_le_mul_of_nonneg_right h1 (show 0 ≤ ∑ j : Fin 3,‖embed (bracket (activeSpin (boost j)) (spinVariation sharp 3) q)‖^2 from
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hprice : spinRelativePrice sharp q ≤ closurePrice*SourceClockYukawaSpinRelativeForm.spinVariationGram sharp q := by
    rw [gram_tuple]
    unfold spinRelativePrice
    change (9/400:ℝ)*‖embed (fullAction sharp q)‖^2+
      (3/2:ℝ)*(∑ j : Fin 4,(spinNumberPrice j)^2*‖embed (spinVariation sharp j q)‖^2)+
      (∑ j : Fin 3,‖embed (bracket (activeSpin (boost j)) (spinVariation sharp 3) q)‖^2) ≤ _
    nlinarith only [hs,hY,hD]
  have hbar : 0 ≤ SourceClockYukawaSpinRelativeForm.spinVariationGram (!sharp) q :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply hprice.trans
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hbar) hC

/-- The original spin current is paid by the same coframe and conserved complete source square. -/
theorem original_spin_closure_coframe_price (sharp : Bool) (p q : QuantumTest) (δ : ℝ) (hδ : 0<δ) :
    ‖sourcePair p (spinCurrent sharp q)‖ ≤ δ*(sourceTime 0)^2*SourceClockReflectedForm.coframeGram (inverseVolumeAction p)+
      (closurePrice/δ)*closureGram sharp q := by
  have h := original_spin_relative_coframe_price sharp p q δ hδ
  have hp := div_le_div_of_nonneg_right (original_spin_relative_closure_price sharp q) hδ.le
  apply h.trans (add_le_add (le_refl _) (hp.trans_eq _))
  ring


set_option backward.isDefEq.respectTransparency false

private theorem boost_bracket {R : Type*} [Ring R] (A B C : R)
    (ha : A*A= -1) (hB : A*B+B*A=0) (hC : A*C+C*A=0) :
    bracket (A*B) (A*C)=B*C-C*B := by
  unfold bracket
  linear_combination (norm := noncomm_ring) A*hB*C-A*hC*B-ha*(B*C-C*B)
private theorem rotation {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (A B C : R) (ha : A*A= -1) (hB : A*B+B*A=0) (hC : A*C+C*A=0) (hBC : B*C+C*B=0) :
    (Complex.I/2:ℂ) • (B*C)=Complex.I • bracket ((1/2:ℂ) • (A*B)) ((1/2:ℂ) • (A*C)) := by
  have hb := boost_bracket A B C ha hB hC
  have hCB : C*B=-(B*C) := by linear_combination (norm := module) hBC
  simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_smul,←smul_sub]
  change _=(Complex.I*((1/2:ℂ)*(1/2:ℂ))) • bracket (A*B) (A*C)
  rw [hb,hCB]
  module
private abbrev spatialIndex (j : Fin 3) : Fin 7 := ⟨j.val+3,by omega⟩
private def rotA (j : Fin 3) : Fin 3 := ![1,2,0] j
private def rotB (j : Fin 3) : Fin 3 := ![2,0,1] j
private theorem source_rotation (j : Fin 3) : GaussCoframeSpin.sourceSpin (spatialIndex j)=
    Complex.I • bracket (GaussCoframeSpin.sourceSpin (activeIndex (boost (rotA j))))
      (GaussCoframeSpin.sourceSpin (activeIndex (boost (rotB j)))) := by
  fin_cases j
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroTwo_anticommute diracGammaZeroThree_anticommute diracGammaTwoThree_anticommute
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroThree_anticommute diracGammaZeroOne_anticommute
      ((add_comm _ _).trans diracGammaOneThree_anticommute)
  · exact rotation _ _ _ diracGammaZero_sq diracGammaZeroOne_anticommute diracGammaZeroTwo_anticommute diracGammaOneTwo_anticommute
private theorem lift_scalar (A : DiracMatrix) (c : ℂ) : GaussCoframeSpin.spinLift (c • A)=c • GaussCoframeSpin.spinLift A := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [GaussCoframeSpin.spinLift,h]
private theorem lift_sub (A B : DiracMatrix) : GaussCoframeSpin.spinLift (A-B)=GaussCoframeSpin.spinLift A-GaussCoframeSpin.spinLift B := by
  ext i j
  by_cases h : i.2=j.2 <;> simp [GaussCoframeSpin.spinLift,h]
private theorem primal_rotation (j : Fin 3) : GaussCoframeSpin.primal (spatialIndex j)=
    Complex.I • bracket (GaussCoframeSpin.primal (activeIndex (boost (rotA j))))
      (GaussCoframeSpin.primal (activeIndex (boost (rotB j)))) := by
  simp only [GaussCoframeSpin.primal,source_rotation,bracket,lift_scalar,lift_sub,lift_mul]
private theorem conjugate_scalar {ι : Type*} (A : Matrix ι ι ℂ) (c : ℂ) :
    (c • A).map (starRingEnd ℂ)=(starRingEnd ℂ c) • A.map (starRingEnd ℂ) := by
  ext i j
  change (starRingEnd ℂ) (c*A i j)=(starRingEnd ℂ c)*(starRingEnd ℂ (A i j))
  exact map_mul (starRingEnd ℂ) _ _
private theorem conjugate_bracket {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) :
    (bracket A B).map (starRingEnd ℂ)=bracket (A.map (starRingEnd ℂ)) (B.map (starRingEnd ℂ)) := by
  ext i j
  simp only [bracket,Matrix.map_apply,Matrix.sub_apply,map_sub,Matrix.mul_apply,map_sum,map_mul]
private theorem block_bracket {ι : Type*} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℂ) :
    bracket (Matrix.fromBlocks A 0 0 C) (Matrix.fromBlocks B 0 0 D)=
      Matrix.fromBlocks (bracket A B) 0 0 (bracket C D) := by
  simp only [bracket,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero,
    Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,zero_add]
private theorem full_rotation (j : Fin 3) : GaussCoframeSpin.full (spatialIndex j)=
    Complex.I • bracket (S (boost (rotA j))) (S (boost (rotB j))) := by
  have ha : (activeIndex (boost (rotA j))).val<3 := by simp [activeIndex,(rotA j).isLt]
  have hb : (activeIndex (boost (rotB j))).val<3 := by simp [activeIndex,(rotB j).isLt]
  have hs : ¬(spatialIndex j).val<3 := by
    change ¬j.val+3<3
    omega
  have hp := primal_rotation j
  have hdual : -(GaussCoframeSpin.primal (spatialIndex j)).map (starRingEnd ℂ)=Complex.I •
      bracket ((GaussCoframeSpin.primal (activeIndex (boost (rotA j)))).map (starRingEnd ℂ))
        ((GaussCoframeSpin.primal (activeIndex (boost (rotB j)))).map (starRingEnd ℂ)) := by
    rw [hp,conjugate_scalar,conjugate_bracket,show starRingEnd ℂ Complex.I= -Complex.I by simp,
      neg_smul,neg_neg]
  simp only [S,GaussCoframeSpin.full,ha,hb,hs,ite_true,ite_false]
  simp only [bracket,sub_eq_add_neg,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
    Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,zero_add,add_zero]
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero]
  simp only [bracket,sub_eq_add_neg] at hp hdual
  rw [hdual,hp]

set_option backward.isDefEq.respectTransparency true

private theorem spatial_core (j : Fin 3) : GaussCoframeSpin.current (spatialIndex j)=
    Complex.I • bracket (activeSpin (boost (rotA j))) (activeSpin (boost (rotB j))) := by
  have h : quantized (GaussCoframeSpin.full (spatialIndex j))=
      Complex.I • bracket (quantized (S (boost (rotA j)))) (quantized (S (boost (rotB j)))) := by
    change quantizer (GaussCoframeSpin.full (spatialIndex j))=_
    rw [full_rotation,map_smul]
    change Complex.I • quantized (bracket (S (boost (rotA j))) (S (boost (rotB j))))=_
    rw [←quantized_bracket]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hc (g : QuantumTest) : GaussCoframeSpin.current (spatialIndex j) g z=quantized (GaussCoframeSpin.full (spatialIndex j)) (g z) := rfl
  simp only [LinearMap.smul_apply,bracket,LinearMap.sub_apply,Module.End.mul_apply,hc]
  unfold activeSpin
  change quantized (GaussCoframeSpin.full (spatialIndex j)) (f z)=Complex.I •
    (quantized (S (boost (rotA j))) (quantized (S (boost (rotB j))) (f z))-
      quantized (S (boost (rotB j))) (quantized (S (boost (rotA j))) (f z)))
  simpa only [bracket,smul_apply,sub_apply,mul_apply_eq_comp] using congrArg (fun A : FiberEnd => A (f z)) h
set_option backward.isDefEq.respectTransparency true

private theorem spatial_Q8 (j : Fin 3) (sharp : Bool) : Commute (GaussCoframeSpin.current (spatialIndex j)) (Q8 sharp) := by
  rw [spatial_core]
  have ha := original_Q8_active_commute (boost (rotA j)) sharp
  have hb := original_Q8_active_commute (boost (rotB j)) sharp
  exact ((ha.mul_left hb).sub_left (hb.mul_left ha)).smul_left Complex.I

private theorem number_spin (j : Fin 7) : Commute GaussCoframeForm.number (GaussCoframeSpin.current j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hn (g : QuantumTest) : GaussCoframeForm.number g z=fiberNumber (g z) := by
    apply PiLp.ext
    intro word
    exact (GaussCoframeForm.number_apply g z word).trans (fiberNumber_apply (g z) word).symm
  change GaussCoframeForm.number (GaussCoframeSpin.current j f) z=GaussCoframeSpin.current j (GaussCoframeForm.number f) z
  have hs (g : QuantumTest) : GaussCoframeSpin.current j g z=quantized (GaussCoframeSpin.full j) (g z) := rfl
  simp only [hn,hs]
  exact congrArg (fun A : FiberEnd => A (f z)) (number_commute (GaussCoframeSpin.full j)).eq
private theorem real_spin (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (j : Fin 4) :
    Commute (multiply c hc) (activeSpin j) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (activeSpin j f) z=activeSpin j (multiply c hc f) z
  rw [multiply_apply,spin_at,spin_at,multiply_apply]
  exact (map_smul (quantized (S j)) _ _).symm
private theorem real_full (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (fullAction sharp f) z=fullAction sharp (multiply c hc f) z
  rw [multiply_apply,full_at,full_at,multiply_apply]
  exact (map_smul (branchMap sharp (scalarField z)) _ _).symm
private theorem coefficient_commute {A : End} (sharp : Bool)
    (hJ : ∀ j : Fin 4,Commute A (activeSpin j)) (hY : Commute A (fullAction sharp)) (mu : Fin 8) :
    Commute A (spinClosureCoefficient sharp mu) := by
  have hK (j : Fin 4) : Commute A (spinVariation sharp j) := by
    unfold spinVariation
    exact ((hJ j).mul_right hY).sub_right (hY.mul_right (hJ j))
  have hD (j : Fin 3) : Commute A (bracket (activeSpin (boost j)) (spinVariation sharp 3)) :=
    ((hJ (boost j)).mul_right (hK 3)).sub_right ((hK 3).mul_right (hJ (boost j)))
  rw [coefficient_tuple]
  fin_cases mu
  · exact hY
  · exact hK 0
  · exact hK 1
  · exact hK 2
  · exact hK 3
  · exact hD 0
  · exact hD 1
  · exact hD 2
private theorem Q8_commute {A : End} (sharp : Bool)
    (hJ : ∀ j : Fin 4,Commute A (activeSpin j)) (hY : ∀ s : Bool,Commute A (fullAction s)) : Commute A (Q8 sharp) := by
  have hK (mu : Fin 8) := coefficient_commute sharp hJ (hY sharp) mu
  have hD (mu : Fin 8) : Commute A (daggerCoefficient sharp mu) :=
    (coefficient_commute (!sharp) hJ (hY (!sharp)) mu).smul_right _
  unfold Q8
  exact Commute.sum_right Finset.univ (fun mu => daggerCoefficient sharp mu*spinClosureCoefficient sharp mu+
    spinClosureCoefficient sharp mu*daggerCoefficient sharp mu) A (fun mu _ => ((hD mu).mul_right (hK mu)).add_right ((hK mu).mul_right (hD mu)))
private theorem real_Q8 (c : SourceCoordinateSlice → ℝ) (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (Q8 sharp) := Q8_commute sharp (real_spin c hc) (real_full c hc)
private theorem number_Q8 (sharp : Bool) : Commute GaussCoframeForm.number (Q8 sharp) := by
  have hj (j : Fin 4) : Commute GaussCoframeForm.number (activeSpin j) := by
    unfold activeSpin
    exact number_spin (activeIndex j)
  exact Q8_commute sharp hj original_number_full

/-- The complete source square commutes with the original seven signed squares and Number shift. -/
theorem original_Q8_spin_commute (sharp : Bool) : Commute spinPotential (Q8 sharp) := by
  have hJ (j : Fin 7) : Commute (GaussCoframeSpin.current j) (Q8 sharp) := by
    fin_cases j
    · simpa [activeSpin,activeIndex] using original_Q8_active_commute 0 sharp
    · simpa [activeSpin,activeIndex] using original_Q8_active_commute 1 sharp
    · simpa [activeSpin,activeIndex] using original_Q8_active_commute 2 sharp
    · exact spatial_Q8 0 sharp
    · exact spatial_Q8 1 sharp
    · exact spatial_Q8 2 sharp
    · simpa [activeSpin,activeIndex] using original_Q8_active_commute 3 sharp
  have hS (j : Fin 7) : Commute (GaussCoframeForm.spinSquare j) (Q8 sharp) := by
    unfold GaussCoframeForm.spinSquare
    simp only [←Module.End.mul_eq_comp]
    exact (((hJ j).mul_left (real_Q8 GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth sharp)).mul_left (hJ j)).smul_left _
  have hN : Commute GaussCoframeForm.numberShift (Q8 sharp) := by
    unfold GaussCoframeForm.numberShift
    simp only [←Module.End.mul_eq_comp]
    have hn := number_Q8 sharp
    have hc := real_Q8 GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth sharp
    exact ((hn.mul_left hc).add_left (hc.mul_left hn)).smul_left (1/2:ℂ)
  unfold spinPotential
  exact (Commute.sum_left Finset.univ GaussCoframeForm.spinSquare (Q8 sharp) (fun j _ => hS j)).add_left hN

/-- Both formal sharp readouts are the same complete source square. -/
theorem original_Q8_sharp_return (sharp : Bool) : Q8 (!sharp)=Q8 sharp := by
  unfold Q8 daggerCoefficient
  simp only [Bool.not_not,smul_mul_assoc,mul_smul_comm]
  apply Finset.sum_congr rfl
  intro mu _
  module

end LowEnergy.SourceClockYukawaSpinClosure
