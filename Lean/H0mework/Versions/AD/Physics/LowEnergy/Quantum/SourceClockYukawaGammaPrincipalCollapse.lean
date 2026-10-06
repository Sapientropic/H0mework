import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGammaPrincipalForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGammaPrincipalCollapse
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
open SourceClockYukawaGammaPrincipal
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

private theorem active_square (j : Fin 4) :
    GaussCoframeSpin.sourceSpin (activeIndex j)*GaussCoframeSpin.sourceSpin (activeIndex j)=(1/4 : ℂ) • (1 : DiracMatrix) := by
  fin_cases j
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaOne))*((1/2 : ℂ) • (diracGammaZero*diracGammaOne))=_
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,boost_square _ _ diracGammaZero_sq diracGammaOne_sq diracGammaZeroOne_anticommute]
    norm_num
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaTwo))*((1/2 : ℂ) • (diracGammaZero*diracGammaTwo))=_
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,boost_square _ _ diracGammaZero_sq diracGammaTwo_sq diracGammaZeroTwo_anticommute]
    norm_num
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaThree))*((1/2 : ℂ) • (diracGammaZero*diracGammaThree))=_
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,boost_square _ _ diracGammaZero_sq diracGammaThree_sq diracGammaZeroThree_anticommute]
    norm_num
  · change ((-1/2 : ℂ) • diracGammaFive)*((-1/2 : ℂ) • diracGammaFive)=_
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,diracGammaFive_sq]
    norm_num

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

private theorem primal_square (j : Fin 4) :
    GaussCoframeSpin.primal (activeIndex j)*GaussCoframeSpin.primal (activeIndex j)=
      (1/4:ℂ) • (1 : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ) := by
  rw [GaussCoframeSpin.primal,←lift_mul,active_square]
  ext i k
  change (if i.2=k.2 then ((1/4:ℂ) • (1:DiracMatrix)) i.1 k.1 else 0)=_
  rcases i with ⟨i,a⟩
  rcases k with ⟨k,b⟩
  simp only [Matrix.smul_apply,Matrix.one_apply]
  by_cases hab : a=b <;> by_cases hik : i=k <;> simp [hab,hik]

private theorem full_square (j : Fin 4) : S j*S j=(1/4:ℂ) • (1 : Matrix Mode Mode ℂ) := by
  have hp := primal_square j
  have hd := congrArg ((starRingEnd ℂ).mapMatrix : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ →+* _) hp
  simp only [map_mul] at hd
  change (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*
    (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)=
      ((1/4:ℂ) • (1 : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ)).map (starRingEnd ℂ) at hd
  have hd' : (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*
      (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)=
        (1/4:ℂ) • (1 : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ) := by
    rw [hd]
    ext i k
    simp only [Matrix.map_apply,Matrix.smul_apply,Matrix.one_apply,starRingEnd_apply]
    split_ifs <;> norm_num
  change GaussCoframeSpin.full (activeIndex j)*GaussCoframeSpin.full (activeIndex j)=_
  unfold GaussCoframeSpin.full
  split_ifs <;> rw [Matrix.fromBlocks_multiply] <;>
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,neg_mul,mul_neg,neg_neg,hp,hd'] <;>
    ext i k <;> cases i <;> cases k <;> simp [Matrix.fromBlocks,Matrix.one_apply]

private theorem anti_bracket {R : Type*} [Ring R] (J C A : R)
    (hJC : Commute J C) (hJA : J*A+A*J=0) :
    J*bracket C A+bracket C A*J=0 := by
  unfold bracket
  linear_combination (norm := noncomm_ring) hJC.eq*A+A*hJC.eq+C*hJA-hJA*C

private def row (A B : Matrix Mode Mode ℂ) : Matrix Mode Mode ℂ :=
  bracket A.conjTranspose B+bracket A B.conjTranspose

private theorem row_preserved (J A B : Matrix Mode Mode ℂ)
    (hJ : J.conjTranspose=J) (hJJ : J*J=(1/4:ℂ) • 1)
    (hA : J*A+A*J=0) (hB : J*B+B*J=0) :
    row (bracket J A) (bracket J B)=row A B := by
  have hr (X : Matrix Mode Mode ℂ) (hx : J*X+X*J=0) : bracket J X=(2:ℂ) • (J*X) := by
    unfold bracket
    linear_combination (norm := module) -hx
  have hl (X : Matrix Mode Mode ℂ) (hx : J*X+X*J=0) : bracket J X=(-2:ℂ) • (X*J) := by
    unfold bracket
    linear_combination (norm := module) hx
  have right (X Y : Matrix Mode Mode ℂ) (hx : J*X+X*J=0) (hy : J*Y+Y*J=0) :
      (bracket J X).conjTranspose*bracket J Y=X.conjTranspose*Y := by
    rw [hr X hx,hr Y hy,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,hJ]
    simp only [Complex.star_def,Complex.conj_ofNat,smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [show (X.conjTranspose*J)*(J*Y)=X.conjTranspose*(J*J)*Y by noncomm_ring,hJJ]
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,smul_smul]
    norm_num
  have left (X Y : Matrix Mode Mode ℂ) (hx : J*X+X*J=0) (hy : J*Y+Y*J=0) :
      bracket J X*(bracket J Y).conjTranspose=X*Y.conjTranspose := by
    rw [hl X hx,hl Y hy,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,hJ]
    simp only [Complex.star_def,map_neg,Complex.conj_ofNat,smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [show (X*J)*(J*Y.conjTranspose)=X*(J*J)*Y.conjTranspose by noncomm_ring,hJJ]
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,smul_smul]
    norm_num
  simp only [row,bracket]
  change (bracket J A).conjTranspose*bracket J B-bracket J B*(bracket J A).conjTranspose+
    (bracket J A*(bracket J B).conjTranspose-(bracket J B).conjTranspose*bracket J A)=_
  rw [right A B hA hB,left B A hB hA,left A B hA hB,right B A hB hA]

private theorem coefficient_row (mu : Fin 8) (phi psi : Scalar) :
    row (coefficientMatrix false mu phi) (coefficientMatrix false mu psi)=row (fullMatrix phi) (fullMatrix psi) := by
  have hsingle (j : Fin 4) := row_preserved (S j) (fullMatrix phi) (fullMatrix psi)
    (GaussCoframeSpin.full_hermitian _) (full_square j) (full_anti j phi) (full_anti j psi)
  unfold coefficientMatrix
  split_ifs with h0 h1
  · rfl
  · exact hsingle _
  · let j : Fin 3 := ⟨mu.val-5,by omega⟩
    have hp : S (boost j)*bracket (S 3) (fullMatrix phi)+bracket (S 3) (fullMatrix phi)*S (boost j)=0 :=
      anti_bracket _ _ _ (boost_chiral_matrix j) (full_anti _ phi)
    have hq : S (boost j)*bracket (S 3) (fullMatrix psi)+bracket (S 3) (fullMatrix psi)*S (boost j)=0 :=
      anti_bracket _ _ _ (boost_chiral_matrix j) (full_anti _ psi)
    exact (row_preserved (S (boost j)) _ _ (GaussCoframeSpin.full_hermitian _) (full_square _) hp hq).trans (hsingle 3)

/-- The complete eight-spin principal is exactly eight copies of the original one-body Yukawa current; all repaired-dual signs are retained before quantization. -/
theorem original_principal_closure_return (phi psi : Scalar) :
    principalMatrix phi psi=(8:ℂ) • (bracket (fullMatrix phi).conjTranspose (fullMatrix psi)+
      bracket (fullMatrix phi) (fullMatrix psi).conjTranspose) := by
  change (∑ mu : Fin 8,row (coefficientMatrix false mu phi) (coefficientMatrix false mu psi))=(8:ℂ) • row (fullMatrix phi) (fullMatrix psi)
  simp only [coefficient_row,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℂ 8 (row (fullMatrix phi) (fullMatrix psi))).symm


open SourceClockYukawaJointRadialZero SourceClockYukawaGammaPrincipalForm SourceClockYukawaSpinClosure
open SourceClockYukawaRadialNativeHessian SourceClockYukawaSpinJointForce
private def adMatrix (j : Fin 4) (A : Matrix Mode Mode ℂ) : Matrix Mode Mode ℂ :=
  bracket (GaussCoframeSpin.full (activeIndex j)) A

private def daggerSign (mu : Fin 8) : ℂ := if 0 < mu.val ∧ mu.val < 5 then -1 else 1

private theorem ad_dagger (j : Fin 4) (A : Matrix Mode Mode ℂ) :
    (adMatrix j A).conjTranspose=-adMatrix j A.conjTranspose := by
  unfold adMatrix bracket
  rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,
    GaussCoframeSpin.full_hermitian]
  noncomm_ring

private theorem ad_neg (j : Fin 4) (A : Matrix Mode Mode ℂ) : adMatrix j (-A)=-adMatrix j A := by
  unfold adMatrix bracket
  noncomm_ring

private theorem matrix_dagger (mu : Fin 8) (phi : Scalar) :
    coefficientMatrix true mu phi=daggerSign mu • (coefficientMatrix false mu phi).conjTranspose := by
  have he (s : Bool) : coefficientMatrix s mu phi=
      if h0 : mu.val=0 then branchMatrix s phi else
      if h1 : mu.val<5 then adMatrix ⟨mu.val-1,by omega⟩ (branchMatrix s phi) else
        adMatrix ⟨mu.val-5,by omega⟩ (adMatrix 3 (branchMatrix s phi)) := rfl
  simp only [he]
  split_ifs with h0 h1
  · have hs : daggerSign mu=1 := by simp [daggerSign,h0]
    rw [hs,one_smul]
    rfl
  · have hp : 0 < mu.val := Nat.pos_of_ne_zero h0
    simp only [daggerSign,hp,h1,and_self,ite_true,neg_one_smul,branchMatrix,
      Bool.false_eq_true,ite_false,ad_dagger,neg_neg]
  · have hs : ¬(0 < mu.val ∧ mu.val < 5) := by omega
    simp only [daggerSign,hs,ite_false,one_smul,branchMatrix,Bool.false_eq_true,
      ite_true,ad_dagger,ad_neg,neg_neg]

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    bracket (quantized A) (quantized B)=quantized (bracket A B) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [bracket,quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem full_at (sharp : Bool) (f : QuantumTest) (x : SourceCoordinateSlice) :
    fullAction sharp f x=quantized (branchMatrix sharp (scalarField x)) (f x) := by
  unfold SourceMixedNativeReturn.fullAction
  cases sharp
  · rfl
  · change (quantized (GaussYukawaCoefficient.fullMatrix (scalarField x))).adjoint (f x)=
      quantized (GaussYukawaCoefficient.fullMatrix (scalarField x)).conjTranspose (f x)
    exact congrArg (fun A : FiberEnd => A (f x))
      (quantized_adjoint (GaussYukawaCoefficient.fullMatrix (scalarField x)))

private theorem active_at (j : Fin 4) (f : QuantumTest) (x : SourceCoordinateSlice) :
    activeSpin j f x=quantized (GaussCoframeSpin.full (activeIndex j)) (f x) := rfl

private theorem core_coefficient_at (sharp : Bool) (mu : Fin 8) (f : QuantumTest)
    (x : SourceCoordinateSlice) :
    spinClosureCoefficient sharp mu f x=fiberCoefficient sharp mu (scalarField x) (f x) := by
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient fiberCoefficient coefficientMatrix
  split_ifs with h0 h1
  · exact full_at sharp f x
  · simp only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,full_at]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-1,by omega⟩)))
      (quantized (branchMatrix sharp (scalarField x)))) (f x)=_
    rw [quantized_bracket]
    rfl
  · simp only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,active_at,full_at]
    change (bracket (quantized (GaussCoframeSpin.full (activeIndex ⟨mu.val-5,by omega⟩)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex 3)))
        (quantized (branchMatrix sharp (scalarField x))))) (f x)=_
    rw [quantized_bracket,quantized_bracket]
    rfl


private theorem sign_square (mu : Fin 8) : daggerSign mu*daggerSign mu=1 := by
  unfold daggerSign
  split_ifs <;> norm_num
private theorem dagger_at (mu : Fin 8) (f : QuantumTest) (x : SourceCoordinateSlice) :
    daggerCoefficient false mu f x=quantized (coefficientMatrix false mu (scalarField x)).conjTranspose (f x) := by
  have hd : daggerCoefficient false mu=daggerSign mu • spinClosureCoefficient true mu := rfl
  simp only [hd,LinearMap.smul_apply]
  change daggerSign mu • spinClosureCoefficient true mu f x=_
  rw [core_coefficient_at]
  unfold fiberCoefficient
  rw [matrix_dagger]
  have hs (c : ℂ) (A : Matrix Mode Mode ℂ) : quantized (c • A)=c • quantized A := map_smul quantizer c A
  rw [hs]
  change daggerSign mu • (daggerSign mu • quantized (coefficientMatrix false mu (scalarField x)).conjTranspose (f x))=_
  rw [smul_smul,sign_square,one_smul]
private theorem gamma_dagger_at (mu : Fin 8) (f : QuantumTest) (x : SourceCoordinateSlice) :
    gammaDagger false mu f x=quantized (coefficientMatrix false mu (gammaGradient x)).conjTranspose (f x) := by
  have hd : gammaDagger false mu=daggerSign mu • gammaCore true mu := rfl
  simp only [hd,LinearMap.smul_apply]
  change daggerSign mu • gammaCore true mu f x=_
  rw [original_gamma_core_point]
  unfold fiberCoefficient
  rw [matrix_dagger]
  have hs (c : ℂ) (A : Matrix Mode Mode ℂ) : quantized (c • A)=c • quantized A := map_smul quantizer c A
  rw [hs]
  change daggerSign mu • (daggerSign mu • quantized (coefficientMatrix false mu (gammaGradient x)).conjTranspose (f x))=_
  rw [smul_smul,sign_square,one_smul]

private theorem bracket_at (A B : End) (a b : FiberEnd) (x : SourceCoordinateSlice)
    (hA : ∀ f : QuantumTest,A f x=a (f x)) (hB : ∀ f : QuantumTest,B f x=b (f x)) (f : QuantumTest) :
    bracket A B f x=bracket a b (f x) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,hA,hB,mul_apply_eq_comp]

private theorem weighted_gamma_at (sharp : Bool) (mu : Fin 8) (f : QuantumTest) (x : SourceCoordinateSlice) :
    weightedGamma sharp mu f x=(reciprocalVolume x:ℂ) • fiberCoefficient sharp mu (gammaGradient x) (f x) := by
  change (reciprocalVolume x:ℂ) • gammaCore sharp mu f x=_
  rw [original_gamma_core_point]
private theorem weighted_dagger_at (mu : Fin 8) (f : QuantumTest) (x : SourceCoordinateSlice) :
    weightedGammaDagger false mu f x=(reciprocalVolume x:ℂ) •
      quantized (coefficientMatrix false mu (gammaGradient x)).conjTranspose (f x) := by
  change (reciprocalVolume x:ℂ) • gammaDagger false mu f x=_
  rw [gamma_dagger_at]

private theorem weighted_row_at (mu : Fin 8) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (bracket (daggerCoefficient false mu) (weightedGamma false mu)+
      bracket (spinClosureCoefficient false mu) (weightedGammaDagger false mu)) f x=
        (reciprocalVolume x:ℂ) • quantized (row (coefficientMatrix false mu (scalarField x))
          (coefficientMatrix false mu (gammaGradient x))) (f x) := by
  have h1 := bracket_at (daggerCoefficient false mu) (weightedGamma false mu)
    (quantized (coefficientMatrix false mu (scalarField x)).conjTranspose)
    ((reciprocalVolume x:ℂ) • quantized (coefficientMatrix false mu (gammaGradient x))) x
    (fun f => dagger_at mu f x) (fun f => weighted_gamma_at false mu f x) f
  have h2 := bracket_at (spinClosureCoefficient false mu) (weightedGammaDagger false mu)
    (quantized (coefficientMatrix false mu (scalarField x)))
    ((reciprocalVolume x:ℂ) • quantized (coefficientMatrix false mu (gammaGradient x)).conjTranspose) x
    (fun f => core_coefficient_at false mu f x) (fun f => weighted_dagger_at mu f x) f
  have hb (A B : FiberEnd) (c : ℂ) : bracket A (c • B)=c • bracket A B := by
    simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]
  simp only [hb,quantized_bracket] at h1 h2
  change bracket (daggerCoefficient false mu) (weightedGamma false mu) f x+
    bracket (spinClosureCoefficient false mu) (weightedGammaDagger false mu) f x=_
  rw [h1,h2]
  have ha (A B : Matrix Mode Mode ℂ) : quantized (A+B)=quantized A+quantized B := map_add quantizer A B
  simp only [row,ha,add_apply,smul_apply,smul_add]

/-- The retained principal uses the original Yukawa pair itself; it is still a true full-CAR commutator. -/
def baseWeightedPrincipalCore : End :=
  bracket (fullAction true) (weightedGamma false 0)+bracket (fullAction false) (weightedGamma true 0)

/-- Actual Number-weighted gamma principal collapses before any estimate or clipping. -/
theorem original_weighted_principal_collapse :
    weightedGammaPrincipalCore=(8:ℂ) • baseWeightedPrincipalCore := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  have hb : baseWeightedPrincipalCore f x=(reciprocalVolume x:ℂ) •
      quantized (row (fullMatrix (scalarField x)) (fullMatrix (gammaGradient x))) (f x) := by
    have hD : daggerCoefficient false 0=fullAction true := by
      change (1:ℂ) • fullAction true=fullAction true
      exact one_smul ℂ _
    have hK : spinClosureCoefficient false 0=fullAction false := rfl
    have hG : weightedGammaDagger false 0=weightedGamma true 0 := by
      unfold weightedGammaDagger gammaDagger weightedGamma
      change inverseVolumeAction*((1:ℂ) • gammaCore true 0)=inverseVolumeAction*gammaCore true 0
      rw [one_smul]
    simpa only [hD,hK,hG,show coefficientMatrix false 0 (scalarField x)=fullMatrix (scalarField x) from rfl,
      show coefficientMatrix false 0 (gammaGradient x)=fullMatrix (gammaGradient x) from rfl,
      baseWeightedPrincipalCore] using weighted_row_at 0 f x
  change (∑ mu : Fin 8,(bracket (daggerCoefficient false mu) (weightedGamma false mu)+
    bracket (spinClosureCoefficient false mu) (weightedGammaDagger false mu))) f x=(8:ℂ) • baseWeightedPrincipalCore f x
  let ev : QuantumTest →ₗ[ℂ] FockFiber :=
    { toFun := fun q => q x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hs (q : Fin 8 → QuantumTest) : (∑ mu,q mu) x=∑ mu,q mu x := map_sum ev q Finset.univ
  rw [LinearMap.sum_apply,hs]
  simp only [weighted_row_at,coefficient_row,hb,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℂ 8 _).symm

/-- The original two-sharp source word keeps the complete weighted error after the matrix cancellation. -/
theorem actual_joint_gamma_word_collapsed (m ell : ℕ) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (g : GaussDiagonalHistory.diagonal.domain) :
    (∑ mu : Fin 8,(sourcePair (jointState false m ell F z hz g mu) (gammaWord false m ell F z hz g mu)+
      sourcePair (jointState true m ell F z hz g mu) (gammaWord true m ell F z hz g mu))).im=
      (2*sourceTime 0)*(sourcePair (windowState m ell F z hz g)
        (baseWeightedPrincipalCore (windowState m ell F z hz g))).im-(gammaWeightedError m ell F z hz g).im := by
  rw [actual_joint_gamma_word_form,original_weighted_principal_collapse]
  have hr : (8:ℂ).re=8 := by norm_num
  have hi : (8:ℂ).im=0 := by norm_num
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right,Complex.mul_im,hr,hi,zero_mul,add_zero]
  ring


/-- This is the complete CAR product current, before extracting its anti-Hermitian part. -/
def constantCurrent (phi psi : Scalar) : FiberEnd := ∑ mu : Fin 8,
  ((fiberCoefficient false mu psi).adjoint*fiberCoefficient false mu phi+
    (fiberCoefficient true mu psi).adjoint*fiberCoefficient true mu phi)

private theorem fiber_dagger (mu : Fin 8) (phi : Scalar) :
    fiberCoefficient true mu phi=daggerSign mu • (fiberCoefficient false mu phi).adjoint := by
  unfold fiberCoefficient
  rw [matrix_dagger,quantized_adjoint]
  exact map_smul quantizer _ _

private theorem true_current (mu : Fin 8) (phi psi : Scalar) :
    (fiberCoefficient true mu psi).adjoint*fiberCoefficient true mu phi=
      fiberCoefficient false mu psi*(fiberCoefficient false mu phi).adjoint := by
  rw [fiber_dagger,fiber_dagger]
  by_cases h : 0 < mu.val ∧ mu.val < 5
  · have hs : daggerSign mu= -1 := by unfold daggerSign;rw [if_pos h]
    simp only [hs,neg_one_smul,map_neg,ContinuousLinearMap.adjoint_adjoint,neg_mul,mul_neg,neg_neg]
  · have hs : daggerSign mu=1 := by unfold daggerSign;rw [if_neg h]
    simp only [hs,one_smul,ContinuousLinearMap.adjoint_adjoint]

private theorem current_skew (K M : FiberEnd) :
    (M.adjoint*K+M*K.adjoint)-(M.adjoint*K+M*K.adjoint).adjoint=
      -(bracket K.adjoint M+bracket K M.adjoint) := by
  have h : (M.adjoint*K+M*K.adjoint).adjoint=K.adjoint*M+K*M.adjoint := by
    simp only [map_add,ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]
  rw [h]
  unfold bracket
  noncomm_ring

/-- Only the skew part of the actual CAR product current becomes the one-body source principal. -/
theorem original_constant_current_skew (phi psi : Scalar) :
    constantCurrent phi psi-(constantCurrent phi psi).adjoint=
      (-8:ℂ) • quantized (bracket (fullMatrix phi).conjTranspose (fullMatrix psi)+
        bracket (fullMatrix phi) (fullMatrix psi).conjTranspose) := by
  have hs (mu : Fin 8) :
      ((fiberCoefficient false mu psi).adjoint*fiberCoefficient false mu phi+
        (fiberCoefficient true mu psi).adjoint*fiberCoefficient true mu phi)-
      ((fiberCoefficient false mu psi).adjoint*fiberCoefficient false mu phi+
        (fiberCoefficient true mu psi).adjoint*fiberCoefficient true mu phi).adjoint=
      -quantized (row (coefficientMatrix false mu phi) (coefficientMatrix false mu psi)) := by
    rw [true_current,current_skew]
    simp only [fiberCoefficient,quantized_adjoint,quantized_bracket]
    have ha (A B : Matrix Mode Mode ℂ) : quantized (A+B)=quantized A+quantized B := map_add quantizer A B
    rw [row,ha]
  unfold constantCurrent
  rw [map_sum,←Finset.sum_sub_distrib]
  simp_rw [hs]
  rw [Finset.sum_neg_distrib]
  have hsum (f : Fin 8 → Matrix Mode Mode ℂ) : quantized (∑ mu,f mu)=∑ mu,quantized (f mu) := map_sum quantizer f Finset.univ
  rw [←hsum]
  change -quantized (principalMatrix phi psi)=_
  rw [original_principal_closure_return]
  have hc (c : ℂ) (A : Matrix Mode Mode ℂ) : quantized (c • A)=c • quantized A := map_smul quantizer c A
  rw [hc]
  exact (neg_smul (8:ℂ) (quantized (bracket (fullMatrix phi).conjTranspose (fullMatrix psi)+
    bracket (fullMatrix phi) (fullMatrix psi).conjTranspose))).symm

end LowEnergy.SourceClockYukawaGammaPrincipalCollapse
