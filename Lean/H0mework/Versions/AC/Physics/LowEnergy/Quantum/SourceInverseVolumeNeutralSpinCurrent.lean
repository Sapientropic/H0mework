import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralScalarCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseNeutralSpinCurrent
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
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead defectAction compressionCore
  SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion
  neutralCurrent scalarNeutral scalarCurrent radialCurrent coframeReducedRemainder scalarReducedRemainder
  GaussCoframeForm.spinSquare GaussCoframeForm.numberShift

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) : Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z : ℂ) (f z)).symm

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm



private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g


private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  cases sharp <;> rfl



private theorem spatial_spin_full (j : Fin 3) (sharp : Bool) :
    Commute (GaussCoframeSpin.current ⟨j.val+3,by omega⟩) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change quantized (GaussCoframeSpin.full ⟨j.val+3,by omega⟩) (SourceMixedNativeReturn.fullAction sharp f z)=
    SourceMixedNativeReturn.fullAction sharp (GaussCoframeSpin.current ⟨j.val+3,by omega⟩ f) z
  rw [full_at,full_at]
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
    (original_spatial_spin_branch j sharp (scalarField z)).eq


private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)


private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem number_at (f : QuantumTest) (z : SourceCoordinateSlice) :
    GaussCoframeForm.number f z=fiberNumber (f z) := by
  apply PiLp.ext
  intro word
  exact (GaussCoframeForm.number_apply f z word).trans (fiberNumber_apply (f z) word).symm

private theorem number_false : Commute GaussCoframeForm.number (SourceMixedNativeReturn.fullAction false) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeForm.number (SourceMixedNativeReturn.fullAction false f) z=
    SourceMixedNativeReturn.fullAction false (GaussCoframeForm.number f) z
  rw [number_at,full_at,full_at,number_at]
  change fiberNumber (sourceMap (scalarField z) (f z))=sourceMap (scalarField z) (fiberNumber (f z))
  rw [source_map_return]
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) (number_commute _).eq

/-- The actual full Yukawa action preserves the original CAR number, on both independent-dual branches. -/
theorem original_number_full (sharp : Bool) :
    Commute GaussCoframeForm.number (SourceMixedNativeReturn.fullAction sharp) := by
  cases sharp
  · exact number_false
  · apply LinearMap.ext
    intro g
    apply SourceCoframeVolume.pair_ext
    intro f
    change sourcePair f (GaussCoframeForm.number (SourceMixedNativeReturn.fullAction true g))=
      sourcePair f (SourceMixedNativeReturn.fullAction true (GaussCoframeForm.number g))
    rw [GaussCoframeForm.number_pair,full_pair,full_pair,GaussCoframeForm.number_pair]
    exact congrArg (fun q : QuantumTest => sourcePair q g) (LinearMap.congr_fun number_false.eq f).symm

private theorem number_shift_full (sharp : Bool) :
    Commute GaussCoframeForm.numberShift (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeForm.numberShift
  simp only [←Module.End.mul_eq_comp]
  exact (((original_number_full sharp).mul_left (real_full _ _ sharp)).add_left
    ((real_full _ _ sharp).mul_left (original_number_full sharp))).smul_left _

/-- Each actual spatial square commutes; boost and chirality rows are not dropped. -/
theorem original_spatial_square_full (j : Fin 3) (sharp : Bool) :
    Commute (GaussCoframeForm.spinSquare ⟨j.val+3,by omega⟩) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeForm.spinSquare
  simp only [←Module.End.mul_eq_comp]
  exact ((spatial_spin_full j sharp).mul_left ((real_full _ _ sharp).mul_left (spatial_spin_full j sharp))).smul_left _

def fourPotential : End := GaussCoframeForm.spinSquare 0+GaussCoframeForm.spinSquare 1+
  GaussCoframeForm.spinSquare 2+GaussCoframeForm.spinSquare 6

def fourCurrent (sharp : Bool) : End := bracket fourPotential (SourceMixedNativeReturn.fullAction sharp)

private theorem bracket_add {R : Type*} [Ring R] (A B C : R) :
    bracket (A+B) C=bracket A C+bracket B C := by unfold bracket;noncomm_ring

private theorem bracket_commute {R : Type*} [Ring R] {A B : R} (h : Commute A B) : bracket A B=0 :=
  sub_eq_zero.mpr h.eq

/-- The full seven-square/number source reduces to its three boosts and chirality row. -/
theorem original_spin_four_return (sharp : Bool) : spinCurrent sharp=fourCurrent sharp := by
  have hs : spinPotential=fourPotential+
      (GaussCoframeForm.spinSquare 3+GaussCoframeForm.spinSquare 4+GaussCoframeForm.spinSquare 5)+
      GaussCoframeForm.numberShift := by
    simp only [spinPotential,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change GaussCoframeForm.spinSquare 0+(GaussCoframeForm.spinSquare 1+
      (GaussCoframeForm.spinSquare 2+(GaussCoframeForm.spinSquare 3+
      (GaussCoframeForm.spinSquare 4+(GaussCoframeForm.spinSquare 5+GaussCoframeForm.spinSquare 6)))))+
      GaussCoframeForm.numberShift=_
    unfold fourPotential
    abel
  have h3 : Commute (GaussCoframeForm.spinSquare 3) (SourceMixedNativeReturn.fullAction sharp) := original_spatial_square_full 0 sharp
  have h4 : Commute (GaussCoframeForm.spinSquare 4) (SourceMixedNativeReturn.fullAction sharp) := original_spatial_square_full 1 sharp
  have h5 : Commute (GaussCoframeForm.spinSquare 5) (SourceMixedNativeReturn.fullAction sharp) := original_spatial_square_full 2 sharp
  have hr := (h3.add_left h4).add_left h5
  unfold spinCurrent
  rw [hs]
  rw [bracket_add,bracket_add,bracket_commute hr,bracket_commute (number_shift_full sharp),add_zero,add_zero]
  rfl


def activeIndex (j : Fin 4) : Fin 7 := if h : j.val<3 then ⟨j.val,by omega⟩ else 6

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

private theorem double_ladder {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (S Y : R)
    (hs : S*S=(1/4 : ℂ) • (1 : R)) (hy : S*Y+Y*S=0) :
    bracket S (bracket S Y)=Y := by
  unfold bracket
  have h1 := congrArg (fun A : R => A*Y) hs
  have h2 := congrArg (fun A : R => Y*A) hs
  have h3 := congrArg (fun A : R => S*A) hy
  simp only [mul_add,mul_sub,sub_mul,mul_zero,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,mul_assoc] at h1 h2 h3 ⊢
  linear_combination (norm := module) (3 : ℂ) • h1+h2-(2 : ℂ) • h3
private theorem primal_ladder (j : Fin 4) (phi : Scalar) :
    bracket (GaussCoframeSpin.primal (activeIndex j))
      (bracket (GaussCoframeSpin.primal (activeIndex j)) (GaussYukawaCoefficient.primal phi))=
      GaussYukawaCoefficient.primal phi := by
  have hs := congrArg diracMap (active_square j)
  simp only [map_smul,dirac_map_mul,dirac_map_one] at hs
  have hd := double_ladder (R := Module.End ℂ DiracExteriorMatterCarrier) _ _ hs (active_yukawa_anti j (scalarCoordinateEquiv.symm phi))
  have hm := congrArg LowEnergy.Quantum.operatorMatrix hd
  have he (A : DiracMatrix) : LowEnergy.Quantum.operatorMatrix (diracMap A)=GaussCoframeSpin.spinLift A :=
    GaussCoframeSpin.spinLift_source A
  simp only [bracket,map_mul,map_sub,he] at hm
  exact hm

private theorem block_ladder {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℂ) :
    bracket (Matrix.fromBlocks A 0 0 C) (bracket (Matrix.fromBlocks A 0 0 C) (Matrix.fromBlocks B 0 0 D))=
      Matrix.fromBlocks (bracket A (bracket A B)) 0 0 (bracket C (bracket C D)) := by
  simp only [bracket,sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add,neg_zero,add_zero,
    Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,zero_add]

private theorem full_matrix_ladder (j : Fin 4) (phi : Scalar) :
    bracket (GaussCoframeSpin.full (activeIndex j))
      (bracket (GaussCoframeSpin.full (activeIndex j)) (GaussYukawaCoefficient.fullMatrix phi))=
      GaussYukawaCoefficient.fullMatrix phi := by
  have hp := primal_ladder j phi
  have hd := congrArg ((starRingEnd ℂ).mapMatrix : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ →+* _) hp
  simp only [bracket,map_sub,map_mul] at hd
  change (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*
    ((GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)-
    (GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))-
    ((GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)*(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)-
    (GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)*(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))*
    (GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ)=(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ) at hd
  change bracket (GaussCoframeSpin.full (activeIndex j))
    (bracket (GaussCoframeSpin.full (activeIndex j))
      (Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))))=
    Matrix.fromBlocks (GaussYukawaCoefficient.primal phi) 0 0 (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ))
  unfold GaussCoframeSpin.full
  split_ifs
  · have hdual : bracket ((GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))
        (bracket ((GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))
          (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)))=-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ) := by
      unfold bracket
      linear_combination (norm := noncomm_ring) -hd
    exact (block_ladder _ _ _ _).trans (congrArg₂ (fun A B => Matrix.fromBlocks A 0 0 B) hp hdual)
  · have hdual : bracket (-(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))
        (bracket (-(GaussCoframeSpin.primal (activeIndex j)).map (starRingEnd ℂ))
          (-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ)))=-(GaussYukawaCoefficient.primal phi).map (starRingEnd ℂ) := by
      unfold bracket
      linear_combination (norm := noncomm_ring) -hd
    exact (block_ladder _ _ _ _).trans (congrArg₂ (fun A B => Matrix.fromBlocks A 0 0 B) hp hdual)

private theorem fock_ladder (j : Fin 4) (phi : Scalar) :
    bracket (quantized (GaussCoframeSpin.full (activeIndex j)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (sourceMap phi))=sourceMap phi := by
  change bracket (quantized (GaussCoframeSpin.full (activeIndex j)))
    (bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (quantized (GaussYukawaCoefficient.fullMatrix phi)))=
    quantized (GaussYukawaCoefficient.fullMatrix phi)
  simp only [bracket,quantized_bracket]
  exact congrArg quantized (full_matrix_ladder j phi)

private theorem reverse_ladder {R : Type*} [Ring R] (S Y : R)
    (h : (Y*S-S*Y)*S-S*(Y*S-S*Y)=Y) : bracket S (bracket S Y)=Y := by
  unfold bracket
  linear_combination (norm := noncomm_ring) h

/-- The original full-CAR boost and chiral adjoint actions close after two steps on either source branch. -/
theorem original_active_spin_ladder (j : Fin 4) (sharp : Bool) (phi : Scalar) :
    bracket (quantized (GaussCoframeSpin.full (activeIndex j)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (branchMap sharp phi))=branchMap sharp phi := by
  cases sharp
  · exact fock_ladder j phi
  · have hs : (quantized (GaussCoframeSpin.full (activeIndex j))).adjoint=
        quantized (GaussCoframeSpin.full (activeIndex j)) := by
      rw [quantized_adjoint,GaussCoframeSpin.full_hermitian]
    have h := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (fock_ladder j phi)
    simp only [bracket,map_sub,ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,hs] at h
    change bracket (quantized (GaussCoframeSpin.full (activeIndex j)))
      (bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (sourceMap phi).adjoint)=(sourceMap phi).adjoint
    change ((sourceMap phi).adjoint*quantized (GaussCoframeSpin.full (activeIndex j))-
      quantized (GaussCoframeSpin.full (activeIndex j))*(sourceMap phi).adjoint)*
      quantized (GaussCoframeSpin.full (activeIndex j))-
      quantized (GaussCoframeSpin.full (activeIndex j))*
      ((sourceMap phi).adjoint*quantized (GaussCoframeSpin.full (activeIndex j))-
        quantized (GaussCoframeSpin.full (activeIndex j))*(sourceMap phi).adjoint)=(sourceMap phi).adjoint at h
    exact reverse_ladder _ _ h


def branchMatrix (sharp : Bool) (phi : Scalar) : Matrix Mode Mode ℂ :=
  if sharp then (GaussYukawaCoefficient.fullMatrix phi).conjTranspose else GaussYukawaCoefficient.fullMatrix phi

/-- Each intermediate variation is one actual CAR matrix current, not a product of two Fock readers. -/
theorem original_active_spin_matrix (j : Fin 4) (sharp : Bool) (phi : Scalar) :
    bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (branchMap sharp phi)=
      quantized (bracket (GaussCoframeSpin.full (activeIndex j)) (branchMatrix sharp phi)) := by
  cases sharp
  · change quantized _*quantized _-quantized _*quantized _=quantized _
    exact quantized_bracket _ _
  · change bracket (quantized (GaussCoframeSpin.full (activeIndex j))) (sourceMap phi).adjoint=_
    have hy : sourceMap phi=quantized (GaussYukawaCoefficient.fullMatrix phi) := rfl
    rw [hy,quantized_adjoint]
    exact quantized_bracket _ _

def activeSpin (j : Fin 4) : End := GaussCoframeSpin.current (activeIndex j)
def spinVariation (sharp : Bool) (j : Fin 4) : End := bracket (activeSpin j) (SourceMixedNativeReturn.fullAction sharp)
def spinVolume : End := multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth

def reducedSpinCurrent (sharp : Bool) : End := (3/2 : ℂ) • (spinVolume*
  (spinVariation sharp 3*activeSpin 3-spinVariation sharp 0*activeSpin 0-
    spinVariation sharp 1*activeSpin 1-spinVariation sharp 2*activeSpin 2-SourceMixedNativeReturn.fullAction sharp))

private theorem spin_at (j : Fin 4) (f : QuantumTest) (z : SourceCoordinateSlice) :
    activeSpin j f z=quantized (GaussCoframeSpin.full (activeIndex j)) (f z) := rfl

private theorem core_ladder (j : Fin 4) (sharp : Bool) :
    bracket (activeSpin j) (spinVariation sharp j)=SourceMixedNativeReturn.fullAction sharp := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have h := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
    (original_active_spin_ladder j sharp (scalarField z))
  simpa only [spinVariation,bracket,LinearMap.sub_apply,Module.End.mul_apply,sub_apply,
    spin_at,full_at,map_sub,mul_apply_eq_comp] using h

private theorem anticommutator_ladder {R : Type*} [Ring R] [Module ℂ R] (S Y : R)
    (h : bracket S (bracket S Y)=Y) :
    S*bracket S Y+bracket S Y*S=(2 : ℂ) • (bracket S Y*S)+Y := by
  change S*bracket S Y-bracket S Y*S=Y at h
  linear_combination (norm := module) h

private theorem square_coefficient {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (c : ℂ) (S V Y : R) (hVS : Commute V S) (hVY : Commute V Y) :
    bracket (c • (S*(V*S))) Y=c • (V*(S*bracket S Y+bracket S Y*S)) := by
  have hp : S*(V*S)=V*(S*S) := by rw [←mul_assoc,←hVS.eq,mul_assoc]
  rw [hp]
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,←smul_sub]
  congr 1
  linear_combination (norm := noncomm_ring) hVY.eq*(S*S)

private theorem volume_spin (a : Fin 7) : Commute spinVolume (GaussCoframeSpin.current a) := by
  unfold spinVolume GaussCoframeSpin.current GaussQuantumMultiplier.action
  exact real_local _ _ _ _

private theorem active_weight (j : Fin 4) :
    (GaussCoframeForm.spinWeight (activeIndex j) : ℂ)=if j.val<3 then (-3/4 : ℂ) else (3/4 : ℂ) := by
  fin_cases j
  · change ((-3/4 : ℝ) : ℂ)=(-3/4 : ℂ)
    push_cast
    rfl
  · change ((-3/4 : ℝ) : ℂ)=(-3/4 : ℂ)
    push_cast
    rfl
  · change ((-3/4 : ℝ) : ℂ)=(-3/4 : ℂ)
    push_cast
    rfl
  · change ((3/4 : ℝ) : ℂ)=(3/4 : ℂ)
    push_cast
    rfl

private theorem active_square_return (j : Fin 4) (sharp : Bool) :
    bracket (GaussCoframeForm.spinSquare (activeIndex j)) (SourceMixedNativeReturn.fullAction sharp)=
      (if j.val<3 then (-3/4 : ℂ) else (3/4 : ℂ)) •
        (spinVolume*((2 : ℂ) • (spinVariation sharp j*activeSpin j)+SourceMixedNativeReturn.fullAction sharp)) := by
  have hs := square_coefficient (R := End) (GaussCoframeForm.spinWeight (activeIndex j) : ℂ)
    (activeSpin j) spinVolume (SourceMixedNativeReturn.fullAction sharp)
    (volume_spin _) (real_full _ _ sharp)
  have hl := anticommutator_ladder (R := End) _ _ (core_ladder j sharp)
  have hc := congrArg (fun A : End => (GaussCoframeForm.spinWeight (activeIndex j) : ℂ) • (spinVolume*A)) hl
  have h := hs.trans hc
  rw [active_weight] at h
  simpa only [GaussCoframeForm.spinSquare,activeSpin,spinVolume,spinVariation,←Module.End.mul_eq_comp,active_weight] using h

private theorem collect_four {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (V Y Z0 Z1 Z2 Z3 A0 A1 A2 A3 : R)
    (h0 : A0=(-3/4 : ℂ) • (V*((2 : ℂ) • Z0+Y)))
    (h1 : A1=(-3/4 : ℂ) • (V*((2 : ℂ) • Z1+Y)))
    (h2 : A2=(-3/4 : ℂ) • (V*((2 : ℂ) • Z2+Y)))
    (h3 : A3=(3/4 : ℂ) • (V*((2 : ℂ) • Z3+Y))) :
    A0+A1+A2+A3=(3/2 : ℂ) • (V*(Z3-Z0-Z1-Z2-Y)) := by
  rw [h0,h1,h2,h3]
  simp only [mul_add,mul_sub,mul_smul_comm]
  module

/-- The zero-order source has no number term or spatial-square reader; four single CAR variations and one Y term remain. -/
theorem original_spin_ladder_return (sharp : Bool) : spinCurrent sharp=reducedSpinCurrent sharp := by
  have h0 : bracket (GaussCoframeForm.spinSquare 0) (SourceMixedNativeReturn.fullAction sharp)=
      (-3/4 : ℂ) • (spinVolume*((2 : ℂ) • (spinVariation sharp 0*activeSpin 0)+SourceMixedNativeReturn.fullAction sharp)) :=
    active_square_return 0 sharp
  have h1 : bracket (GaussCoframeForm.spinSquare 1) (SourceMixedNativeReturn.fullAction sharp)=
      (-3/4 : ℂ) • (spinVolume*((2 : ℂ) • (spinVariation sharp 1*activeSpin 1)+SourceMixedNativeReturn.fullAction sharp)) :=
    active_square_return 1 sharp
  have h2 : bracket (GaussCoframeForm.spinSquare 2) (SourceMixedNativeReturn.fullAction sharp)=
      (-3/4 : ℂ) • (spinVolume*((2 : ℂ) • (spinVariation sharp 2*activeSpin 2)+SourceMixedNativeReturn.fullAction sharp)) :=
    active_square_return 2 sharp
  have h3 : bracket (GaussCoframeForm.spinSquare 6) (SourceMixedNativeReturn.fullAction sharp)=
      (3/4 : ℂ) • (spinVolume*((2 : ℂ) • (spinVariation sharp 3*activeSpin 3)+SourceMixedNativeReturn.fullAction sharp)) :=
    active_square_return 3 sharp
  rw [original_spin_four_return]
  unfold fourCurrent fourPotential reducedSpinCurrent
  simp only [bracket_add]
  exact collect_four _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3

def spinNeutral (sharp : Bool) (m ell : ℕ) : End :=
  (scalarCurrent sharp+reducedSpinCurrent sharp)*SourceMixedNativeReturn.thetaAction m ell+
    SourceMixedNativeReturn.fullAction sharp*radialCurrent m ell

private theorem neutral_return (sharp : Bool) (m ell : ℕ) : scalarNeutral sharp m ell=spinNeutral sharp m ell := by
  unfold scalarNeutral spinNeutral
  rw [original_spin_ladder_return]

def spinReducedRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  -(1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z
    (bracket (defectAction F) (spinNeutral sharp m ell)) a 0 0 0)+
  (1/48 : ℂ) • coframeRest (fun a =>
    inverseCross F seed z (bracket diagonalAction (spinNeutral sharp m ell)) a 0+
      finiteResolvent F z*inputFlux F seed (bracket diagonalAction (spinNeutral sharp m ell)) a 0*finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z

/-- The original joint remainder consumes the four-current source reduction at the same F, seed and frequency. -/
theorem actual_spin_ward_remainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) :
    scalarReducedRemainder sharp m ell F seed z=spinReducedRemainder sharp m ell F seed z := by
  unfold scalarReducedRemainder spinReducedRemainder
  exact congrArg (fun Q : End =>
    -(1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z (bracket (defectAction F) Q) a 0 0 0)+
    (1/48 : ℂ) • coframeRest (fun a => inverseCross F seed z (bracket diagonalAction Q) a 0+
      finiteResolvent F z*inputFlux F seed (bracket diagonalAction Q) a 0*finiteResolvent F z)+
    finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
      (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z)
    (neutral_return sharp m ell)

end LowEnergy.SourceInverseNeutralSpinCurrent
