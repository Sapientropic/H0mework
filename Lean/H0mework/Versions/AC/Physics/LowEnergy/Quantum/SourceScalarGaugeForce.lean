import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarDoubleGap
import H0mework.Physics.LowEnergy.Quantum.JointCurrentHeisenberg
import H0mework.Physics.Matter.ExteriorMotherLieYukawaDerivation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarGaugeForce
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineHolonomicField StageNineDiracDualYukawaSpinJurisdiction
open StageNineExteriorMotherLieYukawaDerivation SU7MotherLieAlgebra
open SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussDiagonalHistory GaussYukawaCoefficient GaussRadialDomain
open SourceCoframeVolumeCurrent SourceDilationRemainder SourceHamiltonianScaleJet SourceMixedNativeReturn SourceClosedCostNativeProbe
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussNativeMatter GaussQuantumMultiplier SourceScalarDoubleCurrent
open scoped ContDiff InnerProductSpace BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

private theorem internal_dirac (a : SU7MotherLieMatrix) (S : DiracMatrix)
    (f : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction a (diracMatrixMatterAction S f)=
      diracMatrixMatterAction S (diracExteriorMotherLieAction a f) :=
  (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal S (exteriorSpinorMotherLieAction a)) f).symm

private theorem repaired_native (a : SU7MotherLieMatrix) (phi : ExteriorBreakingScalarCarrier)
    (f : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction a (diracDualRightChiralYukawaAction phi f)=
      diracDualRightChiralYukawaAction (exteriorMotherLieAction 4 a phi) f+
        diracDualRightChiralYukawaAction phi (diracExteriorMotherLieAction a f) := by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracExteriorYukawaInternalAction_motherLieAction,internal_dirac]

private theorem hamiltonian_native (a : SU7MotherLieMatrix) (phi : ExteriorBreakingScalarCarrier) :
    diracExteriorMotherLieAction a*LowEnergy.FullQuantum.yukawaHamiltonian phi-
      LowEnergy.FullQuantum.yukawaHamiltonian phi*diracExteriorMotherLieAction a=
      LowEnergy.FullQuantum.yukawaHamiltonian (exteriorMotherLieAction 4 a phi) := by
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LowEnergy.FullQuantum.yukawaHamiltonian,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [internal_dirac,repaired_native,map_add,smul_add,add_sub_cancel_right]

private theorem alg_bracket {R S : Type*} [Ring R] [Ring S] [Algebra ℂ R] [Algebra ℂ S]
    (e : R ≃ₐ[ℂ] S) (A B C : R) (h : A*B-B*A=C) : e A*e B-e B*e A=e C := by
  rw [←map_mul,←map_mul,←map_sub,h]

/-- Actual repaired Yukawa matrix covariance, before taking any chart or Fock quotient. -/
theorem original_matrix_native (a : NativeLie) (phi : Scalar) :
    nativePrimal a*primal phi-primal phi*nativePrimal a=primal (SourceQuantumScalarChart.action phi a) := by
  have hp : scalarCoordinateEquiv.symm (SourceQuantumScalarChart.action phi a)=
      exteriorMotherLieAction 4 (p286LieBlockEmbed (p286CoordinateEquiv.symm a)) (scalarCoordinateEquiv.symm phi) :=
    scalarCoordinateEquiv.symm_apply_apply _
  change LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a)))*
      LowEnergy.Quantum.operatorMatrix (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))-
    LowEnergy.Quantum.operatorMatrix (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))*
      LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a)))=
    LowEnergy.Quantum.operatorMatrix (LowEnergy.FullQuantum.yukawaHamiltonian
      (scalarCoordinateEquiv.symm (SourceQuantumScalarChart.action phi a)))
  rw [hp]
  simpa only using! alg_bracket
    (R := Module.End ℂ DiracExteriorMatterCarrier)
    (S := Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ)
    LowEnergy.Quantum.operatorMatrix _ _ _
    (hamiltonian_native (p286LieBlockEmbed (p286CoordinateEquiv.symm a)) (scalarCoordinateEquiv.symm phi))

private theorem block_bracket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N Y Z : Matrix ι ι ℂ) (h : N*Y-Y*N=Z) :
    Matrix.fromBlocks N 0 0 (N.map (starRingEnd ℂ))*Matrix.fromBlocks Y 0 0 (-(Y.map (starRingEnd ℂ)))-
      Matrix.fromBlocks Y 0 0 (-(Y.map (starRingEnd ℂ)))*Matrix.fromBlocks N 0 0 (N.map (starRingEnd ℂ))=
      Matrix.fromBlocks Z 0 0 (-(Z.map (starRingEnd ℂ))) := by
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,Matrix.mul_neg,Matrix.neg_mul]
  rw [sub_eq_add_neg,Matrix.fromBlocks_neg,Matrix.fromBlocks_add]
  simp only [neg_zero,add_zero,neg_neg]
  congr 1
  have hc := congrArg (fun A : Matrix ι ι ℂ => -(A.map (starRingEnd ℂ))) h
  rw [Matrix.map_sub (starRingEnd ℂ) (map_sub (starRingEnd ℂ)),Matrix.map_mul,Matrix.map_mul] at hc
  exact (by abel : -(N.map (starRingEnd ℂ)*Y.map (starRingEnd ℂ))+
    Y.map (starRingEnd ℂ)*N.map (starRingEnd ℂ)=
    -(N.map (starRingEnd ℂ)*Y.map (starRingEnd ℂ)-Y.map (starRingEnd ℂ)*N.map (starRingEnd ℂ))).trans hc

theorem original_full_matrix_native (a : NativeLie) (phi : Scalar) :
    nativeFull a*fullMatrix phi-fullMatrix phi*nativeFull a=
      fullMatrix (SourceQuantumScalarChart.action phi a) :=
  block_bracket _ _ _ (original_matrix_native a phi)

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

/-- The full original CAR action preserves the actual mother/Yukawa derivation. -/
theorem original_fock_native (a : NativeLie) (phi : Scalar) :
    nativeFock a*sourceMap phi-sourceMap phi*nativeFock a=
      sourceMap (SourceQuantumScalarChart.action phi a) := by
  change quantized (nativeFull a)*quantized (fullMatrix phi)-
    quantized (fullMatrix phi)*quantized (nativeFull a)=quantized (fullMatrix (SourceQuantumScalarChart.action phi a))
  rw [quantized_bracket,original_full_matrix_native]

private theorem fock_skew_operator (a : NativeLie) :
    (nativeFock a).adjoint= -nativeFock a := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right,neg_apply,inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (nativeFock_skew a y x)

/-- The independent adjoint branch has its own exact source covariance. -/
theorem original_branch_native (sharp : Bool) (a : NativeLie) (phi : Scalar) :
    nativeFock a*branchMap sharp phi-branchMap sharp phi*nativeFock a=
      branchMap sharp (SourceQuantumScalarChart.action phi a) := by
  cases sharp
  · exact original_fock_native a phi
  · have h := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (original_fock_native a phi)
    change nativeFock a*(sourceMap phi).adjoint-(sourceMap phi).adjoint*nativeFock a=
      (sourceMap (SourceQuantumScalarChart.action phi a)).adjoint
    simpa only [map_sub,ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,
      fock_skew_operator,ContinuousLinearMap.comp_neg,ContinuousLinearMap.neg_comp,neg_sub_neg] using! h

private theorem full_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (GaussNativePotential.scalarField z) (f z) := by
  cases sharp <;> rfl

private theorem branch_directional (sharp : Bool) (v : Ambient) (f : QuantumTest)
    (z : SourceCoordinateSlice) :
    directional v (SourceMixedNativeReturn.fullAction sharp f) z=
      branchMap sharp (GaussNativePotential.scalarField z) (directional v f z)+
      branchMap sharp ((inverseL z v).2.1 : Scalar) (f z) := by
  let B : SourceCoordinateSlice → FockFiber →L[ℝ] FockFiber := fun w =>
    (branchMap sharp (GaussNativePotential.scalarField w)).restrictScalars ℝ
  have hphi : HasFDerivAt GaussNativePotential.scalarField GaussRadialMomentum.scalarCoordinate z := by
    simpa only using! (GaussRadialMomentum.scalarCoordinate.hasFDerivAt (x := z)).const_add vacuum
  have hB := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).hasFDerivAt.comp z
    ((branchMap sharp).hasFDerivAt.comp z hphi)
  have hf := f.contDiff.differentiable (by simp)
  have he : (SourceMixedNativeReturn.fullAction sharp f : SourceCoordinateSlice → FockFiber)=fun w => B w (f w) := by
    funext w
    cases sharp <;> rfl
  have hd := (hB.clm_apply (hf z).hasFDerivAt).fderiv
  change fderiv ℝ (fun w => B w (f w)) z=_ at hd
  rw [directional_apply,he,hd]
  change branchMap sharp (GaussNativePotential.scalarField z) (fderiv ℝ f z (direction v z))+
    branchMap sharp ((direction v z).2.1 : Scalar) (f z)=_
  rfl

/-- The inverse chart and the source connection cancel in the full covariant derivative. -/
theorem original_full_momentum (sharp : Bool) (v : Ambient) (f : QuantumTest) :
    covariantMomentum v (SourceMixedNativeReturn.fullAction sharp f)=
      SourceMixedNativeReturn.fullAction sharp (covariantMomentum v f)+
        (-Complex.I) • constantAction sharp v.1 f := by
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hi := congrArg Prod.fst (inverse_right ⟨z,hz⟩ v)
    change SourceQuantumScalarChart.action (GaussNativePotential.scalarField z) (inverseL z v).1+
      ((inverseL z v).2.1 : Scalar)=v.1 at hi
    have hn := congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
      (original_branch_native sharp (inverseL z v).1 (GaussNativePotential.scalarField z))
    have hs := congrArg (fun phi : Scalar => branchMap sharp phi (f z)) hi
    simp only [map_add,add_apply] at hs
    change nativeFock (inverseL z v).1 (branchMap sharp (GaussNativePotential.scalarField z) (f z))-
      branchMap sharp (GaussNativePotential.scalarField z) (nativeFock (inverseL z v).1 (f z))=
      branchMap sharp (SourceQuantumScalarChart.action (GaussNativePotential.scalarField z) (inverseL z v).1) (f z) at hn
    change covariantMomentum v (SourceMixedNativeReturn.fullAction sharp f) z=
      SourceMixedNativeReturn.fullAction sharp (covariantMomentum v f) z+
        (-Complex.I) • constantAction sharp v.1 f z
    rw [covariantMomentum_apply,full_apply,full_apply]
    change (-Complex.I) • (directional v (SourceMixedNativeReturn.fullAction sharp f) z+
      nativeFock (inverseL z v).1 (branchMap sharp (GaussNativePotential.scalarField z) (f z)))=
      branchMap sharp (GaussNativePotential.scalarField z)
        ((-Complex.I) • (directional v f z+nativeFock (inverseL z v).1 (f z)))+
        (-Complex.I) • branchMap sharp v.1 (f z)
    rw [branch_directional,map_smul,map_add,←smul_add]
    congr 1
    have hn' := eq_add_of_sub_eq hn
    rw [hn']
    exact (by abel : _=branchMap sharp (GaussNativePotential.scalarField z) (directional v f z)+
      branchMap sharp (GaussNativePotential.scalarField z) (nativeFock (inverseL z v).1 (f z))+
      (branchMap sharp (SourceQuantumScalarChart.action (GaussNativePotential.scalarField z) (inverseL z v).1) (f z)+
        branchMap sharp ((inverseL z v).2.1 : Scalar) (f z))).trans (congrArg (fun y : FockFiber =>
          branchMap sharp (GaussNativePotential.scalarField z) (directional v f z)+
          branchMap sharp (GaussNativePotential.scalarField z) (nativeFock (inverseL z v).1 (f z))+y) hs)
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

theorem original_gauge_full (sharp : Bool) (v : Ambient) (hv : v.1=0) :
    Commute (covariantMomentum v) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  have h := original_full_momentum sharp v f
  have hc : constantAction sharp v.1=0 := by
    rw [hv]
    apply LinearMap.ext
    intro q
    apply DFunLike.ext
    intro z
    exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (q z)) (map_zero (branchMap sharp))
  simpa only [hc,LinearMap.zero_apply,smul_zero,add_zero] using! h

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem full_real (sharp : Bool) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • SourceMixedNativeReturn.fullAction sharp f z=
    SourceMixedNativeReturn.fullAction sharp (multiply c hc f) z
  rw [full_apply,full_apply]
  exact (map_smul (branchMap sharp (GaussNativePotential.scalarField z)) (c z : ℂ) (f z)).symm

theorem original_gauge_full_adjoint (sharp : Bool) (v : Ambient) (hv : v.1=0) :
    Commute (GaussMomentumAdjoint.adjoint v) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have he := LinearMap.congr_fun (original_gauge_full (!sharp) v hv).eq f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (SourceMixedNativeReturn.fullAction sharp g))=
    sourcePair f (SourceMixedNativeReturn.fullAction sharp (GaussMomentumAdjoint.adjoint v g))
  calc
    _=sourcePair (covariantMomentum v f) (SourceMixedNativeReturn.fullAction sharp g) := GaussNativeForm.adjoint_pair _ _ _
    _=sourcePair (SourceMixedNativeReturn.fullAction (!sharp) (covariantMomentum v f)) g := full_pair _ _ _
    _=sourcePair (covariantMomentum v (SourceMixedNativeReturn.fullAction (!sharp) f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) (GaussMomentumAdjoint.adjoint v g) :=
      (GaussNativeForm.adjoint_pair _ _ _).symm
    _=_ := (full_pair _ _ _).symm

private theorem commute_mul {R : Type*} [Ring R] (A B C : R) (hA : Commute A C) (hB : Commute B C) :
    Commute (A*B) C := hA.mul_left hB

private theorem commute_right_product {R : Type*} [Ring R] (A B C : R)
    (hB : Commute A B) (hC : Commute A C) : Commute A (B*C) := hB.mul_right hC

private theorem commute_sum {R : Type*} [Ring R] {ι : Type*} [Fintype ι]
    (A : ι → R) (B : R) (h : ∀ i,Commute (A i) B) : Commute (∑ i,A i) B :=
  Commute.sum_left Finset.univ A B (fun i _ => h i)

private theorem commute_smul {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (c : ℂ) (A B : R) (h : Commute A B) :
    Commute (c • A) B := h.smul_left c

private theorem commute_add {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A+B) C := hA.add_left hB

/-- Original gauge kinetic action commutes with both complete Yukawa branches, including vacuum. -/
theorem original_electric_full (sharp : Bool) :
    Commute gaugeKinetic (SourceMixedNativeReturn.fullAction sharp) := by
  unfold gaugeKinetic
  apply commute_smul (R := CoreEnd)
  apply commute_sum (R := CoreEnd)
  intro a
  apply commute_sum (R := CoreEnd)
  intro i
  apply commute_sum (R := CoreEnd)
  intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) _
  exact commute_mul (R := CoreEnd) _ _ _ (original_gauge_full_adjoint sharp _ rfl)
    (commute_mul (R := CoreEnd) _ _ _ (full_real sharp _ _) (original_gauge_full sharp _ rfl))

private theorem polynomial_commute {R : Type*} [Ring R] (A B : R) (m ell : ℕ) (h : Commute A B) :
    Commute A ((1-B)^(m+1)-(1-B)^(ell+1)) :=
  ((Commute.one_right A).sub_right h |>.pow_right _).sub_right
    ((Commute.one_right A).sub_right h |>.pow_right _)

/-- The actual signed spatial potential is retained and commutes as its original real multiplier. -/
theorem original_electric_insertion (sharp : Bool) (m ell : ℕ) :
    Commute electricSpatial (fullInsertion sharp m ell) := by
  have hg : Commute gaugeKinetic (fullInsertion sharp m ell) :=
    commute_right_product (R := CoreEnd) _ _ _ (original_electric_full sharp)
      (polynomial_commute (R := CoreEnd) _ _ m ell GaussRadialHamiltonian.gauge_commutes)
  have hs : Commute spatialAction (fullInsertion sharp m ell) :=
    commute_right_product (R := CoreEnd) _ _ _ (full_real sharp spatialPotential spatial_smooth)
      (polynomial_commute (R := CoreEnd) _ _ m ell (GaussRadialHamiltonian.real_commutes _ _))
  exact commute_add (R := CoreEnd) _ _ _ hg hs

private theorem mixed_reduce {R : Type*} [Ring R] [Module ℂ R]
    (E M X : R) (h : Commute E X) :
    bracket M (bracket E X)+bracket E (bracket M X)+(4 : ℂ) • bracket E (bracket E X)=
      bracket E (bracket M X) := by
  have hz : bracket E X=0 := sub_eq_zero.mpr h.eq
  rw [hz]
  simp only [bracket,mul_zero,zero_mul,sub_self,zero_add,smul_zero,add_zero]

/-- Two actual force blocks vanish by the source gauge/Yukawa law; the complete mixed matter current survives. -/
theorem original_electric_matter_current (sharp : Bool) (m ell : ℕ) :
    electricMatterCurrent (fullInsertion sharp m ell)=
      bracket (R := CoreEnd) electricSpatial
        (bracket (R := CoreEnd) GaussMatterCore.matterAction (fullInsertion sharp m ell)) :=
  mixed_reduce (R := CoreEnd) _ _ _ (original_electric_insertion sharp m ell)

/-- The original gapped force consumes the newly generated gauge cancellation, with every other source term unchanged. -/
theorem actual_gapped_force_return (sharp : Bool) (m ell : ℕ) (F : GaussUnitaryHistory.Index)
    (g : diagonal.domain) :
    compressedOscillatorForce sharp m ell F g=
      sourceRead F g (
        bracket (R := CoreEnd) electricSpatial
          (bracket (R := CoreEnd) GaussMatterCore.matterAction (fullInsertion sharp m ell))-
        (2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
        (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
        (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-doubleProjectionFlux sharp m ell F g := by
  unfold compressedOscillatorForce oscillatorForce
  rw [original_electric_matter_current]

end LowEnergy.SourceScalarGaugeForce
