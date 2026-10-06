import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeMagneticForceLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseMagneticForceCancellation
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceMixedNativeReturn
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open SourceInverseGaugeSingleDefectJoin SourceInverseHamiltonianForceReduction
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCartanCubic GaussLiveMomentum
open SaturationMonoid.PhysicsCore DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineHolonomicField StageNineDiracDualYukawaSpinJurisdiction
open GaussYukawaCoefficient SourceInverseMagneticForceLocalization SU7ExteriorBreakingYukawa StageNineDynamicBreakingVacuum
open FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets SourceGaugeCoframeJets SourceScalarForceBudget
open SourceInverseCompressionGaugeSplice
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
open scoped ContDiff InnerProductSpace Matrix
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  sourceRead state defectAction compressionCore magneticAction
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent matterInsertion neutralCurrent kineticMagneticForce

private theorem magnetic_smooth (z : physicalChart) : ContDiffAt ℝ ∞ magneticPotential z.val := by
  have hm (i j : Fin 3) := (inverseSpatial_smooth i j z).mul
    ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt)
  exact (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hm i j)

private theorem native_pair_skew (a b c : NativeLie) :
    inner ℝ (nativeBracket a b) c= -inner ℝ b (nativeBracket a c) := SourceCartanCubic.pair_skew a b c

private theorem native_derivation (a b c : NativeLie) :
    nativeBracket a (nativeBracket b c)=nativeBracket (nativeBracket a b) c+nativeBracket b (nativeBracket a c) :=
  SourceCartanCubic.bracket_derivation a b c

/-- The original inverse-chart scalar direction differentiates the magnetic connection only along its true gauge orbit. -/
private theorem scalar_connection_derivative (v : Ambient) (hv : v.2=0) (z : physicalChart) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => connectionField (z.val+r • direction v z.val) i)
      (-(nativeBracket (inverseL z.val v).1 (connectionField z.val i))) 0 := by
  let C : SourceCoordinateSlice →L[ℝ] NativeLie := (gaugeCoordinate i).toContinuousLinearMap.comp
    (coordinateSlice.subtypeL.comp ((ContinuousLinearMap.snd ℝ scalarSlice coordinateSlice).comp
      (ContinuousLinearMap.snd ℝ Coframe (scalarSlice × coordinateSlice))))
  have hg : HasDerivAt (fun r : ℝ => z.val+r • direction v z.val) (direction v z.val) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z.val)).const_add z.val
  have hc := C.hasFDerivAt.comp_hasDerivAt 0 hg
  have hi := congrArg Prod.snd (inverse_right z v)
  change nativeGauge (inverseL z.val v).1 (z.val.2.2 : Gauge)+((inverseL z.val v).2.2 : Gauge)=v.2 at hi
  rw [hv] at hi
  have hcoord := congrArg (gaugeCoordinate i) hi
  simp only [map_add,map_zero] at hcoord
  change nativeBracket (inverseL z.val v).1 (connectionField z.val i)+
    gaugeCoordinate i ((inverseL z.val v).2.2 : Gauge)=0 at hcoord
  have he : C (direction v z.val)= -nativeBracket (inverseL z.val v).1 (connectionField z.val i) :=
    eq_neg_of_add_eq_zero_right hcoord
  rw [he] at hc
  exact hc

private theorem bilinear_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E →L[ℝ] E) {f g : ℝ → E} {df dg : E}
    (hf : HasDerivAt f df 0) (hg : HasDerivAt g dg 0) :
    HasDerivAt (fun r => L (f r) (g r)) (L (f 0) dg+L df (g 0)) 0 :=
  by simpa only [Function.comp_apply,add_comm] using (L.hasFDerivAt.comp_hasDerivAt 0 hf).clm_apply hg

private theorem scalar_magnetic_field (v : Ambient) (hv : v.2=0) (z : physicalChart) (i : Fin 3) :
    HasDerivAt (fun r : ℝ => magneticField (z.val+r • direction v z.val) i)
      (-nativeBracket (inverseL z.val v).1 (magneticField z.val i)) 0 := by
  let a := (inverseL z.val v).1
  let L : NativeLie →L[ℝ] NativeLie →L[ℝ] NativeLie := nativeBracket.toContinuousBilinearMap
  have h (j k : Fin 3) : HasDerivAt
      (fun r : ℝ => nativeBracket (connectionField (z.val+r • direction v z.val) j)
        (connectionField (z.val+r • direction v z.val) k))
      (-nativeBracket a (nativeBracket (connectionField z.val j) (connectionField z.val k))) 0 := by
    have hj := scalar_connection_derivative v hv z j
    have hk := scalar_connection_derivative v hv z k
    have hd := bilinear_derivative L hj hk
    have he : L (connectionField z.val j) (-nativeBracket a (connectionField z.val k))+
        L (-nativeBracket a (connectionField z.val j)) (connectionField z.val k)=
        -nativeBracket a (nativeBracket (connectionField z.val j) (connectionField z.val k)) := by
      change nativeBracket _ (-nativeBracket a _)+nativeBracket (-nativeBracket a _) _=_
      simp only [map_neg,LinearMap.neg_apply]
      linear_combination (norm := module) (native_derivation a (connectionField z.val j) (connectionField z.val k))
    simp only [zero_smul,add_zero] at hd
    exact hd.congr_deriv he
  fin_cases i
  · exact h 1 2
  · exact h 2 0
  · exact h 0 1

/-- Every original scalar70 magnetic derivative vanishes by actual Ad invariance and inverse_right; no kinetic cross is assumed. -/
theorem original_scalar_magnetic_derivative (v : Ambient) (hv : v.2=0) (z : physicalChart) :
    fderiv ℝ magneticPotential z.val (direction v z.val)=0 := by
  let γ : ℝ → SourceCoordinateSlice := fun r => z.val+r • direction v z.val
  let a := (inverseL z.val v).1
  have hg : HasDerivAt γ (direction v z.val) 0 := by
    simpa only [γ,one_smul,id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const (direction v z.val)).const_add z.val
  have hi (i j : Fin 3) : HasDerivAt
      (fun r : ℝ => inner ℝ (magneticField (γ r) i) (magneticField (γ r) j)) 0 0 := by
    have h := (scalar_magnetic_field v hv z i).inner ℝ (scalar_magnetic_field v hv z j)
    have he : inner ℝ (magneticField z.val i) (-nativeBracket a (magneticField z.val j))+
        inner ℝ (-nativeBracket a (magneticField z.val i)) (magneticField z.val j)=0 := by
      rw [inner_neg_left,inner_neg_right,native_pair_skew]
      abel
    simp only [zero_smul,add_zero] at h
    exact h.congr_deriv he
  have hw (i j : Fin 3) := (hi i j).const_mul (inverseSpatial z.val i j)
  have hs := ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hw i j))).const_mul
    (volume z.val/(2*sourceSigma*sourceTime 0)))
  have hfun : (fun r : ℝ => magneticPotential (γ r))=
      (fun r : ℝ => volume z.val/(2*sourceSigma*sourceTime 0)*
        ∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z.val i j*inner ℝ (magneticField (γ r) i) (magneticField (γ r) j)) := by
    funext r
    simp only [magneticPotential,γ,direction,volume,inverseSpatial,Prod.smul_mk,Prod.fst_add,add_zero,smul_zero]
  have hzero : HasDerivAt (fun r : ℝ => magneticPotential (γ r)) 0 0 := by
    rw [hfun]
    simpa only [mul_zero,Finset.sum_const_zero] using! hs
  have hd := ((magnetic_smooth z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hg (by simp [γ])
  exact hd.unique hzero

private def rotationIndex (j : Fin 3) : Fin 7 := ⟨j.val+3,by omega⟩

private theorem even_commute {R : Type*} [Ring R] (G A B : R)
    (hA : G*A+A*G=0) (hB : G*B+B*G=0) : Commute (A*B) G := by
  change A*B*G=G*(A*B)
  linear_combination (norm := noncomm_ring) A*hB-hA*B

private theorem rotation_commute (j : Fin 3) (G : DiracMatrix)
    (h1 : G*diracGammaOne+diracGammaOne*G=0)
    (h2 : G*diracGammaTwo+diracGammaTwo*G=0)
    (h3 : G*diracGammaThree+diracGammaThree*G=0) :
    Commute (GaussCoframeSpin.sourceSpin (rotationIndex j)) G := by
  fin_cases j
  · exact (even_commute _ _ _ h2 h3).smul_left (Complex.I/2)
  · exact (even_commute _ _ _ h3 h1).smul_left (Complex.I/2)
  · exact (even_commute _ _ _ h1 h2).smul_left (Complex.I/2)

private theorem rotation_gamma (j : Fin 3) :
    Commute (GaussCoframeSpin.sourceSpin (rotationIndex j)) diracGammaZero :=
  rotation_commute j diracGammaZero diracGammaZeroOne_anticommute diracGammaZeroTwo_anticommute diracGammaZeroThree_anticommute

private theorem rotation_chiral (j : Fin 3) :
    Commute (GaussCoframeSpin.sourceSpin (rotationIndex j)) rightChiralityProjector := by
  have h := rotation_commute j diracGammaFive
    (diracGammaFive_anticommutes 1) (diracGammaFive_anticommutes 2) (diracGammaFive_anticommutes 3)
  unfold rightChiralityProjector
  exact ((Commute.one_right _).add_right h).smul_right _

private theorem dirac_commute (A B : DiracMatrix) (h : Commute A B) :
    Commute (diracMatrixMatterAction A) (diracMatrixMatterAction B) := by
  apply LinearMap.ext
  intro f
  change diracMatrixMatterAction A (diracMatrixMatterAction B f)=diracMatrixMatterAction B (diracMatrixMatterAction A f)
  rw [diracMatrixMatterAction_apply_apply,diracMatrixMatterAction_apply_apply,h.eq]

private theorem rotation_yukawa (j : Fin 3) (phi : ExteriorBreakingScalarCarrier) :
    Commute (diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (rotationIndex j)))
      (LowEnergy.FullQuantum.yukawaHamiltonian phi) := by
  have hg := dirac_commute _ _ (rotation_gamma j)
  have hc := dirac_commute _ _ (rotation_chiral j)
  have hi : Commute (diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (rotationIndex j)))
      (diracExteriorYukawaInternalAction phi) :=
    diracMatrixMatterAction_commutes_internal _ (exteriorYukawaInternalAction phi)
  unfold LowEnergy.FullQuantum.yukawaHamiltonian diracDualRightChiralYukawaAction
  exact (hg.mul_right (hi.mul_right hc)).smul_right _

private theorem rotation_primal (j : Fin 3) (phi : Scalar) :
    Commute (GaussCoframeSpin.primal (rotationIndex j)) (GaussYukawaCoefficient.primal phi) := by
  have h := congrArg LowEnergy.Quantum.operatorMatrix (rotation_yukawa j (scalarCoordinateEquiv.symm phi)).eq
  simp only [map_mul,GaussCoframeSpin.spinLift_source] at h
  exact h

private theorem block_commute {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ) (h : Commute A B) :
    Commute (Matrix.fromBlocks A 0 0 (-(A.map (starRingEnd ℂ))))
      (Matrix.fromBlocks B 0 0 (-(B.map (starRingEnd ℂ)))) := by
  change _*_=_*_
  rw [Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,Matrix.mul_neg,Matrix.neg_mul,neg_neg,neg_zero]
  have hc := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) h.eq
  rw [Matrix.map_mul,Matrix.map_mul] at hc
  exact congrArg₂ (fun X Y : Matrix ι ι ℂ => Matrix.fromBlocks X 0 0 Y) h.eq hc

private theorem rotation_full_matrix (j : Fin 3) (phi : Scalar) :
    Commute (GaussCoframeSpin.full (rotationIndex j)) (GaussYukawaCoefficient.fullMatrix phi) := by
  have hn : ¬(rotationIndex j).val<3 := by simp only [rotationIndex];omega
  unfold GaussCoframeSpin.full
  rw [if_neg hn]
  exact block_commute _ _ (rotation_primal j phi)

private theorem quantized_bracket (A B : Matrix Mode Mode ℂ) :
    quantized A*quantized B-quantized B*quantized A=quantized (A*B-B*A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fiberCoordinates.injective
  simpa only [quantized,quantizedFiber,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,map_sub] using!
    LinearMap.congr_fun (SourceJointCurrentHeisenberg.quantize_commutator A B) (fiberCoordinates f)

private theorem rotation_fock (j : Fin 3) (phi : Scalar) :
    Commute (quantized (GaussCoframeSpin.full (rotationIndex j))) (sourceMap phi) := by
  apply sub_eq_zero.mp
  change quantized _*quantized _-quantized _*quantized _=0
  rw [quantized_bracket,(rotation_full_matrix j phi).eq,sub_self]
  exact map_zero GaussQuantumMultiplier.quantizer

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

/-- The actual spatial spin rows commute with both original independent-dual Yukawa branches. -/
theorem original_spatial_spin_branch (j : Fin 3) (sharp : Bool) (phi : Scalar) :
    Commute (quantized (GaussCoframeSpin.full (rotationIndex j))) (branchMap sharp phi) := by
  have h := rotation_fock j phi
  cases sharp
  · exact h
  · have ha : (quantized (GaussCoframeSpin.full (rotationIndex j))).adjoint=
        quantized (GaussCoframeSpin.full (rotationIndex j)) := by
      rw [quantized_adjoint,GaussCoframeSpin.full_hermitian]
    have hh := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ)) h.eq
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,ha] using! hh.symm

attribute [local irreducible] magneticForce localMagneticForce magneticKernel

private theorem zero_kernel {V : Type*} [AddCommMonoid V] [Module ℂ V]
    {ι : Type*} [Fintype ι] (A : ι → V) (c d e f : ℂ) :
    (∑ i,(0 : ℂ) • A i)+c • (0 : V)+d • (0 : V)+e • (0 : V)+f • (0 : V)=0 := by
  simp only [zero_smul,Finset.sum_const_zero,smul_zero,add_zero]

private theorem magnetic_kernel_zero (sharp : Bool) (z : physicalChart) : magneticKernel sharp z.val=0 := by
  have hs (a : ScalarIndex) : fderiv ℝ magneticPotential z.val (direction (scalarDirection a) z.val)=0 :=
    original_scalar_magnetic_derivative (scalarDirection a) rfl z
  have h3 : bracket (quantized (GaussCoframeSpin.full 3)) (branchMap sharp (scalarField z.val))=0 :=
    sub_eq_zero.mpr (original_spatial_spin_branch 0 sharp (scalarField z.val)).eq
  have h4 : bracket (quantized (GaussCoframeSpin.full 4)) (branchMap sharp (scalarField z.val))=0 :=
    sub_eq_zero.mpr (original_spatial_spin_branch 1 sharp (scalarField z.val)).eq
  have h5 : bracket (quantized (GaussCoframeSpin.full 5)) (branchMap sharp (scalarField z.val))=0 :=
    sub_eq_zero.mpr (original_spatial_spin_branch 2 sharp (scalarField z.val)).eq
  unfold magneticKernel
  change (∑ a : ScalarIndex,((scalarWeight z.val : ℂ)*
      (fderiv ℝ magneticPotential z.val (direction (scalarDirection a) z.val) : ℂ)) • branchMap sharp (scalarDirection a).1)+
    (Complex.I*(GaussCoframeForm.currentCoefficient 0 z.val : ℂ)*
      (fderiv ℝ magneticPotential z.val (GaussCoframeCore.coframeDirection 1) : ℂ)) •
      bracket (quantized (GaussCoframeSpin.full 5)) (branchMap sharp (scalarField z.val))+
    (Complex.I*(GaussCoframeForm.currentCoefficient 1 z.val : ℂ)*
      (fderiv ℝ magneticPotential z.val (GaussCoframeCore.coframeDirection 3) : ℂ)) •
      bracket (quantized (GaussCoframeSpin.full 3)) (branchMap sharp (scalarField z.val))+
    (Complex.I*((-GaussCoframeForm.currentCoefficient 0 z.val : ℝ) : ℂ)*
      (fderiv ℝ magneticPotential z.val (GaussCoframeCore.coframeDirection 3) : ℂ)) •
      bracket (quantized (GaussCoframeSpin.full 4)) (branchMap sharp (scalarField z.val))+
    (Complex.I*(GaussCoframeForm.currentCoefficient 2 z.val : ℂ)*
      (fderiv ℝ magneticPotential z.val (GaussCoframeCore.coframeDirection 4) : ℂ)) •
      bracket (quantized (GaussCoframeSpin.full 3)) (branchMap sharp (scalarField z.val))=0
  simp only [hs,Complex.ofReal_zero,mul_zero,h3,h4,h5]
  exact zero_kernel _ _ _ _ _

/-- The actual Ad invariant magnetic potential and repaired spatial-spin Yukawa source erase the complete magnetic double current. -/
theorem original_magnetic_force_zero (sharp : Bool) : magneticForce sharp=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change magneticForce sharp f z=0
  by_cases hz : z∈physicalChart
  · rw [original_magnetic_force_apply,magnetic_kernel_zero sharp ⟨z,hz⟩,zero_apply]
  · exact image_eq_zero_of_notMem_tsupport (fun h => hz ((magneticForce sharp f).tsupport_subset h))

/-- No magnetic force remains in the original cutoff neutral current; the gauge-kinetic cross is not removed. -/
theorem original_magnetic_neutral_zero (sharp : Bool) (m ell : ℕ) :
    bracket magneticAction (neutralCurrent sharp m ell)=0 := by
  rw [original_magnetic_force_localization,original_magnetic_force_zero,mul_zero]

attribute [local irreducible] readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  cutoffEuler scaleDoubleRemainder constantAction solverOperator oscillatorMass
  singleResponseJet joinedPolynomial hamiltonianCorrectionJet gaugeFilter nativeForceRemainder

/-- The literal remaining source word after the actual magnetic force cancels; all original corrections remain. -/
def kineticCrossRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => hamiltonianCorrectionJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (hamiltonianGaugeForce sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (hamiltonianGaugeForce sharp m ell) 0 n)*finiteResolvent F z-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F g
    (-(2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F-
    (4 : ℂ) • sourceRead F g (-bracket gaugeKinetic (neutralCurrent sharp m ell))+
    (2 : ℂ) • sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)))*finiteResolvent F z


/-- The complete same-F/g/z native remainder consumes source Mag=0, leaving its true gauge-kinetic cross. -/
theorem actual_native_kinetic_cross (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :
    nativeForceRemainder sharp m ell F g z=kineticCrossRemainder sharp m ell F g z := by
  have hk : kineticMagneticForce sharp m ell= -bracket gaugeKinetic (neutralCurrent sharp m ell) := by
    have hm := original_magnetic_neutral_zero sharp m ell
    unfold kineticMagneticForce bracket at hm ⊢
    linear_combination (norm := noncomm_ring) hm
  unfold nativeForceRemainder kineticCrossRemainder
  exact congrArg (fun K : End =>
    (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
      gaugeFilter (fun n => hamiltonianCorrectionJet sharp m ell F g z n 0)-
      gaugeFilter (fun n => inverseCross F g z (hamiltonianGaugeForce sharp m ell) 0 n)-
      finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (hamiltonianGaugeForce sharp m ell) 0 n)*finiteResolvent F z-
      gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
      finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*finiteResolvent F z)+
    finiteResolvent F z*(sourceRead F g
      (-(2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
        (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
        (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F-
      (4 : ℂ) • sourceRead F g K+
      (2 : ℂ) • sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)))*finiteResolvent F z) hk

end LowEnergy.SourceInverseMagneticForceCancellation
