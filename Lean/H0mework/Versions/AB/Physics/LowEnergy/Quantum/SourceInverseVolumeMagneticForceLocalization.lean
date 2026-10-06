import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeHamiltonianForceReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseMagneticForceLocalization
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets SourceGaugeCoframeJets SourceScalarForceBudget
open SourceInverseGaugeSingleDefectJoin SourceInverseHamiltonianForceReduction SourceInverseCompressionGaugeSplice
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceScalarRadialContact SourceNativeCutoffContact
open Filter MeasureTheory SourceResolventBandLimit
open GaussLiveMomentum
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  sourceRead state defectAction compressionCore deltaGauge
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent matterInsertion neutralCurrent kineticMagneticForce nativeForceRemainder
  scalarSpatialAction scalarEulerAction weightedProfileAction

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

private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  unfold SourceMixedNativeReturn.thetaAction
  exact ((Commute.one_right _).sub_right (GaussRadialHamiltonian.real_commutes c hc) |>.pow_right _).sub_right
    ((Commute.one_right _).sub_right (GaussRadialHamiltonian.real_commutes c hc) |>.pow_right _)

private theorem magnetic_smooth (z : physicalChart) : ContDiffAt ℝ ∞ magneticPotential z.val := by
  have hm (i j : Fin 3) := (inverseSpatial_smooth i j z).mul
    ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt)
  exact (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hm i j)

private theorem magnetic_scalar_derivative (z : physicalChart) :
    fderiv ℝ magneticPotential z.val (scalarEuler z.val)=0 := by
  have hc : HasDerivAt (fun r : ℝ => (z.val.1,r • z.val.2.1,z.val.2.2)) (scalarEuler z.val) 1 := by
    simpa only [scalarEuler,one_smul] using!
      (hasDerivAt_const (1 : ℝ) z.val.1).prodMk (((hasDerivAt_id (1 : ℝ)).smul_const z.val.2.1).prodMk (hasDerivAt_const (1 : ℝ) z.val.2.2))
  have hh := ((magnetic_smooth z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 1 hc
    (by simp)
  change HasDerivAt (fun _ : ℝ => magneticPotential z.val)
    (fderiv ℝ magneticPotential z.val (scalarEuler z.val)) 1 at hh
  exact hh.unique (hasDerivAt_const 1 _)

private theorem magnetic_euler : Commute magneticAction scalarEulerAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · change magneticAction (scalarEulerAction f) z=scalarEulerAction (magneticAction f) z
    rw [scalar_euler_apply]
    have he : (magneticAction f : SourceCoordinateSlice → FockFiber)=fun w => magneticPotential w • f w := by
      funext w
      unfold magneticAction
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    rw [he,fderiv_fun_smul ((magnetic_smooth ⟨z,hz⟩).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change (magneticPotential z : ℂ) • scalarEulerAction f z=magneticPotential z • fderiv ℝ f z (scalarEuler z)+
      fderiv ℝ magneticPotential z (scalarEuler z) • f z
    rw [magnetic_scalar_derivative ⟨z,hz⟩,zero_smul,add_zero]
    rw [scalar_euler_apply]
    apply PiLp.ext
    intro word
    exact Complex.real_smul.symm
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The actual magnetic multiplier commutes with the complete source cutoff current. -/
theorem original_magnetic_radial_current (m ell : ℕ) :
    bracket magneticAction (bracket diagonalAction (SourceMixedNativeReturn.thetaAction m ell))=0 := by
  have hp : Commute magneticAction (weightedProfileAction m ell) := by
    unfold magneticAction weightedProfileAction
    exact real_commute _ _ _ _
  have hh := original_hamiltonian_radial_contact m ell
  change diagonalAction*SourceMixedNativeReturn.thetaAction m ell-
    SourceMixedNativeReturn.thetaAction m ell*diagonalAction=_ at hh
  simp only [bracket]
  rw [hh]
  exact sub_eq_zero.mpr (((magnetic_euler.mul_right hp).add_right (hp.mul_right magnetic_euler)).add_right
    (hp.smul_right (61 : ℂ)) |>.smul_right (1/2 : ℂ)).eq

/-- The remaining bare magnetic force is generated by the original H and full Yukawa branch. -/
def magneticForce (sharp : Bool) : End := bracket magneticAction (bracket diagonalAction (SourceMixedNativeReturn.fullAction sharp))

private theorem magnetic_matter (sharp : Bool) (m ell : ℕ) : Commute magneticAction (matterInsertion sharp m ell) := by
  have hm : Commute magneticAction matterAction := by
    unfold magneticAction matterAction
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro j _
    exact real_local _ _ _ _
  have hx : Commute magneticAction (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
    unfold SourceScalarDoubleCurrent.fullInsertion magneticAction
    exact (real_full _ _ sharp).mul_right (real_theta _ _ m ell)
  unfold matterInsertion bracket
  exact (hm.mul_right hx).sub_right (hx.mul_right hm)

private theorem localized_double {R : Type*} [Ring R] (A H Y T : R)
    (hY : Commute A Y) (hT : Commute A T) (hyT : Commute Y T)
    (hHT : bracket A (bracket H T)=0) :
    bracket A (bracket H (Y*T))=T*bracket A (bracket H Y) := by
  have hs : bracket A (bracket H (T*Y))=
      T*bracket A (bracket H Y)+bracket A (bracket H T)*Y := by
    unfold bracket
    linear_combination (norm := noncomm_ring)
      hT.eq*(H*Y-Y*H)+(H*T-T*H)*hY.eq
  rw [hyT.eq,hs,hHT,zero_mul,add_zero]

/-- No cutoff derivative survives in the complete magnetic part of the original neutral current. -/
theorem original_magnetic_force_localization (sharp : Bool) (m ell : ℕ) :
    bracket magneticAction (neutralCurrent sharp m ell)=
      SourceMixedNativeReturn.thetaAction m ell*magneticForce sharp := by
  have hy : Commute magneticAction (SourceMixedNativeReturn.fullAction sharp) := by
    unfold magneticAction
    exact real_full _ _ sharp
  have ht : Commute magneticAction (SourceMixedNativeReturn.thetaAction m ell) := by
    unfold magneticAction
    exact real_theta _ _ m ell
  have hyt : Commute (SourceMixedNativeReturn.fullAction sharp) (SourceMixedNativeReturn.thetaAction m ell) := by
    unfold SourceMixedNativeReturn.thetaAction
    have h := GaussRadialHamiltonian.original_commutes
    have hd := GaussRadialHamiltonian.adjoint_commutes
    cases sharp
    · exact ((Commute.one_right _).sub_right h |>.pow_right _).sub_right ((Commute.one_right _).sub_right h |>.pow_right _)
    · exact ((Commute.one_right _).sub_right hd |>.pow_right _).sub_right ((Commute.one_right _).sub_right hd |>.pow_right _)
  have h := localized_double magneticAction diagonalAction (SourceMixedNativeReturn.fullAction sharp)
    (SourceMixedNativeReturn.thetaAction m ell) hy ht hyt (original_magnetic_radial_current m ell)
  have hm := magnetic_matter sharp m ell
  unfold neutralCurrent firstHamiltonianCurrent SourceScalarDoubleCurrent.fullInsertion magneticForce
  unfold bracket at h ⊢
  linear_combination (norm := noncomm_ring) h-hm.eq

private def magneticContact (D : End) : End := D*magneticAction-magneticAction*D

private theorem magnetic_contact_apply (D : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hD : ∀ f z,D f z=fderiv ℝ f z (e z)) (f : QuantumTest) (z : SourceCoordinateSlice) :
    magneticContact D f z=(fderiv ℝ magneticPotential z (e z) : ℂ) • f z := by
  by_cases hz : z∈physicalChart
  · change D (magneticAction f) z-magneticAction (D f) z=_
    rw [hD]
    have he : (magneticAction f : SourceCoordinateSlice → FockFiber)=fun w => magneticPotential w • f w := by
      funext w
      unfold magneticAction
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    rw [he,fderiv_fun_smul ((magnetic_smooth ⟨z,hz⟩).differentiableAt (by simp))
      (f.contDiff.differentiable (by simp)).differentiableAt]
    change magneticPotential z • fderiv ℝ f z (e z)+fderiv ℝ magneticPotential z (e z) • f z-
      (magneticPotential z : ℂ) • D f z=_
    rw [hD]
    apply PiLp.ext
    intro word
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    rw [h0,h0,smul_zero]

private theorem magnetic_contact_pair (D : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hD : ∀ f z,D f z=fderiv ℝ f z (e z)) (f g : QuantumTest) :
    sourcePair f (magneticContact D g)=sourcePair (magneticContact D f) g := by
  rw [sourcePair_integral,sourcePair_integral]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [densityPair_sum,densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [magnetic_contact_apply D e hD,magnetic_contact_apply D e hD]
  change _*star (f z word)*((fderiv ℝ magneticPotential z (e z) : ℂ)*g z word)=
    _*star ((fderiv ℝ magneticPotential z (e z) : ℂ)*f z word)*g z word
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
  ring

private theorem native_magnetic_current (v : Ambient) :
    bracket magneticAction (covariantMomentum v)=Complex.I • magneticContact (directional v) := by
  have hc : Commute magneticAction (localMultiplier (connection v) (connection_smooth v)) := by
    unfold magneticAction
    exact real_local _ _ _ _
  unfold covariantMomentum magneticContact bracket
  simp only [mul_smul_comm,smul_mul_assoc,add_mul,mul_add]
  linear_combination (norm := module) (-Complex.I) • hc.eq

private theorem pair_smul_right (f g : QuantumTest) (c : ℂ) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem adjoint_current {A P Q C : End}
    (hA : ∀ f g,sourcePair f (A g)=sourcePair (A f) g)
    (hP : ∀ f g,sourcePair f (Q g)=sourcePair (P f) g)
    (hC : ∀ f g,sourcePair f (C g)=sourcePair (C f) g)
    (h : bracket A P=Complex.I • C) : bracket A Q=Complex.I • C := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have hh := congrArg (fun t : QuantumTest => sourcePair t g) (LinearMap.congr_fun h f)
  change sourcePair (A (P f)-P (A f)) g=sourcePair (Complex.I • C f) g at hh
  simp only [sourcePair,map_sub,map_smul,inner_sub_left,inner_smul_left,Complex.conj_I] at hh
  change sourcePair f (A (Q g)-Q (A g))=sourcePair f (Complex.I • C g)
  have hl : sourcePair f (A (Q g)-Q (A g))=sourcePair (P (A f)) g-sourcePair (A (P f)) g := by
    change inner ℂ (embed f) (embed (A (Q g)-Q (A g)))=_
    rw [map_sub,inner_sub_right]
    change sourcePair f (A (Q g))-sourcePair f (Q (A g))=_
    rw [hA,hP,hP,hA]
  rw [hl]
  rw [pair_smul_right,hC]
  change inner ℂ (embed (P (A f))) (embed g)-inner ℂ (embed (A (P f))) (embed g)=
    Complex.I*inner ℂ (embed (C f)) (embed g)
  linear_combination -hh

private theorem native_magnetic_adjoint (v : Ambient) :
    bracket magneticAction (GaussMomentumAdjoint.adjoint v)=Complex.I • magneticContact (directional v) := by
  exact adjoint_current (fun f g => multiply_pair magneticPotential _ f g)
    (GaussNativeForm.adjoint_pair v)
    (magnetic_contact_pair (directional v) (direction v) (directional_apply v)) (native_magnetic_current v)

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem native_full_current (sharp : Bool) (v : Ambient) :
    bracket (covariantMomentum v) (SourceMixedNativeReturn.fullAction sharp)=
      (-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (SourceMixedNativeReturn.fullAction sharp f)-
    SourceMixedNativeReturn.fullAction sharp (covariantMomentum v f)=_
  rw [original_full_momentum]
  abel

private theorem native_full_adjoint (sharp : Bool) (v : Ambient) :
    bracket (GaussMomentumAdjoint.adjoint v) (SourceMixedNativeReturn.fullAction sharp)=
      (-Complex.I) • constantAction sharp v.1 := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have h := original_full_momentum (!sharp) v f
  have hh := congrArg (fun t : QuantumTest => sourcePair t g) h
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at hh
  change sourcePair f (GaussMomentumAdjoint.adjoint v (SourceMixedNativeReturn.fullAction sharp g)-
    SourceMixedNativeReturn.fullAction sharp (GaussMomentumAdjoint.adjoint v g))=
      sourcePair f ((-Complex.I) • constantAction sharp v.1 g)
  have hl : sourcePair f (GaussMomentumAdjoint.adjoint v (SourceMixedNativeReturn.fullAction sharp g)-
      SourceMixedNativeReturn.fullAction sharp (GaussMomentumAdjoint.adjoint v g))=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) (covariantMomentum v f)) g-
        sourcePair (covariantMomentum v (SourceMixedNativeReturn.fullAction (!sharp) f)) g := by
    change inner ℂ (embed f) (embed (_-_))=_
    rw [map_sub,inner_sub_right]
    change sourcePair f (GaussMomentumAdjoint.adjoint v (SourceMixedNativeReturn.fullAction sharp g))-
      sourcePair f (SourceMixedNativeReturn.fullAction sharp (GaussMomentumAdjoint.adjoint v g))=_
    rw [GaussNativeForm.adjoint_pair,full_pair,full_pair,GaussNativeForm.adjoint_pair]
  rw [hl]
  rw [pair_smul_right,SourceMixedNativeReturn.constant_pair]
  change inner ℂ (embed (SourceMixedNativeReturn.fullAction (!sharp) (covariantMomentum v f))) (embed g)-
    inner ℂ (embed (covariantMomentum v (SourceMixedNativeReturn.fullAction (!sharp) f))) (embed g)=
      (-Complex.I)*inner ℂ (embed (constantAction (!sharp) v.1 f)) (embed g)
  linear_combination -hh

private theorem full_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    SourceMixedNativeReturn.fullAction sharp f z=branchMap sharp (scalarField z) (f z) := by
  cases sharp <;> rfl

private theorem contact_full (D : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (hD : ∀ f z,D f z=fderiv ℝ f z (e z)) (sharp : Bool) :
    Commute (magneticContact D) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change magneticContact D (SourceMixedNativeReturn.fullAction sharp f) z=
    SourceMixedNativeReturn.fullAction sharp (magneticContact D f) z
  rw [magnetic_contact_apply D e hD,full_at,full_at,magnetic_contact_apply D e hD,map_smul]

private theorem bracket_mul_right {R : Type*} [Ring R] (A B C : R) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket; noncomm_ring
private theorem bracket_mul_left {R : Type*} [Ring R] (A B C : R) :
    bracket (A*B) C=A*bracket B C+bracket A C*B := by unfold bracket; noncomm_ring
private theorem bracket_add_left {R : Type*} [Ring R] (A B C : R) :
    bracket (A+B) C=bracket A C+bracket B C := by unfold bracket; noncomm_ring
private theorem bracket_add_right {R : Type*} [Ring R] (A B C : R) :
    bracket A (B+C)=bracket A B+bracket A C := by unfold bracket; noncomm_ring
private theorem bracket_smul_left {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (a : ℂ) (A B : R) :
    bracket (a • A) B=a • bracket A B := by simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_smul_right {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (a : ℂ) (A B : R) :
    bracket A (a • B)=a • bracket A B := by simp only [bracket,smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem commute_bracket {R : Type*} [Ring R] {A B : R} (h : Commute A B) : bracket A B=0 := sub_eq_zero.mpr h.eq
private theorem jacobi_move {R : Type*} [Ring R] (A H Y : R) (hAY : Commute A Y) :
    bracket A (bracket H Y)=bracket (bracket A H) Y := by
  unfold bracket
  linear_combination (norm := noncomm_ring) H*hAY.eq-hAY.eq*H

private theorem local_double_sandwich {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (M Y a w p D C : R)
    (hMY : Commute M Y) (hMw : Commute M w) (hwY : Commute w Y) (hDY : Commute D Y)
    (hMa : bracket M a=Complex.I • D) (hMp : bracket M p=Complex.I • D)
    (haY : bracket a Y=(-Complex.I) • C) (hpY : bracket p Y=(-Complex.I) • C) :
    bracket M (bracket (a*w*p) Y)=D*w*C+C*w*D := by
  rw [jacobi_move M (a*w*p) Y hMY]
  simp only [bracket_mul_right,hMa,hMp,commute_bracket hMw,mul_zero,add_zero]
  simp only [bracket_add_left,bracket_mul_left,bracket_smul_left,commute_bracket hDY,
    commute_bracket hwY,haY,hpY,mul_zero,zero_mul,zero_add,add_zero,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [show Complex.I*(-Complex.I)=(1 : ℂ) by rw [mul_neg,Complex.I_mul_I,neg_neg]]
  module

private def scalarMagneticForce (sharp : Bool) : End := (1/2 : ℂ) • ∑ a : ScalarIndex,
  (magneticContact (directional (scalarDirection a))*multiply scalarWeight scalarWeight_smooth*constantAction sharp (scalarDirection a).1+
    constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*magneticContact (directional (scalarDirection a)))

private theorem bracket_sum_left {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (B : R) :
    bracket (∑ i,A i) B=∑ i,bracket (A i) B := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
private theorem bracket_sum_right {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : R) (B : ι → R) :
    bracket A (∑ i,B i)=∑ i,bracket A (B i) := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]

private theorem scalar_magnetic_force (sharp : Bool) :
    bracket magneticAction (bracket scalarKinetic (SourceMixedNativeReturn.fullAction sharp))=scalarMagneticForce sharp := by
  have hm : Commute magneticAction (SourceMixedNativeReturn.fullAction sharp) := by unfold magneticAction;exact real_full _ _ sharp
  have hw : Commute magneticAction (multiply scalarWeight scalarWeight_smooth) := by unfold magneticAction;exact real_commute _ _ _ _
  have hwY := real_full scalarWeight scalarWeight_smooth sharp
  have he (a : ScalarIndex) := local_double_sandwich magneticAction (SourceMixedNativeReturn.fullAction sharp)
    (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (covariantMomentum (scalarDirection a)) (magneticContact (directional (scalarDirection a)))
    (constantAction sharp (scalarDirection a).1) hm hw hwY
    (contact_full _ _ (directional_apply _) sharp) (native_magnetic_adjoint _) (native_magnetic_current _)
    (native_full_adjoint sharp _) (native_full_current sharp _)
  unfold scalarKinetic scalarMagneticForce sandwich
  simp only [←Module.End.mul_eq_comp,←mul_assoc,bracket_smul_left,bracket_smul_right,bracket_sum_left,bracket_sum_right]
  exact congrArg (fun A : End => (1/2 : ℂ) • A) (Finset.sum_congr rfl (fun a _ => he a))

private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 0) (hz : γ 0=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 0 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem coframe_derivative_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let e := GaussCoframeCore.coframeDirection i
  let A := (branchMap sharp (scalarField z)).restrictScalars ℝ
  have hg : HasDerivAt (fun r : ℝ => z+r • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have he := invariant_derivative A f (SourceMixedNativeReturn.fullAction sharp f) (fun r : ℝ => z+r • e) z e hg
    (by simp) ((f.contDiff.differentiable (by simp)) z)
    (((SourceMixedNativeReturn.fullAction sharp f).contDiff.differentiable (by simp)) z) (fun r => by
      rw [full_at]
      simp only [A,e,GaussCoframeCore.coframeDirection,scalarField,Prod.smul_mk,Prod.snd_add,
        smul_zero,add_zero,ContinuousLinearMap.coe_restrictScalars'])
  change GaussCoframeCore.derivative e (SourceMixedNativeReturn.fullAction sharp f) z=
    SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.derivative e f) z
  rw [GaussCoframeCore.derivative_apply,full_at,GaussCoframeCore.derivative_apply]
  exact he

private theorem coframe_full (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.momentum i) (SourceMixedNativeReturn.fullAction sharp) :=
  (coframe_derivative_full i sharp).smul_left (-Complex.I)

private theorem coframe_full_adjoint (i : Fin 6) (sharp : Bool) :
    Commute (GaussCoframeCore.adjoint i) (SourceMixedNativeReturn.fullAction sharp) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have he := LinearMap.congr_fun (coframe_full i (!sharp)).eq f
  change sourcePair f (GaussCoframeCore.adjoint i (SourceMixedNativeReturn.fullAction sharp g))=
    sourcePair f (SourceMixedNativeReturn.fullAction sharp (GaussCoframeCore.adjoint i g))
  rw [GaussCoframeKinetic.adjoint_pair,full_pair,full_pair,GaussCoframeKinetic.adjoint_pair]
  exact congrArg (fun q => sourcePair q g) he.symm

private theorem coframe_magnetic_current (i : Fin 6) :
    bracket magneticAction (GaussCoframeCore.momentum i)=
      Complex.I • magneticContact (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) := by
  unfold GaussCoframeCore.momentum magneticContact bracket
  simp only [mul_smul_comm,smul_mul_assoc]
  module

private theorem coframe_magnetic_adjoint (i : Fin 6) :
    bracket magneticAction (GaussCoframeCore.adjoint i)=
      Complex.I • magneticContact (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) :=
  adjoint_current (fun f g => multiply_pair magneticPotential _ f g)
    (GaussCoframeKinetic.adjoint_pair i)
    (magnetic_contact_pair _ _ (GaussCoframeCore.derivative_apply _)) (coframe_magnetic_current i)

private theorem magnetic_spin (a : Fin 7) : Commute magneticAction (GaussCoframeSpin.current a) := by
  unfold magneticAction GaussCoframeSpin.current GaussQuantumMultiplier.action
  exact real_local _ _ _ _

private def localMixedForce (sharp : Bool) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : End :=
  (Complex.I/2) • bracket
    (GaussCoframeSpin.current a*multiply c hc*magneticContact (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i))+
      magneticContact (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i))*multiply c hc*GaussCoframeSpin.current a)
    (SourceMixedNativeReturn.fullAction sharp)

private theorem mixed_magnetic_force (sharp : Bool) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    bracket magneticAction (bracket (GaussCoframeForm.mixed i a c hc) (SourceMixedNativeReturn.fullAction sharp))=
      localMixedForce sharp i a c hc := by
  have hMY : Commute magneticAction (SourceMixedNativeReturn.fullAction sharp) := by unfold magneticAction;exact real_full _ _ sharp
  have hMc : Commute magneticAction (multiply c hc) := by unfold magneticAction;exact real_commute _ _ _ _
  rw [jacobi_move _ _ _ hMY]
  unfold GaussCoframeForm.mixed localMixedForce
  simp only [←Module.End.mul_eq_comp,bracket_smul_right,bracket_add_right,bracket_mul_right,
    commute_bracket (magnetic_spin a),commute_bracket hMc,coframe_magnetic_current,coframe_magnetic_adjoint,
    zero_mul,mul_zero,zero_add,add_zero,mul_smul_comm,smul_mul_assoc,←smul_add,smul_smul,bracket_smul_left]
  congr 1
  ring

private def coframeMagneticForce (sharp : Bool) : End :=
  localMixedForce sharp 1 5 (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0)+
  localMixedForce sharp 3 3 (GaussCoframeForm.currentCoefficient 1) (GaussCoframeForm.currentCoefficient_smooth 1)+
  localMixedForce sharp 3 4 (fun z => -GaussCoframeForm.currentCoefficient 0 z)
    (fun z => (GaussCoframeForm.currentCoefficient_smooth 0 z).neg)+
  localMixedForce sharp 4 3 (GaussCoframeForm.currentCoefficient 2) (GaussCoframeForm.currentCoefficient_smooth 2)

private theorem coframe_kinetic_full (sharp : Bool) : Commute GaussCoframeKinetic.kinetic (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  unfold GaussCoframeKinetic.term
  exact (coframe_full_adjoint i sharp).mul_left ((real_full _ _ sharp).mul_left (coframe_full j sharp))

private theorem magnetic_coframe_rest : Commute magneticAction
    ((∑ a : Fin 7,GaussCoframeForm.spinSquare a)+GaussCoframeForm.numberShift+
      multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth) := by
  have hi : Commute magneticAction (multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth) := by
    unfold magneticAction
    exact real_commute _ _ _ _
  have hs (a : Fin 7) : Commute magneticAction (GaussCoframeForm.spinSquare a) := by
    unfold GaussCoframeForm.spinSquare
    exact ((magnetic_spin a).mul_right (hi.mul_right (magnetic_spin a))).smul_right _
  have hn : Commute magneticAction GaussCoframeForm.number := by
    unfold magneticAction GaussCoframeForm.number GaussQuantumMultiplier.action
    exact real_local _ _ _ _
  have hc : Commute magneticAction (multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth) := by
    unfold magneticAction
    exact real_commute _ _ _ _
  have hns : Commute magneticAction GaussCoframeForm.numberShift := by
    unfold GaussCoframeForm.numberShift
    exact ((hn.mul_right hc).add_right (hc.mul_right hn)).smul_right _
  have hv : Commute magneticAction (multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth) := by
    unfold magneticAction
    exact real_commute _ _ _ _
  have hss : Commute magneticAction (∑ a : Fin 7,GaussCoframeForm.spinSquare a) := by
    apply Commute.sum_right
    intro a _
    exact hs a
  exact (hss.add_right hns).add_right hv

private theorem coframe_magnetic_force (sharp : Bool) :
    bracket magneticAction (bracket GaussCoframeForm.coframeAction (SourceMixedNativeReturn.fullAction sharp))=
      coframeMagneticForce sharp := by
  let V := (∑ a : Fin 7,GaussCoframeForm.spinSquare a)+GaussCoframeForm.numberShift+
    multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
  have hc : GaussCoframeForm.coframeAction=GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+V := by
    unfold GaussCoframeForm.coframeAction V
    abel
  have hmY : Commute magneticAction (SourceMixedNativeReturn.fullAction sharp) := by unfold magneticAction;exact real_full _ _ sharp
  have hV : bracket magneticAction (bracket V (SourceMixedNativeReturn.fullAction sharp))=0 := by
    rw [jacobi_move _ _ _ hmY,commute_bracket magnetic_coframe_rest]
    simp only [bracket,zero_mul,mul_zero,sub_self]
  rw [hc]
  simp only [bracket_add_left,bracket_add_right,commute_bracket (coframe_kinetic_full sharp),hV]
  have hz : bracket magneticAction (0 : End)=0 := by simp only [bracket,mul_zero,zero_mul,sub_self]
  rw [hz,zero_add,add_zero]
  change bracket magneticAction (bracket GaussCoframeForm.currentAction (SourceMixedNativeReturn.fullAction sharp))=_
  unfold GaussCoframeForm.currentAction coframeMagneticForce
  simp only [bracket_add_left,bracket_add_right,mixed_magnetic_force]

/-- A concrete zero-order source expression: all scalar70 and original four coframe-current contacts. -/
def localMagneticForce (sharp : Bool) : End := scalarMagneticForce sharp+coframeMagneticForce sharp

/-- The original H magnetic double current contains no derivative of the moving input. -/
theorem original_magnetic_local_force (sharp : Bool) : magneticForce sharp=localMagneticForce sharp := by
  have hmY : Commute magneticAction (SourceMixedNativeReturn.fullAction sharp) := by unfold magneticAction;exact real_full _ _ sharp
  have hMM : Commute magneticAction matterAction := by
    unfold magneticAction matterAction
    apply Commute.sum_right
    intro i _
    apply Commute.sum_right
    intro j _
    exact real_local _ _ _ _
  have hM : bracket magneticAction (bracket matterAction (SourceMixedNativeReturn.fullAction sharp))=0 := by
    rw [jacobi_move _ _ _ hmY,commute_bracket hMM]
    simp only [bracket,zero_mul,mul_zero,sub_self]
  unfold magneticForce diagonalAction nativeAction localMagneticForce
  simp only [bracket_add_left,bracket_add_right,commute_bracket (original_electric_full sharp),
    commute_bracket (real_full potential potential_smooth sharp),scalar_magnetic_force,coframe_magnetic_force,hM]
  simp only [bracket,mul_zero,zero_mul,sub_self,add_zero]

private theorem native_contact_at (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    magneticContact (directional v) f z=(fderiv ℝ magneticPotential z (direction v z) : ℂ) • f z :=
  magnetic_contact_apply _ _ (directional_apply v) f z

private theorem coframe_contact_at (i : Fin 6) (f : QuantumTest) (z : SourceCoordinateSlice) :
    magneticContact (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) f z=
      (fderiv ℝ magneticPotential z (GaussCoframeCore.coframeDirection i) : ℂ) • f z :=
  magnetic_contact_apply _ _ (GaussCoframeCore.derivative_apply _) f z

private theorem constant_at (sharp : Bool) (v : Scalar) (f : QuantumTest) (z : SourceCoordinateSlice) :
    constantAction sharp v f z=branchMap sharp v (f z) := rfl
private theorem spin_at (a : Fin 7) (f : QuantumTest) (z : SourceCoordinateSlice) :
    GaussCoframeSpin.current a f z=GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a) (f z) := rfl

private def mixedKernel (sharp : Bool) (i : Fin 6) (a : Fin 7) (c : ℝ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (Complex.I*(c : ℂ)*(fderiv ℝ magneticPotential z (GaussCoframeCore.coframeDirection i) : ℂ)) •
    bracket (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)) (branchMap sharp (scalarField z))

/-- The literal magnetic coefficient contains source derivatives of Mag, and no derivative of an input state. -/
def magneticKernel (sharp : Bool) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (∑ a : ScalarIndex,((scalarWeight z : ℂ)*(fderiv ℝ magneticPotential z (direction (scalarDirection a) z) : ℂ)) •
    branchMap sharp (scalarDirection a).1)+
  mixedKernel sharp 1 5 (GaussCoframeForm.currentCoefficient 0 z) z+
  mixedKernel sharp 3 3 (GaussCoframeForm.currentCoefficient 1 z) z+
  mixedKernel sharp 3 4 (-GaussCoframeForm.currentCoefficient 0 z) z+
  mixedKernel sharp 4 3 (GaussCoframeForm.currentCoefficient 2 z) z

private theorem scalar_force_at (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    scalarMagneticForce sharp f z=
      (∑ a : ScalarIndex,((scalarWeight z : ℂ)*(fderiv ℝ magneticPotential z (direction (scalarDirection a) z) : ℂ)) •
        branchMap sharp (scalarDirection a).1) (f z) := by
  simp only [scalarMagneticForce,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,
    smul_apply,sum_apply,add_apply,native_contact_at,multiply_apply,constant_at,map_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  module

private theorem mixed_force_at (sharp : Bool) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (f : QuantumTest) (z : SourceCoordinateSlice) :
    localMixedForce sharp i a c hc f z=mixedKernel sharp i a (c z) z (f z) := by
  simp only [localMixedForce,mixedKernel,bracket,LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.add_apply,
    Module.End.mul_apply,smul_apply,sub_apply,add_apply,coframe_contact_at,multiply_apply,full_at,spin_at,
    map_add,map_smul,mul_apply_eq_comp]
  module

/-- Actual pointwise zero-order return of the complete magnetic H-force. -/
theorem original_magnetic_force_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    magneticForce sharp f z=magneticKernel sharp z (f z) := by
  rw [original_magnetic_local_force]
  simp only [localMagneticForce,coframeMagneticForce,LinearMap.add_apply,add_apply,scalar_force_at,mixed_force_at,magneticKernel]
  abel

/-- Both original Yukawa branches of the magnetic source have the genuine fixed-input cutoff tail. -/
theorem original_magnetic_fixed_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ‖embed (bracket magneticAction (neutralCurrent sharp m ell) f)‖<ε := by
  have he (m ell : ℕ) : embed (bracket magneticAction (neutralCurrent sharp m ell) f)=
      SourceRelativePowerTail.relativeTail m ell (embed (magneticForce sharp f)) := by
    rw [original_magnetic_force_localization]
    change embed (SourceMixedNativeReturn.thetaAction m ell (magneticForce sharp f))=_
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
      SourceNativeCutoffContact.theta_core]
  simpa only [he] using! SourceHardyRetardedTail.original_relative_tail (embed (magneticForce sharp f))

attribute [local irreducible] readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  cutoffEuler scaleDoubleRemainder constantAction solverOperator oscillatorMass
  singleResponseJet joinedPolynomial hamiltonianCorrectionJet gaugeFilter

/-- The literal native remainder, now consuming the zero-order magnetic coefficient; Kg remains intact. -/
def magneticLocalizedRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
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
    (4 : ℂ) • sourceRead F g (SourceMixedNativeReturn.thetaAction m ell*localMagneticForce sharp-
      bracket gaugeKinetic (neutralCurrent sharp m ell))+
    (2 : ℂ) • sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)))*finiteResolvent F z


/-- The complete actual remainder consumes the magnetic source localization in the original two-leg word. -/
theorem actual_native_magnetic_localization (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :
    nativeForceRemainder sharp m ell F g z=magneticLocalizedRemainder sharp m ell F g z := by
  have hk : kineticMagneticForce sharp m ell=
      SourceMixedNativeReturn.thetaAction m ell*localMagneticForce sharp-bracket gaugeKinetic (neutralCurrent sharp m ell) := by
    unfold kineticMagneticForce
    have hm := original_magnetic_force_localization sharp m ell
    rw [original_magnetic_local_force] at hm
    unfold bracket at hm ⊢
    linear_combination (norm := noncomm_ring) hm
  unfold nativeForceRemainder magneticLocalizedRemainder
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

end LowEnergy.SourceInverseMagneticForceLocalization
