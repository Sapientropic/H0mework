import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarPairedTransport
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarRadialContact
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceSignedCutoffWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourcePairedRadialFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussHistoryHilbert
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum GaussMomentumAdjoint
open SourceMixedNativeReturn SourceGammaNativeBudget SourceEscapeCurrent SourceMinimalGraphParticular
open SourcePhysicalHamiltonianSquare SourceCoframeVolumeCurrent SourceScalarPairedTransport
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart FullYSourceResolventGraphSplice
open SourceScalarRadialContact (scalarEulerAction scalar_native_contraction scalar_adjoint_contraction radialAdjoint radialMomentum)
open SourceHamiltonianScaleJet SourceCoframeDilation SourceCoframeVolume SourceDilationRemainder
open scoped ContDiff InnerProductSpace BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
private abbrev OriginalCore : Type := diagonal.domain

private theorem potential_real (m ell : ℕ) (f : QuantumTest) :
    (potentialAction m ell f : SourceCoordinateSlice → FockFiber)=
      fun z => radialPotential m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem multiplier_commutes (m ell : ℕ)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) (potentialAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (radialPotential m ell z : ℂ) (f z)

private theorem real_commutes (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c smooth) (potentialAction m ell) := multiplier_commutes _ _ _ _

private theorem paired_commutes (m ell : ℕ) (A B : CoreEnd)
    (pair : GaussCoframeForm.Paired B A) (hc : Commute A (potentialAction m ell)) :
    Commute B (potentialAction m ell) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (B (potentialAction m ell g))=
    sourcePair f (potentialAction m ell (B g))
  have he : A (potentialAction m ell f)=potentialAction m ell (A f) := LinearMap.congr_fun hc.eq f
  calc
    _=sourcePair (A f) (potentialAction m ell g) := pair _ _
    _=sourcePair (potentialAction m ell (A f)) g := potential_pair _ _ _ _
    _=sourcePair (A (potentialAction m ell f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (potentialAction m ell f) (B g) := (pair _ _).symm
    _=_ := (potential_pair _ _ _ _).symm

private theorem potential_coframe_derivative (m ell : ℕ) (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ (radialPotential m ell) z (GaussCoframeCore.coframeDirection i)=0 := by
  have hd := ((potential_smooth m ell).differentiable (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z+r • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => radialPotential m ell (z+r • GaussCoframeCore.coframeDirection i))=
      (fun _ => radialPotential m ell z) := by
    funext r
    simp [radialPotential,primitivePower,radius,GaussCoframeCore.coframeDirection]
  change HasDerivAt (fun r : ℝ => radialPotential m ell (z+r • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ (radialPotential m ell) z (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem coframe_derivative (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (potentialAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative _ (potentialAction m ell f) z=
    potentialAction m ell (GaussCoframeCore.derivative _ f) z
  rw [GaussCoframeCore.derivative_apply,potential_real,
    fderiv_fun_smul ((potential_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change radialPotential m ell z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ (radialPotential m ell) z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [potential_coframe_derivative,zero_smul,add_zero]
  change _=(radialPotential m ell z : ℂ) • GaussCoframeCore.derivative _ f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem coframe_momentum (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.momentum i) (potentialAction m ell) :=
  (coframe_derivative m ell i).smul_left (-Complex.I)

private theorem coframe_adjoint (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.adjoint i) (potentialAction m ell) :=
  paired_commutes m ell _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum m ell i)

private theorem quantum_commutes (m ell : ℕ) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) (potentialAction m ell) := multiplier_commutes _ _ _ _

private theorem end_sum_commute {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (B : R)
    (h : ∀ i, Commute (A i) B) : Commute (∑ i, A i) B := by
  change (∑ i, A i)*B=B*(∑ i, A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (h i).eq)

private theorem end_smul_commute {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (c : ℂ) (A B : R) (h : Commute A B) : Commute (c • A) B := by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem end_mul_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB

private theorem end_add_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A+B) C := hA.add_left hB

private theorem coframe_kinetic (m ell : ℕ) :
    Commute GaussCoframeKinetic.kinetic (potentialAction m ell) := by
  change Commute (∑ i : Fin 6, ∑ j : Fin 6, GaussCoframeKinetic.term i j) (potentialAction m ell)
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro j
  change Commute (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) (potentialAction m ell)
  apply end_mul_commute (R := CoreEnd)
  · exact coframe_adjoint m ell i
  · apply end_mul_commute (R := CoreEnd)
    · exact real_commutes m ell _ _
    · exact coframe_momentum m ell j

private theorem coframe_current (m ell : ℕ) (a : Fin 7) :
    Commute (GaussCoframeSpin.current a) (potentialAction m ell) := quantum_commutes _ _ _ _

private theorem coframe_mixed (m ell : ℕ) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) (potentialAction m ell) := by
  change Commute ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c smooth*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c smooth*GaussCoframeSpin.current a))) (potentialAction m ell)
  apply end_smul_commute (R := CoreEnd)
  apply end_add_commute (R := CoreEnd)
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_current m ell a
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes m ell c smooth
      · exact coframe_momentum m ell i
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_adjoint m ell i
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes m ell c smooth
      · exact coframe_current m ell a

private theorem coframe_commutes (m ell : ℕ) :
    Commute GaussCoframeForm.coframeAction (potentialAction m ell) := by
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction
    GaussCoframeForm.spinSquare GaussCoframeForm.numberShift
  apply end_add_commute (R := CoreEnd)
  · apply end_add_commute (R := CoreEnd)
    · apply end_add_commute (R := CoreEnd)
      · apply end_add_commute (R := CoreEnd)
        · exact coframe_kinetic m ell
        · apply end_add_commute (R := CoreEnd)
          · apply end_add_commute (R := CoreEnd)
            · apply end_add_commute (R := CoreEnd)
              · exact coframe_mixed _ _ _ _ _ _
              · exact coframe_mixed _ _ _ _ _ _
            · exact coframe_mixed _ _ _ _ _ _
          · exact coframe_mixed _ _ _ _ _ _
      · apply end_sum_commute (R := CoreEnd)
        intro a
        apply end_smul_commute (R := CoreEnd)
        change Commute (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume
          GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current a)) (potentialAction m ell)
        apply end_mul_commute (R := CoreEnd)
        · exact coframe_current m ell a
        · apply end_mul_commute (R := CoreEnd)
          · exact real_commutes _ _ _ _
          · exact coframe_current m ell a
    · apply end_smul_commute (R := CoreEnd)
      change Commute (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number) (potentialAction m ell)
      apply end_add_commute (R := CoreEnd)
      · apply end_mul_commute (R := CoreEnd)
        · exact quantum_commutes _ _ _ _
        · exact real_commutes _ _ _ _
      · apply end_mul_commute (R := CoreEnd)
        · exact real_commutes _ _ _ _
        · exact quantum_commutes _ _ _ _
  · exact real_commutes _ _ _ _

private theorem matter_commutes (m ell : ℕ) :
    Commute GaussMatterCore.matterAction (potentialAction m ell) := by
  unfold GaussMatterCore.matterAction
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro a
  exact quantum_commutes _ _ _ _

def momentumContact (m ell : ℕ) (v : Ambient) : CoreEnd :=
  (-Complex.I) • (SourceClosedCostNativeProbe.coordinateAction v*thetaAction m ell)

private theorem contact_pair (m ell : ℕ) (v : Ambient) (f g : QuantumTest) :
    sourcePair f (momentumContact m ell v g)= -sourcePair (momentumContact m ell v f) g := by
  have h (f g : QuantumTest) :
      sourcePair f (SourceClosedCostNativeProbe.coordinateAction v (thetaAction m ell g))=
        sourcePair (SourceClosedCostNativeProbe.coordinateAction v (thetaAction m ell f)) g := by
    have ht : SourceNativeCutoffContact.thetaAction m ell=thetaAction m ell :=
      SourceNativeCutoffContact.theta_action_polynomial m ell
    rw [←ht]
    have hc : SourceNativeCutoffContact.thetaAction m ell (SourceClosedCostNativeProbe.coordinateAction v f)=
        SourceClosedCostNativeProbe.coordinateAction v (SourceNativeCutoffContact.thetaAction m ell f) := by
      apply DFunLike.ext
      intro z
      exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ)
        (SourceClosedCostNativeProbe.coordinate v z : ℂ) (f z)
    exact (multiply_pair _ _ f _).trans ((multiply_pair _ _ _ g).trans
      (congrArg (fun q : QuantumTest => sourcePair q g) hc))
  change inner ℂ (embed f) (embed ((-Complex.I) • _))= -inner ℂ (embed ((-Complex.I) • _)) (embed g)
  rw [map_smul,map_smul,inner_smul_right,inner_smul_left]
  change (-Complex.I)*sourcePair f (SourceClosedCostNativeProbe.coordinateAction v (thetaAction m ell g))=_
  rw [h]
  simp only [map_neg,Complex.conj_I,neg_neg,neg_mul]
  rfl

private theorem sharp_potential (m ell : ℕ) (v : Ambient) (g : QuantumTest) :
    GaussMomentumAdjoint.adjoint v (potentialAction m ell g)=
      potentialAction m ell (GaussMomentumAdjoint.adjoint v g)+momentumContact m ell v g := by
  apply SourceCoframeVolume.pair_ext
  intro f
  have h1 := GaussNativeForm.adjoint_pair v f (potentialAction m ell g)
  have h2 := potential_pair m ell (covariantMomentum v f) g
  have h3 := GaussNativeForm.adjoint_pair v (potentialAction m ell f) g
  have h4 := potential_pair m ell f (GaussMomentumAdjoint.adjoint v g)
  have h5 := contact_pair m ell v f g
  rw [momentum_potential] at h3
  change sourcePair (potentialAction m ell f) (GaussMomentumAdjoint.adjoint v g)=
    inner ℂ (embed (potentialAction m ell (covariantMomentum v f)+momentumContact m ell v f)) (embed g) at h3
  rw [map_add,inner_add_left] at h3
  change sourcePair f (GaussMomentumAdjoint.adjoint v (potentialAction m ell g))=
    inner ℂ (embed f) (embed (potentialAction m ell (GaussMomentumAdjoint.adjoint v g)+momentumContact m ell v g))
  rw [map_add,inner_add_right]
  change _=sourcePair f (potentialAction m ell (GaussMomentumAdjoint.adjoint v g))+sourcePair f (momentumContact m ell v g)
  rw [h1,h2,h4,h3,h5]
  unfold sourcePair
  ring

private theorem gauge_momentum (m ell : ℕ) (v : Ambient) (hv : v.1=0) :
    Commute (covariantMomentum v) (potentialAction m ell) := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (potentialAction m ell f)=potentialAction m ell (covariantMomentum v f)
  rw [momentum_potential]
  have hq : SourceClosedCostNativeProbe.coordinateAction v=0 := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    change (inner ℝ (z.2.1 : Scalar) v.1 : ℂ) • f z=0
    rw [hv,inner_zero_right,Complex.ofReal_zero,zero_smul]
  rw [hq,LinearMap.zero_apply,smul_zero,add_zero]

private theorem gauge_adjoint (m ell : ℕ) (v : Ambient) (hv : v.1=0) :
    Commute (GaussMomentumAdjoint.adjoint v) (potentialAction m ell) :=
  paired_commutes m ell _ _ (GaussNativeForm.adjoint_pair v) (gauge_momentum m ell v hv)

private theorem gauge_commutes (m ell : ℕ) : Commute gaugeKinetic (potentialAction m ell) := by
  unfold gaugeKinetic
  apply end_smul_commute (R := CoreEnd)
  apply end_sum_commute (R := CoreEnd)
  intro a
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) (potentialAction m ell)
  apply end_mul_commute (R := CoreEnd)
  · exact gauge_adjoint m ell _ rfl
  · apply end_mul_commute (R := CoreEnd)
    · exact real_commutes _ _ _ _
    · exact gauge_momentum m ell _ rfl

def weightedTheta (m ell : ℕ) : CoreEnd :=
  multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*thetaAction m ell

def radialContact (m ell : ℕ) : CoreEnd := (1/2 : ℂ) •
  (scalarEulerAction*weightedTheta m ell+weightedTheta m ell*scalarEulerAction+(61 : ℂ) • weightedTheta m ell)

private theorem weight_contact (a : ScalarIndex) (m ell : ℕ) :
    multiply scalarWeight scalarWeight_smooth*momentumContact m ell (scalarDirection a)=
      Complex.I • (SourceGammaNativeBudget.scalarColumn a*weightedTheta m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (scalarWeight z : ℂ)*((-Complex.I)*
      ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*(thetaAction m ell f z word)))=
    Complex.I*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*
      ((GaussCoframeForm.inverseVolume z : ℂ)*(thetaAction m ell f z word)))
  unfold scalarWeight GaussCoframeForm.inverseVolume
  push_cast
  ring

private theorem contact_weight (a : ScalarIndex) (m ell : ℕ) :
    momentumContact m ell (scalarDirection a)*multiply scalarWeight scalarWeight_smooth=
      Complex.I • (weightedTheta m ell*SourceGammaNativeBudget.scalarColumn a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have ht : SourceNativeCutoffContact.thetaAction m ell=thetaAction m ell :=
    SourceNativeCutoffContact.theta_action_polynomial m ell
  simp only [momentumContact,weightedTheta,←ht,Module.End.mul_apply,LinearMap.smul_apply]
  apply PiLp.ext
  intro word
  change (-Complex.I)*((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*
      ((SourceNativeCutoffContact.theta m ell z : ℂ)*((scalarWeight z : ℂ)*f z word)))=
    Complex.I*((GaussCoframeForm.inverseVolume z : ℂ)*
      ((SourceNativeCutoffContact.theta m ell z : ℂ)*
        ((SourceClosedCostNativeProbe.coordinate (scalarDirection a) z : ℂ)*f z word)))
  unfold scalarWeight GaussCoframeForm.inverseVolume
  push_cast
  ring

private theorem sandwich_contact {R : Type*} [Ring R] (a b w t c : R)
    (ha : a*t=t*a+c) (hb : b*t=t*b+c) (hw : w*t=t*w) :
    (a*w*b)*t=t*(a*w*b)+(a*w*c+c*w*b) := by
  calc
    _=a*w*(b*t) := by noncomm_ring
    _=a*w*(t*b+c) := by rw [hb]
    _=a*(w*t)*b+a*w*c := by noncomm_ring
    _=(a*t)*w*b+a*w*c := by rw [hw]; noncomm_ring
    _=_ := by rw [ha]; noncomm_ring

private theorem scalar_contact (m ell : ℕ) :
    scalarKinetic*potentialAction m ell=potentialAction m ell*scalarKinetic+radialContact m ell := by
  let K : CoreEnd := (1/2 : ℂ) • ∑ a : ScalarIndex,
    (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      momentumContact m ell (scalarDirection a)+
    momentumContact m ell (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      covariantMomentum (scalarDirection a))
  have hs (a : ScalarIndex) :
      sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth*potentialAction m ell=
      potentialAction m ell*sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth+
        (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          momentumContact m ell (scalarDirection a)+
        momentumContact m ell (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
          covariantMomentum (scalarDirection a)) := by
    have ha : GaussMomentumAdjoint.adjoint (scalarDirection a)*potentialAction m ell=
        potentialAction m ell*GaussMomentumAdjoint.adjoint (scalarDirection a)+momentumContact m ell (scalarDirection a) :=
      LinearMap.ext (sharp_potential m ell (scalarDirection a))
    have hb : covariantMomentum (scalarDirection a)*potentialAction m ell=
        potentialAction m ell*covariantMomentum (scalarDirection a)+momentumContact m ell (scalarDirection a) :=
      LinearMap.ext (momentum_potential m ell (scalarDirection a))
    simpa only [sandwich,←Module.End.mul_eq_comp,mul_assoc] using!
      sandwich_contact (R := CoreEnd) _ _ _ _ _ ha hb (real_commutes m ell _ _).eq
  have hK : scalarKinetic*potentialAction m ell=potentialAction m ell*scalarKinetic+K := by
    simp only [scalarKinetic,K,smul_mul_assoc,Finset.sum_mul,hs,Finset.sum_add_distrib,
      ←Finset.mul_sum,mul_smul_comm,smul_add]
  have hr : K=(Complex.I/2) • (radialAdjoint*weightedTheta m ell+weightedTheta m ell*radialMomentum) := by
    dsimp only [K]
    simp only [mul_assoc,weight_contact,contact_weight,mul_smul_comm,smul_mul_assoc,
      ←smul_add,←Finset.smul_sum,smul_smul,Finset.sum_add_distrib]
    simp only [radialAdjoint,radialMomentum,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    congr 1
    ring
  have hi : (Complex.I/2)*(-Complex.I)=(1/2 : ℂ) := by
    calc _=(-Complex.I*Complex.I)/2 := by ring
         _=1/2 := by rw [neg_mul,Complex.I_mul_I,neg_neg]
  have he : K=radialContact m ell := by
    rw [hr,scalar_native_contraction,scalar_adjoint_contraction]
    simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
    rw [smul_smul,hi]
    simp only [add_mul,smul_mul_assoc,one_mul,radialContact]
    module
  exact hK.trans (congrArg (fun A : CoreEnd => potentialAction m ell*scalarKinetic+A) he)

/-- All nonscalar terms of the original action commute with b; its whole force is this scalar61 current. -/
theorem full_potential_contact (m ell : ℕ) :
    diagonalAction*potentialAction m ell-potentialAction m ell*diagonalAction=radialContact m ell := by
  have hn : nativeAction*potentialAction m ell=
      potentialAction m ell*nativeAction+radialContact m ell := by
    change (scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
      GaussNativePotential.potential_smooth)*potentialAction m ell=_
    rw [add_mul,add_mul,scalar_contact,(gauge_commutes m ell).eq,(real_commutes _ _ _ _).eq]
    change _=potentialAction m ell*(scalarKinetic+gaugeKinetic+multiply _ _)+radialContact m ell
    noncomm_ring
  change (nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*potentialAction m ell-
    potentialAction m ell*(nativeAction+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)=_
  rw [add_mul,add_mul,hn,(coframe_commutes m ell).eq,(matter_commutes m ell).eq]
  noncomm_ring

theorem potential_scale_zero (m ell : ℕ) : scaleDerivative (potentialAction m ell)=0 := by
  have he (z : physicalChart) :
      fderiv ℝ (radialPotential m ell) z.val (euler z.val)=(0 : ℝ)*radialPotential m ell z.val := by
    simpa only [Int.cast_zero] using SourceKineticScale.euler_of_scale _ 0 z (potential_smooth m ell).contDiffAt
      (fun _ _ => by simp only [zpow_zero,one_mul]; rfl)
  have h := SourceDilationMultiplier.homogeneous_multiplier (radialPotential m ell)
    (fun _ => (potential_smooth m ell).contDiffAt) 0 he
  change dilation*potentialAction m ell-potentialAction m ell*dilation=_ at h
  simp only [Complex.ofReal_zero,mul_zero,zero_smul] at h
  change (3*Complex.I/2) • (dilation*potentialAction m ell-potentialAction m ell*dilation)=0
  rw [h,smul_zero]

private theorem scale_product (A B : CoreEnd) :
    scaleDerivative (A*B)=scaleDerivative A*B+A*scaleDerivative B := by
  change (3*Complex.I/2) • (dilation*(A*B)-(A*B)*dilation)=
    ((3*Complex.I/2) • (dilation*A-A*dilation))*B+A*((3*Complex.I/2) • (dilation*B-B*dilation))
  simp only [smul_mul_assoc,mul_smul_comm,←smul_add]
  congr 1
  noncomm_ring

private theorem scale_contact (m ell : ℕ) (A : CoreEnd) :
    scaleDerivative (A*potentialAction m ell-potentialAction m ell*A)=
      scaleDerivative A*potentialAction m ell-potentialAction m ell*scaleDerivative A := by
  rw [map_sub,scale_product,scale_product,potential_scale_zero]
  simp only [mul_zero,zero_mul,add_zero,zero_add]

/-- P(delta) annihilates the whole b-contact by the actual full-H local-potential producer. -/
theorem full_contact_scale_polynomial (m ell : ℕ) :
    scaleDerivative (scaleDerivative (scaleDerivative (radialContact m ell)))+
      (3 : ℂ) • scaleDerivative (scaleDerivative (radialContact m ell))-
      scaleDerivative (radialContact m ell)-(3 : ℂ) • radialContact m ell=0 := by
  rw [←full_potential_contact]
  simp only [scale_contact]
  have hlocal : localAction*potentialAction m ell=potentialAction m ell*localAction :=
    (real_commutes m ell _ _).eq
  have hp := congrArg (fun A : CoreEnd => A*potentialAction m ell-potentialAction m ell*A)
    source_local_from_scale_jet
  simp only [add_mul,sub_mul,mul_add,mul_sub,smul_mul_assoc,mul_smul_comm,hlocal,sub_self] at hp
  convert! hp using 1
  module

/-- Original compression and both full defects remain in the single source radial correction. -/
def radialCorrection (m ell : ℕ) (F : Index) (q : QuantumTest) : H :=
  embed (radialContact m ell q)+embed (potentialAction m ell (defectAction F q))-
    embed (defectAction F (potentialAction m ell q))

theorem actual_radial_correction (m ell : ℕ) (F : Index) (q : QuantumTest) :
    transportCorrection F (potentialAction m ell) q=radialCorrection m ell F q := by
  simp only [transportCorrection,full_potential_contact,radialCorrection]

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- The four terms carrying b-force are kept as one antisymmetric radial response. -/
def radialResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : ℂ :=
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  inner ℂ (embed (scalarMomentumAdjoint sharp p)) (finiteResolvent F z (radialCorrection m ell F q))-
    inner ℂ (finiteResolvent F (star z) (radialCorrection m ell F p)) (embed (scalarMomentum sharp q))

def momentumResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : ℂ :=
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  inner ℂ (finiteResolvent F (star z) (transportCorrection F (scalarMomentumAdjoint sharp) p))
    (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))-
  inner ℂ (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
    (finiteResolvent F z (transportCorrection F (scalarMomentum sharp) q))

private theorem six_group {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b c d e f h j : E) :
    inner ℂ a d+inner ℂ b c+inner ℂ b d-inner ℂ e j-inner ℂ f h-inner ℂ f j=
      (inner ℂ (a+b) d-inner ℂ f (h+j))+(inner ℂ b c-inner ℂ e j) := by
  simp only [inner_add_left,inner_add_right]
  ring

/-- All six actual relative terms consume the full original radial contact, with no separate-leg estimate. -/
theorem actual_six_radial_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) : signedCorrection sharp m ell F z hz g k=
      radialResponse sharp m ell F z hz g k+momentumResponse sharp m ell F z hz g k := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hl := actual_relative_transport F (scalarMomentumAdjoint sharp) (star z) (star_im_ne z hz) k
  have hr := actual_relative_transport F (scalarMomentum sharp) z hz g
  have hs := six_group
    (finiteResolvent F (star z) (embed (scalarMomentumAdjoint sharp (coreEquiv.symm k))))
    (finiteResolvent F (star z) (transportCorrection F (scalarMomentumAdjoint sharp) p))
    (finiteResolvent F z (embed (potentialAction m ell (coreEquiv.symm g))))
    (finiteResolvent F z (transportCorrection F (potentialAction m ell) q))
    (finiteResolvent F (star z) (embed (potentialAction m ell (coreEquiv.symm k))))
    (finiteResolvent F (star z) (transportCorrection F (potentialAction m ell) p))
    (finiteResolvent F z (embed (scalarMomentum sharp (coreEquiv.symm g))))
    (finiteResolvent F z (transportCorrection F (scalarMomentum sharp) q))
  have hbq := congrArg (finiteResolvent F z) (actual_radial_correction m ell F q)
  have hbp := congrArg (finiteResolvent F (star z)) (actual_radial_correction m ell F p)
  have ha := congrArg₂ (inner ℂ) hl.symm hbq
  have hb := congrArg₂ (inner ℂ) hbp hr.symm
  exact hs.trans (congrArg (fun c : ℂ => c+momentumResponse sharp m ell F z hz g k)
    (congrArg₂ (fun a b : ℂ => a-b) ha hb))

/-- Literal Gamma returns the two fixed profiles and the complete radial/momentum signed cross. -/
theorem actual_gamma_radial_return (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : OriginalCore) :
    sourceGamma sharp m ell F g k z=
      (-96*(sourceTime 0 : ℂ)^2)*(Complex.I*(fixedProfiles sharp m ell F z g k+
        (radialResponse sharp m ell F z hz g k+momentumResponse sharp m ell F z hz g k)))-
      Complex.I*inner ℂ (Subtype.val k)
        ((sourceRead F g (primitive sharp m ell)*SourceMovingJetFlux.orbitWord F z-
          SourceMovingJetFlux.orbitWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g)) := by
  exact (actual_gamma_paired_return sharp m ell F z hz g k).trans
    (congrArg (fun s : ℂ => (-96*(sourceTime 0 : ℂ)^2)*(Complex.I*(fixedProfiles sharp m ell F z g k+s))-
      Complex.I*inner ℂ (Subtype.val k)
        ((sourceRead F g (primitive sharp m ell)*SourceMovingJetFlux.orbitWord F z-
          SourceMovingJetFlux.orbitWord F z*sourceRead F g (primitive sharp m ell)) (Subtype.val g)))
      (actual_six_radial_return sharp m ell F z hz g k))

private theorem core_embed (x : OriginalCore) : embed (coreEquiv.symm x)=Subtype.val x :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

private theorem contact_green (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (radialContact m ell q)=
      sourcePair (diagonalAction p) (potentialAction m ell q)-
        sourcePair (potentialAction m ell p) (diagonalAction q) := by
  rw [←full_potential_contact]
  change inner ℂ (embed p) (embed (diagonalAction (potentialAction m ell q)-
    potentialAction m ell (diagonalAction q)))=_
  rw [map_sub,inner_sub_right]
  exact congrArg₂ (fun a b : ℂ => a-b) (diagonalAction_pair p _)
    (potential_pair m ell p _)

def radialWard (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) : ℂ :=
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  sourcePair p (radialContact m ell q)-
    inner ℂ (finiteProjectionDefect F (star z) (star_im_ne z hz) k) (embed (potentialAction m ell q))+
    inner ℂ (embed (potentialAction m ell p)) (finiteProjectionDefect F z hz g)

private theorem green_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (z : ℂ) (p q k g dp dq bp bq bk bg : E)
    (hpq : inner ℂ p bq=inner ℂ bp q) (hkq : inner ℂ k bq=inner ℂ bk q)
    (hpg : inner ℂ bp g=inner ℂ p bg) :
    (inner ℂ (k+star z • p+dp) bq-inner ℂ bp (g+z • q+dq))-
      inner ℂ dp bq+inner ℂ bp dq=inner ℂ bk q-inner ℂ p bg := by
  rw [inner_add_left,inner_add_left,inner_smul_left,starRingEnd_apply,star_star,
    inner_add_right,inner_add_right,inner_smul_right,hpq,hkq,hpg]
  ring

/-- The true radial61 current and its two original defects return fixed b-sources; b need not be bounded on H. -/
theorem actual_radial_ward (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : OriginalCore) :
    radialWard m ell F z hz g k=
      inner ℂ (embed (potentialAction m ell (coreEquiv.symm k))) (finiteResolvent F z (Subtype.val g))-
        inner ℂ (finiteResolvent F (star z) (Subtype.val k))
          (embed (potentialAction m ell (coreEquiv.symm g))) := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hp := source_core_action F (star z) (star_im_ne z hz) k
  have hq := source_core_action F z hz g
  have hcontact := (contact_green m ell p q).trans
    (congrArg₂ (fun a b : ℂ => a-b) (congrArg (fun x : H => inner ℂ x (embed (potentialAction m ell q))) hp)
      (congrArg (fun x : H => inner ℂ (embed (potentialAction m ell p)) x) hq))
  have hpq := potential_pair m ell p q
  have hkq := potential_pair m ell (coreEquiv.symm k) q
  have hpg := (potential_pair m ell p (coreEquiv.symm g)).symm
  simp only [sourcePair,p,q,core_embed] at hpq hkq hpg
  change sourcePair p (radialContact m ell q)-
    inner ℂ (finiteProjectionDefect F (star z) (star_im_ne z hz) k) (embed (potentialAction m ell q))+
    inner ℂ (embed (potentialAction m ell p)) (finiteProjectionDefect F z hz g)=_
  rw [hcontact]
  exact green_algebra z _ _ _ _ _ _ _ _ _ _ hpq hkq hpg

end LowEnergy.SourcePairedRadialFlux
