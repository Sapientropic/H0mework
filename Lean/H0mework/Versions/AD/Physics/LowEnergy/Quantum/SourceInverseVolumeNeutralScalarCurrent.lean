import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeNeutralSplice
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeMagneticForceCancellation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseNeutralScalarCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open SourceInverseGaugeSingleDefectJoin SourceInverseCompressionCurrent SourceInverseHamiltonianForceReduction SourceInverseMagneticForceCancellation
open SourceInverseCoframeNeutralBudget SourceScalarRadialContact SourceNativeCutoffContact
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceCoframeVolumeCurrent GaussLiveMomentum
open scoped ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  SourceMixedNativeReturn.thetaAction SourceScalarDoubleCurrent.fullInsertion
  neutralCurrent firstHamiltonianCurrent matterInsertion scalarEulerAction weightedProfileAction

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


private theorem pair_smul_right (f g : QuantumTest) (c : ℂ) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]


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


private theorem coframe_kinetic_full (sharp : Bool) : Commute GaussCoframeKinetic.kinetic (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeKinetic.kinetic
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro j _
  unfold GaussCoframeKinetic.term
  exact (coframe_full_adjoint i sharp).mul_left ((real_full _ _ sharp).mul_left (coframe_full j sharp))

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

private theorem mixed_full (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool)
    (hs : Commute (GaussCoframeSpin.current a) (SourceMixedNativeReturn.fullAction sharp)) :
    Commute (GaussCoframeForm.mixed i a c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeForm.mixed
  simp only [←Module.End.mul_eq_comp]
  exact ((hs.mul_left ((real_full c hc sharp).mul_left (coframe_full i sharp))).add_left
    ((coframe_full_adjoint i sharp).mul_left ((real_full c hc sharp).mul_left hs))).smul_left _

/-- The actual four coframe derivative couplings commute with both repaired Yukawa branches. -/
theorem original_coframe_current_full (sharp : Bool) :
    Commute GaussCoframeForm.currentAction (SourceMixedNativeReturn.fullAction sharp) := by
  unfold GaussCoframeForm.currentAction
  exact (((mixed_full 1 5 _ _ sharp (spatial_spin_full 2 sharp)).add_left
    (mixed_full 3 3 _ _ sharp (spatial_spin_full 0 sharp))).add_left
    (mixed_full 3 4 _ _ sharp (spatial_spin_full 1 sharp))).add_left
    (mixed_full 4 3 _ _ sharp (spatial_spin_full 0 sharp))

/-- The remaining coframe contribution contains no derivative of a test input. -/
def spinPotential : End := (∑ a : Fin 7,GaussCoframeForm.spinSquare a)+GaussCoframeForm.numberShift

def spinCurrent (sharp : Bool) : End := bracket spinPotential (SourceMixedNativeReturn.fullAction sharp)

private theorem bracket_add {R : Type*} [Ring R] (A B C : R) :
    bracket (A+B) C=bracket A C+bracket B C := by unfold bracket;noncomm_ring

private theorem bracket_mul {R : Type*} [Ring R] (A B C : R) :
    bracket A (B*C)=bracket A B*C+B*bracket A C := by unfold bracket;noncomm_ring

private theorem bracket_commute {R : Type*} [Ring R] {A B : R} (h : Commute A B) : bracket A B=0 :=
  sub_eq_zero.mpr h.eq

private theorem coframe_full_return (sharp : Bool) :
    bracket GaussCoframeForm.coframeAction (SourceMixedNativeReturn.fullAction sharp)=spinCurrent sharp := by
  have hcf : GaussCoframeForm.coframeAction=GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
      spinPotential+multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth := by
    unfold GaussCoframeForm.coframeAction spinPotential
    abel
  rw [hcf]
  simp only [bracket_add,bracket_commute (coframe_kinetic_full sharp),
    bracket_commute (original_coframe_current_full sharp),bracket_commute (real_full _ _ sharp),zero_add,add_zero]
  rfl

/-- Original negative scalarWeight and all seventy native scalar momenta are retained. -/
def scalarCurrent (sharp : Bool) : End := (-Complex.I/2 : ℂ) • ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*
      constantAction sharp (scalarDirection a).1+
    constantAction sharp (scalarDirection a).1*multiply scalarWeight scalarWeight_smooth*
      covariantMomentum (scalarDirection a))

private theorem sandwich_current {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R] (P A w X C : R)
    (hP : bracket P X=(-Complex.I) • C) (hA : bracket A X=(-Complex.I) • C)
    (hw : Commute w X) :
    bracket (A*(w*P)) X=(-Complex.I) • (A*w*C+C*w*P) := by
  have he : bracket (A*(w*P)) X=A*w*bracket P X+bracket A X*w*P := by
    unfold bracket
    linear_combination (norm := noncomm_ring) A*hw.eq*P
  rw [he,hP,hA]
  simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]

/-- The bare scalar kinetic commutator is a first-order anticommutator, not a second-order moving input. -/
theorem original_scalar_first_current (sharp : Bool) :
    bracket scalarKinetic (SourceMixedNativeReturn.fullAction sharp)=scalarCurrent sharp := by
  have h (a : ScalarIndex) := sandwich_current (covariantMomentum (scalarDirection a))
    (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (SourceMixedNativeReturn.fullAction sharp) (constantAction sharp (scalarDirection a).1)
    (native_full_current sharp _) (native_full_adjoint sharp _) (real_full _ _ sharp)
  unfold scalarKinetic scalarCurrent sandwich
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,←smul_sub]
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => h a)
  simp only [bracket] at he
  rw [he,←Finset.smul_sum,smul_smul]
  congr 1
  ring

def radialCurrent (m ell : ℕ) : End := (1/2 : ℂ) •
  (scalarEulerAction*weightedProfileAction m ell+weightedProfileAction m ell*scalarEulerAction+
    (61 : ℂ) • weightedProfileAction m ell)

/-- Scalar first derivatives and a zero-order spin/number term exhaust the actual neutral current. -/
def scalarNeutral (sharp : Bool) (m ell : ℕ) : End :=
  (scalarCurrent sharp+spinCurrent sharp)*SourceMixedNativeReturn.thetaAction m ell+
    SourceMixedNativeReturn.fullAction sharp*radialCurrent m ell

private theorem real_matter (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) matterAction := by
  unfold matterAction
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact real_local _ _ _ _

private theorem matter_theta (m ell : ℕ) : Commute matterAction (SourceMixedNativeReturn.thetaAction m ell) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact (real_matter _ _).symm

private theorem neutral_product {R : Type*} [Ring R] (H M Y T C J : R)
    (hC : bracket H Y=bracket M Y+C) (hJ : bracket H T=J) (hM : Commute M T) :
    bracket H (Y*T)-bracket M (Y*T)=C*T+Y*J := by
  rw [bracket_mul,bracket_mul,hC,hJ,bracket_commute hM,mul_zero,add_zero]
  noncomm_ring

/-- The complete Q=B−W loses every coframe derivative of the moving state. -/
theorem original_neutral_scalar_return (sharp : Bool) (m ell : ℕ) :
    neutralCurrent sharp m ell=scalarNeutral sharp m ell := by
  have hC : bracket diagonalAction (SourceMixedNativeReturn.fullAction sharp)=
      bracket matterAction (SourceMixedNativeReturn.fullAction sharp)+scalarCurrent sharp+spinCurrent sharp := by
    unfold diagonalAction nativeAction
    simp only [bracket_add,bracket_commute (original_electric_full sharp),
      bracket_commute (real_full potential potential_smooth sharp),original_scalar_first_current,
      coframe_full_return]
    abel
  have hJ : bracket diagonalAction (SourceMixedNativeReturn.thetaAction m ell)=radialCurrent m ell :=
    original_hamiltonian_radial_contact m ell
  have h := neutral_product diagonalAction matterAction (SourceMixedNativeReturn.fullAction sharp)
    (SourceMixedNativeReturn.thetaAction m ell) (scalarCurrent sharp+spinCurrent sharp) (radialCurrent m ell)
    (hC.trans (add_assoc _ _ _)) hJ (matter_theta m ell)
  simpa only [neutralCurrent,firstHamiltonianCurrent,matterInsertion,
    SourceScalarDoubleCurrent.fullInsertion,scalarNeutral] using h

def spinKernel (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (∑ a : Fin 7,(GaussCoframeForm.spinWeight a : ℂ) •
    (quantized (GaussCoframeSpin.full a)*((GaussCoframeForm.inverseVolume z : ℂ) •
      quantized (GaussCoframeSpin.full a))))+
  (GaussCoframeForm.numberCoefficient z : ℂ) • quantized (Matrix.diagonal (fun _ : Mode => (1 : ℂ)))

private theorem spin_action_at (a : Fin 7) (f : QuantumTest) (z : SourceCoordinateSlice) :
    GaussCoframeSpin.current a f z=quantized (GaussCoframeSpin.full a) (f z) := rfl

private theorem number_action_at (f : QuantumTest) (z : SourceCoordinateSlice) :
    GaussCoframeForm.number f z=quantized (Matrix.diagonal (fun _ : Mode => (1 : ℂ))) (f z) := rfl

private theorem spin_at (f : QuantumTest) (z : SourceCoordinateSlice) :
    spinPotential f z=spinKernel z (f z) := by
  simp only [spinPotential,spinKernel,GaussCoframeForm.spinSquare,GaussCoframeForm.numberShift,
    LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    smul_apply,sum_apply,add_apply,spin_action_at,number_action_at,multiply_apply,map_smul,mul_apply_eq_comp]
  module

/-- The surviving seven spin squares and number term are one literal finite-dimensional multiplier. -/
theorem original_spin_current_apply (sharp : Bool) (f : QuantumTest) (z : SourceCoordinateSlice) :
    spinCurrent sharp f z=bracket (spinKernel z) (branchMap sharp (scalarField z)) (f z) := by
  change spinPotential (SourceMixedNativeReturn.fullAction sharp f) z-
    SourceMixedNativeReturn.fullAction sharp (spinPotential f) z=_
  rw [spin_at,full_at,full_at,spin_at]
  rfl

def scalarCurrentPair (sharp : Bool) (p q : QuantumTest) : ℂ :=
  (-Complex.I/2 : ℂ)*(∑ a : ScalarIndex,
    (sourcePair (covariantMomentum (scalarDirection a) p)
      (multiply scalarWeight scalarWeight_smooth (constantAction sharp (scalarDirection a).1 q))+
    sourcePair (constantAction (!sharp) (scalarDirection a).1 p)
      (multiply scalarWeight scalarWeight_smooth (covariantMomentum (scalarDirection a) q))))

/-- The native adjoint is placed on the actual left input; the right input has only one scalar derivative. -/
theorem original_scalar_current_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (scalarCurrent sharp q)=scalarCurrentPair sharp p q := by
  unfold scalarCurrent scalarCurrentPair
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.add_apply,Module.End.mul_apply,
    sourcePair,map_smul,map_sum,map_add,inner_smul_right,inner_sum,inner_add_right]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg₂ (·+·)
    (GaussNativeForm.adjoint_pair _ p _)
    (SourceMixedNativeReturn.constant_pair sharp (scalarDirection a).1 p _)

private theorem weighted_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (weightedProfileAction m ell q)=sourcePair (weightedProfileAction m ell p) q := by
  unfold weightedProfileAction
  exact multiply_pair _ _ p q

/-- The true scalar dimension 61 cancels in the paired radial anticommutator. -/
theorem original_radial_current_pair (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (radialCurrent m ell q)=(1/2 : ℂ)*
      (sourcePair (weightedProfileAction m ell p) (scalarEulerAction q)-
        sourcePair (scalarEulerAction p) (weightedProfileAction m ell q)) := by
  have h := scalar_euler_current p (weightedProfileAction m ell q)
  have hw := weighted_pair m ell p (scalarEulerAction q)
  simp only [radialCurrent,LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply,
    sourcePair,map_smul,map_add,inner_smul_right,inner_add_right] at h hw ⊢
  linear_combination (norm := ring) (1/2 : ℂ)*h+(1/2 : ℂ)*hw

/-- Both actual dual branches share this complete first-order scalar form, including the zero-order spin multiplier. -/
theorem original_neutral_scalar_pair (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair p (neutralCurrent sharp m ell q)=
      scalarCurrentPair sharp p (SourceMixedNativeReturn.thetaAction m ell q)+
      sourcePair p (spinCurrent sharp (SourceMixedNativeReturn.thetaAction m ell q))+
      (1/2 : ℂ)*(sourcePair (weightedProfileAction m ell (SourceMixedNativeReturn.fullAction (!sharp) p))
          (scalarEulerAction q)-
        sourcePair (scalarEulerAction (SourceMixedNativeReturn.fullAction (!sharp) p))
          (weightedProfileAction m ell q)) := by
  rw [original_neutral_scalar_return]
  have hs (a b : QuantumTest) : sourcePair p (a+b)=sourcePair p a+sourcePair p b := by
    simp only [sourcePair,map_add,inner_add_right]
  simp only [scalarNeutral,LinearMap.add_apply,Module.End.mul_apply,hs]
  rw [original_scalar_current_pair,full_pair,original_radial_current_pair]

open SourceInverseCoframeNeutralSplice SourceScalarPairedTransport FullYSourceResolventGraphSplice
open SourceGaugeCoframeJets SourceScalarForceBudget SourceJointScaleBudget
abbrev Op := H →L[ℂ] H

def scalarReducedRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) : Op :=
  -(1/48 : ℂ) • coframeCubic (fun a => sandwichJet F seed z
    (bracket (defectAction F) (scalarNeutral sharp m ell)) a 0 0 0)+
  (1/48 : ℂ) • coframeRest (fun a =>
    inverseCross F seed z (bracket diagonalAction (scalarNeutral sharp m ell)) a 0+
      finiteResolvent F z*inputFlux F seed (bracket diagonalAction (scalarNeutral sharp m ell)) a 0*finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F seed (neutralContacts sharp m ell)-
    (oscillatorMass : ℂ) • solverOperator sharp m ell F)*finiteResolvent F z

/-- The literal whole-Ward remainder now consumes the first-order scalar source, retaining every H inverse/input correction. -/
theorem actual_scalar_ward_remainder (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain) (z : ℂ) :
    coframeReducedRemainder sharp m ell F seed z=scalarReducedRemainder sharp m ell F seed z := by
  have hc : hamiltonianCoframeCorrection sharp m ell F seed z=(fun a =>
      inverseCross F seed z (bracket diagonalAction (scalarNeutral sharp m ell)) a 0+
        finiteResolvent F z*inputFlux F seed (bracket diagonalAction (scalarNeutral sharp m ell)) a 0*finiteResolvent F z) := by
    funext a
    unfold hamiltonianCoframeCorrection neutralHamiltonianCurrent
    rw [original_neutral_scalar_return]
  simp only [coframeReducedRemainder,scalarReducedRemainder,hc,neutralDefect,original_neutral_scalar_return]

end LowEnergy.SourceInverseNeutralScalarCurrent
