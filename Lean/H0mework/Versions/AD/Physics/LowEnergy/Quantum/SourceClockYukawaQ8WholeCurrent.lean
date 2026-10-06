import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaJointGammaNativeBudget
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaQ8NonScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaQ8WholeCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussQuantumMultiplier
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceClockYukawaSpinClosure SourceClockYukawaSpinNativeJet SourceClockYukawaSpinNativeBudget
open SourceClockYukawaSpinJointForce SourceInverseNeutralSpinCurrent SourceClockYukawaJointGammaNativeBudget
open SourceScalarPositiveBulkWard SourceClockYukawaCubicCurrent
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction compressionCore defectAction diagonalAction

private theorem coefficient_pair (sharp : Bool) (mu : Fin 8) :
    GaussCoframeForm.Paired (spinClosureCoefficient sharp mu) (daggerCoefficient sharp mu) :=
  SourceClockYukawaQ8NonScalar.original_spin_coefficient_pair sharp mu
private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm

private theorem bracket_mul (A B C : End) : bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket
  noncomm_ring
private theorem bracket_sum {ι : Type*} [Fintype ι] (A : End) (B : ι → End) :
    bracket A (∑ i,B i)=∑ i,bracket A (B i) := by
  simp only [bracket,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]
private theorem bracket_add (A B C : End) : bracket A (B+C)=bracket A B+bracket A C := by
  unfold bracket
  noncomm_ring
private theorem bracket_smul (A B : End) (c : ℂ) : bracket A (c • B)=c • bracket A B := by
  simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]

private theorem q8_both : Q8 false=∑ sharp : Bool,∑ mu : Fin 8,
    daggerCoefficient sharp mu*spinClosureCoefficient sharp mu := by
  rw [Fintype.sum_bool,←Finset.sum_add_distrib]
  unfold Q8
  apply Finset.sum_congr rfl
  intro mu _
  change _=(if 0 < mu.val ∧ mu.val<5 then (-1:ℂ) else 1) • spinClosureCoefficient false mu*spinClosureCoefficient true mu+
    (if 0 < mu.val ∧ mu.val<5 then (-1:ℂ) else 1) • spinClosureCoefficient true mu*spinClosureCoefficient false mu
  unfold daggerCoefficient
  simp only [smul_mul_assoc,mul_smul_comm]
  exact add_comm _ _

def hermitianNative (a : ScalarIndex) : End := ∑ sharp : Bool,∑ mu : Fin 8,
  (constantDagger sharp mu a*spinClosureCoefficient sharp mu+
    daggerCoefficient sharp mu*constantCoefficient sharp mu (scalarBasis a))
def scalarSquareCurrent : End := (-Complex.I/2:ℂ) • ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*multiply scalarWeight scalarWeight_smooth*hermitianNative a+
    hermitianNative a*multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))

private theorem dagger_native (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    bracket (covariantMomentum (scalarDirection a)) (daggerCoefficient sharp mu)=
      (-Complex.I) • constantDagger sharp mu a := by
  unfold daggerCoefficient constantDagger
  rw [bracket_smul,original_spin_closure_native_jet]
  exact smul_comm _ _ _
private theorem dagger_adjoint_native (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (daggerCoefficient sharp mu)=
      (-Complex.I) • constantDagger sharp mu a := by
  unfold daggerCoefficient constantDagger
  rw [bracket_smul,original_spin_closure_adjoint_native_jet]
  exact smul_comm _ _ _

/-- The complete Hermitian native coefficient retains both genuine CAR products on all sixteen source rows. -/
theorem original_Q8_native_jet (a : ScalarIndex) :
    bracket (covariantMomentum (scalarDirection a)) (Q8 false)=(-Complex.I) • hermitianNative a ∧
    bracket (GaussMomentumAdjoint.adjoint (scalarDirection a)) (Q8 false)=(-Complex.I) • hermitianNative a := by
  rw [q8_both]
  constructor
  · simp only [bracket_sum,bracket_mul,dagger_native,original_spin_closure_native_jet,
      smul_mul_assoc,mul_smul_comm,←smul_add,←Finset.smul_sum]
    rfl
  · simp only [bracket_sum,bracket_mul,dagger_adjoint_native,original_spin_closure_adjoint_native_jet,
      smul_mul_assoc,mul_smul_comm,←smul_add,←Finset.smul_sum]
    rfl

private theorem real_coefficient (sharp : Bool) (mu : Fin 8) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) (spinClosureCoefficient sharp mu) := by
  have hY : Commute (multiply c hc) (fullAction sharp) := by
    unfold fullAction
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro x
    cases sharp
    · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField x)) (c x:ℂ) (f x)).symm
    · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField x)) (c x:ℂ) (f x)).symm
  have hJ (j : Fin 4) : Commute (multiply c hc) (activeSpin j) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro x
    exact (map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (c x:ℂ) (f x)).symm
  have hb (A B : End) (hA : Commute (multiply c hc) A) (hB : Commute (multiply c hc) B) :
      Commute (multiply c hc) (bracket A B) := (hA.mul_right hB).sub_right (hB.mul_right hA)
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY
  · split
    · exact hb _ _ (hJ _) hY
    · exact hb _ _ (hJ _) (hb _ _ (hJ 3) hY)

private theorem real_Q8 (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) (Q8 false) := by
  rw [q8_both]
  apply Commute.sum_right
  intro sharp _
  apply Commute.sum_right
  intro mu _
  exact ((real_coefficient (!sharp) mu c hc).smul_right _).mul_right (real_coefficient sharp mu c hc)

/-- The original scalar kinetic current of Q8 is a complete native first-order source word. -/
theorem original_scalar_Q8_current : bracket scalarKinetic (Q8 false)=scalarSquareCurrent := by
  have hs (P A w X C : End) (hP : bracket P X=(-Complex.I) • C)
      (hA : bracket A X=(-Complex.I) • C) (hw : Commute w X) :
      bracket (A*(w*P)) X=(-Complex.I) • (A*w*C+C*w*P) := by
    have he : bracket (A*(w*P)) X=A*w*bracket P X+bracket A X*w*P := by
      unfold bracket
      linear_combination (norm := noncomm_ring) A*hw.eq*P
    rw [he,hP,hA]
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,mul_assoc]
  have h (a : ScalarIndex) := hs (covariantMomentum (scalarDirection a))
    (GaussMomentumAdjoint.adjoint (scalarDirection a)) (multiply scalarWeight scalarWeight_smooth)
    (Q8 false) (hermitianNative a) (original_Q8_native_jet a).1 (original_Q8_native_jet a).2
    (real_Q8 scalarWeight scalarWeight_smooth)
  unfold scalarKinetic scalarSquareCurrent sandwich
  simp only [←Module.End.mul_eq_comp,bracket,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,←smul_sub]
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => h a)
  simp only [bracket] at he
  rw [he,←Finset.smul_sum,smul_smul]
  congr 1
  ring

private theorem q8_pair_sum (p q : QuantumTest) : sourcePair p (Q8 false q)=
    ∑ sharp : Bool,∑ mu : Fin 8,sourcePair (spinClosureCoefficient sharp mu p) (spinClosureCoefficient sharp mu q) := by
  rw [q8_both]
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum]
  apply Finset.sum_congr rfl
  intro sharp _
  apply Finset.sum_congr rfl
  intro mu _
  exact paired_symm (coefficient_pair sharp mu) p _

private theorem q8_pair : GaussCoframeForm.Paired (Q8 false) (Q8 false) := by
  intro p q
  rw [q8_pair_sum]
  have h := congrArg (starRingEnd ℂ) (q8_pair_sum q p)
  simp only [map_sum,sourcePair,inner_conj_symm] at h
  exact h.symm

private theorem q8_diag_real (u : QuantumTest) : (sourcePair u (Q8 false u)).im=0 := by
  rw [q8_pair_sum]
  simp only [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro sharp _
  apply Finset.sum_eq_zero
  intro mu _
  change (inner ℂ (embed (spinClosureCoefficient sharp mu u)) (embed (spinClosureCoefficient sharp mu u))).im=0
  exact inner_self_im (𝕜 := ℂ) (embed (spinClosureCoefficient sharp mu u))

open SourceClockYukawaJointSpinRemainingBudget SourceClockYukawaRadialMixedBudget
open SourceClockYukawaRadialMixedClock SourceClockYukawaRadialMixedCore SourceClockYukawaRadialGammaNativeBudget
open SourceRelativePowerTail SourceResolventBandLimit SourceFourPoleEnergyClosed FullYSourceResolventGraphSplice
open MeasureTheory Filter

private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_pair (F : Index) : GaussCoframeForm.Paired (compressionCore F) (compressionCore F) := by
  intro p q
  simp only [sourcePair,compression_embed]
  exact (GaussGradedCompression.compression_pair F _ _).symm
private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

/-- The forcing belongs to the original common radial window; no K- or error-column derivative is introduced. -/
def windowForcing (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (SourceInverseNeutralScalarCurrent.radialCurrent m ell-bracket (defectAction F) (thetaAction m ell))
    (radialMap F z hz (inputCore g))+
    thetaAction m ell ((GaussRadialHamiltonian.radialAction-bracket (defectAction F) inverseAction)
      (resolventCore F z hz (inputCore g)))
def squareCurrent (F : Index) : End := scalarSquareCurrent+
  bracket GaussMatterCore.matterAction (Q8 false)-bracket (defectAction F) (Q8 false)

private theorem square_compression (F : Index) : squareCurrent F=bracket (compressionCore F) (Q8 false) := by
  unfold squareCurrent
  rw [←original_scalar_Q8_current,←SourceClockYukawaQ8NonScalar.original_Q8_hamiltonian_current]
  unfold defectAction bracket
  noncomm_ring

private theorem window_forcing_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    windowForcing m ell F z hz g=
      bracket (compressionCore F) (thetaAction m ell) (radialMap F z hz (inputCore g))+
        thetaAction m ell (bracket (compressionCore F) inverseAction (resolventCore F z hz (inputCore g))) := by
  have hθ : bracket diagonalAction (thetaAction m ell)=SourceInverseNeutralScalarCurrent.radialCurrent m ell :=
    SourceScalarRadialContact.original_hamiltonian_radial_contact m ell
  have hS : bracket diagonalAction inverseAction=GaussRadialHamiltonian.radialAction :=
    sub_eq_iff_eq_add.mpr (GaussRadialHamiltonian.diagonal_commutator.trans (add_comm _ _))
  have h (A : End) : bracket diagonalAction A-bracket (defectAction F) A=bracket (compressionCore F) A := by
    unfold defectAction bracket
    noncomm_ring
  unfold windowForcing
  rw [←hθ,←hS,h,h]

/-- The same compressed resolvent generates the entire common-window source equation. -/
theorem actual_Q8_window_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (windowState m ell F z hz g)=
      windowForcing m ell F z hz g+z • windowState m ell F z hz g := by
  let C : End := compressionCore F
  let R : End := resolventCore F z hz
  let T : End := thetaAction m ell
  let S : End := inverseAction
  have hR := (core_inverses F z hz).1
  have hm : (C-z • (1:End))*T*bracket S R=
      bracket C T*bracket S R+T*bracket C S*R := by
    unfold bracket
    linear_combination (norm := noncomm_ring) T*S*hR-T*hR*S
  have h := LinearMap.congr_fun hm (inputCore g)
  change (compressionCore F-z • (1:End)) (windowState m ell F z hz g)=
    bracket (compressionCore F) (thetaAction m ell) (radialMap F z hz (inputCore g))+
      thetaAction m ell (bracket (compressionCore F) inverseAction (resolventCore F z hz (inputCore g))) at h
  rw [←window_forcing_return] at h
  simpa only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,sub_eq_iff_eq_add] using h

/-- One signed word retains scalar, matter, and the complete coherent compression contribution before clipping. -/
def wholePrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  -(1/2:ℝ)*(sourcePair (windowState m ell F z hz g) (squareCurrent F (windowState m ell F z hz g))).im-
    (sourcePair (Q8 false (windowState m ell F z hz g)) (windowForcing m ell F z hz g)).im

theorem actual_Q8_whole_ward (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    wholePrice m ell F z hz g=z.im*closureGram false (windowState m ell F z hz g) := by
  let u := windowState m ell F z hz g
  have hp := compression_pair F u (Q8 false u)
  have hc := pair_conjugate (Q8 false u) (compressionCore F u)
  have hq := q8_pair u (compressionCore F u)
  have hr : (sourcePair u (squareCurrent F u)).im= -2*(sourcePair (Q8 false u) (compressionCore F u)).im := by
    rw [square_compression]
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right] at *
    rw [hp,hq]
    have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.sub_im]
    linarith only [hi]
  have hs := congrArg (fun f => (sourcePair (Q8 false u) f).im) (actual_Q8_window_source m ell F z hz g)
  change (sourcePair (Q8 false u) (compressionCore F u)).im=
    (sourcePair (Q8 false u) (windowForcing m ell F z hz g+z • u)).im at hs
  simp only [sourcePair,map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_im,Complex.mul_im] at hs
  have h0 : (sourcePair (Q8 false u) u).im=0 := by rw [←q8_pair];exact q8_diag_real u
  have h1 : (sourcePair (Q8 false u) u).re=closureGram false u := by rw [←q8_pair,original_Q8_gram]
  change (sourcePair (Q8 false u) (compressionCore F u)).im=
    (sourcePair (Q8 false u) (windowForcing m ell F z hz g)).im+
      (z.re*(sourcePair (Q8 false u) u).im+z.im*(sourcePair (Q8 false u) u).re) at hs
  rw [h0,h1] at hs
  change -(1/2:ℝ)*(sourcePair u (squareCurrent F u)).im-
    (sourcePair (Q8 false u) (windowForcing m ell F z hz g)).im=_
  rw [hr]
  linarith only [hs]

private theorem closure_norm_sum (u : QuantumTest) : closureGram false u=
    ∑ sharp : Bool,∑ mu : Fin 8,‖embed (spinClosureCoefficient sharp mu u)‖^2 := by
  rw [←original_Q8_gram,q8_pair_sum]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro sharp _
  apply Finset.sum_congr rfl
  intro mu _
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (embed (spinClosureCoefficient sharp mu u))
private theorem two_square (x y : H) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem coherent_square (sharp : Bool) (u : QuantumTest) (e : Column) :
    columnNorm (coherentColumn sharp u e) ≤ 2*closureGram false u+2*columnNorm e := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun mu (_ : mu ∈ Finset.univ) =>
    two_square (embed (spinClosureCoefficient sharp mu u)) (embed (e mu)))
  change (∑ mu : Fin 8,‖embed (spinClosureCoefficient sharp mu u)-embed (e mu)‖^2)≤_ at h
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at h
  have hk : (∑ mu : Fin 8,‖embed (spinClosureCoefficient sharp mu u)‖^2)≤closureGram false u := by
    rw [closure_norm_sum]
    exact Finset.single_le_sum
      (f := fun s : Bool => ∑ mu : Fin 8,‖embed (spinClosureCoefficient s mu u)‖^2)
      (fun s _ => Finset.sum_nonneg (fun mu _ => sq_nonneg ‖embed (spinClosureCoefficient s mu u)‖))
      (Finset.mem_univ sharp)
  change (∑ mu : Fin 8,‖embed (spinClosureCoefficient sharp mu u-e mu)‖^2)≤_
  simp only [map_sub]
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hk (by norm_num)) le_rfl)

/-- The original coherent branch consumes the Q8 source Ward; its only separate error is the already-paid fixed-source L2 column. -/
theorem actual_Q8_joint_mu_price (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (w : ℝ) :
    μ*columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) ≤
      2*wholePrice m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g+
        (2*μ)*columnNorm (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g) := by
  rw [actual_Q8_whole_ward]
  simp only [line_im]
  have h := mul_le_mul_of_nonneg_left (coherent_square sharp
    (windowState m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)
    (errorColumn sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) hμ.le
  change μ*columnNorm (jointState sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)≤_ at h
  convert h using 1
  ring

end LowEnergy.SourceClockYukawaQ8WholeCurrent
