import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeNeutralSpinCurrent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseSpinCompressionBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular SourceEscapeCurrent
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseProjectionCurrentRemainder SourceInverseGaugeSingleDefectJoin
open SourceInverseCompressionGaugeBudget SourceInverseHamiltonianForceReduction
open SourceHamiltonianScaleJet SourceInverseCoframeNeutralBudget
open SourceInverseCoframeCompressionBudget SourceInverseNeutralScalarCurrent SourceInverseNeutralSpinCurrent
open GaussNativeForm GaussCoframeForm GaussQuantumMultiplier SourceNativeCutoffContact
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarGaugeScale MeasureTheory Filter SourceResolventBandLimit
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction sourceRead state defectAction compressionCore
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent singleDefect projectionCurrent doubleProjectionFlux deltaGauge
  matterInsertion matterHamiltonianCurrent readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  wholeCurrent wholeResponse firstRetardedCurrent

private theorem paired_add {A B C D : End} (hA : Paired A B) (hC : Paired C D) :
    Paired (A+C) (B+D) := by
  intro f g
  simp only [LinearMap.add_apply, sourcePair, map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (hA f g) (hC f g)

private theorem paired_real {A B : End} (r : ℝ) (h : Paired A B) :
    Paired ((r : ℂ) • A) ((r : ℂ) • B) := by
  intro f g
  simp only [LinearMap.smul_apply, sourcePair, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((r : ℂ) * ·) (h f g)

private theorem paired_comp {A B C D : End} (hA : Paired A B) (hC : Paired C D) :
    Paired (A.comp C) (D.comp B) := fun f g => (hA f (C g)).trans (hC (B f) g)

private theorem paired_sum {ι : Type*} [Fintype ι] {A B : ι → End}
    (h : ∀ i, Paired (A i) (B i)) : Paired (∑ i, A i) (∑ i, B i) := by
  intro f g
  simp only [LinearMap.sum_apply, sourcePair, map_sum, inner_sum, sum_inner]
  exact Finset.sum_congr rfl (fun i _ => h i f g)

private theorem paired_symmetrize {A B : End} (hA : Paired A B) (hB : Paired B A) :
    Paired ((1/2 : ℂ) • (A+B)) ((1/2 : ℂ) • (A+B)) := by
  have h : Paired (A+B) (B+A) := paired_add hA hB
  rw [add_comm B A] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using paired_real (1/2) h

private theorem paired_sandwich {A M : End} (hA : Paired A A) (hM : Paired M M) :
    Paired (A.comp (M.comp A)) (A.comp (M.comp A)) := by
  have hMA : Paired (M.comp A) (A.comp M) := paired_comp hM hA
  have h : Paired (A.comp (M.comp A)) ((A.comp M).comp A) := paired_comp hA hMA
  simpa only [LinearMap.comp_assoc] using h

/-- Formal pairing of the actual seven spin squares and original number shift. -/
theorem original_spin_potential_pair : Paired spinPotential spinPotential := by
  have hS (a : Fin 7) : Paired (spinSquare a) (spinSquare a) :=
    paired_real (spinWeight a) (paired_sandwich (GaussCoframeSpin.current_pair a)
      (GaussNativeForm.multiply_pair inverseVolume inverseVolume_smooth))
  have hN : Paired numberShift numberShift :=
    paired_symmetrize
      (paired_comp number_pair (GaussNativeForm.multiply_pair numberCoefficient numberCoefficient_smooth))
      (paired_comp (GaussNativeForm.multiply_pair numberCoefficient numberCoefficient_smooth) number_pair)
  exact paired_add (paired_sum hS) hN

private theorem full_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.fullAction sharp g)=
      sourcePair (SourceMixedNativeReturn.fullAction (!sharp) f) g := by
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair g f)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair f g

private theorem spin_current_pair (sharp : Bool) (f g : QuantumTest) :
    sourcePair f (spinCurrent sharp g)= -sourcePair (spinCurrent (!sharp) f) g := by
  unfold spinCurrent
  have hr (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
    simp only [sourcePair,map_sub,inner_sub_right]
  have hl (a b c : QuantumTest) : sourcePair (a-b) c=sourcePair a c-sourcePair b c := by
    simp only [sourcePair,map_sub,inner_sub_left]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply]
  rw [hr,hl,original_spin_potential_pair,full_pair,full_pair,original_spin_potential_pair]
  ring

private theorem real_spin (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (spinCurrent sharp) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change multiply c hc (spinCurrent sharp f) z=spinCurrent sharp (multiply c hc f) z
  rw [multiply_apply,original_spin_current_apply,original_spin_current_apply,multiply_apply]
  exact (map_smul _ _ _).symm

private theorem theta_spin (sharp : Bool) (m ell : ℕ) :
    Commute (SourceMixedNativeReturn.thetaAction m ell) (spinCurrent sharp) := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact real_spin _ _ sharp

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (SourceMixedNativeReturn.thetaAction m ell g)=
      sourcePair (SourceMixedNativeReturn.thetaAction m ell f) g := by
  rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
  exact multiply_pair _ _ _ _

/-- The original zero-order spin current multiplied by its actual cutoff window. -/
def spinInsertion (sharp : Bool) (m ell : ℕ) : End :=
  spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell

attribute [local irreducible] spinPotential spinCurrent spinInsertion

/-- The full insertion's formal adjoint is the opposite actual branch with its commutator sign. -/
theorem original_spin_insertion_pair (sharp : Bool) (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (spinInsertion sharp m ell g)= -sourcePair (spinInsertion (!sharp) m ell f) g := by
  unfold spinInsertion
  change sourcePair f (spinCurrent sharp (SourceMixedNativeReturn.thetaAction m ell g))=_
  rw [spin_current_pair,theta_pair]
  exact congrArg (fun q => -sourcePair q g)
    (LinearMap.congr_fun (theta_spin (!sharp) m ell).eq f)

/-- Each fixed original test pays its spin insertion through the real theta tail. -/
theorem original_spin_insertion_fixed_tail (sharp : Bool) (f : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ‖embed (spinInsertion sharp m ell f)‖<ε := by
  have he (m ell : ℕ) : embed (spinInsertion sharp m ell f)=
      SourceRelativePowerTail.relativeTail m ell (embed (spinCurrent sharp f)) := by
    unfold spinInsertion
    have ht := (LinearMap.congr_fun (theta_spin sharp m ell).eq f).symm
    change embed ((spinCurrent sharp*SourceMixedNativeReturn.thetaAction m ell) f)=_
    rw [ht]
    change embed (SourceMixedNativeReturn.thetaAction m ell (spinCurrent sharp f))=_
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial,
      SourceNativeCutoffContact.theta_core]
  simpa only [he] using! SourceHardyRetardedTail.original_relative_tail (embed (spinCurrent sharp f))

attribute [local irreducible] sourcePair

private theorem compression_core_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem read_compression (F : Index) (seed : diagonal.domain) (A : End) (x : H) :
    sourceRead F seed A (GaussGradedCompression.compression F x)=
      embed (A (coreEquiv.symm ⟨GaussGradedCompression.compression F x,compression_mem_core F x⟩)) := by
  have hm : GaussGradedCompression.compression F x∈inputSpan F seed :=
    Submodule.mem_sup_left (compression_mem_support F x)
  have hp := (inputSpan F seed).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨GaussGradedCompression.compression F x,hm⟩
  unfold sourceRead coreRead
  change embed (A (coreEquiv.symm (Submodule.inclusion (input_span_core F seed)
    ((inputSpan F seed).orthogonalProjectionOnto (GaussGradedCompression.compression F x)))))=_
  rw [hp]
  rfl

/-- Compression enters its actual finite core first; the auxiliary reader seed has no effect. -/
theorem original_spin_after_compression_seed (F : Index) (seed : diagonal.domain) (A : End) :
    sourceRead F seed A*GaussGradedCompression.compression F=
      sourceRead F (0 : diagonal.domain) A*GaussGradedCompression.compression F := by
  apply ContinuousLinearMap.ext
  intro x
  exact (read_compression F seed A x).trans (read_compression F 0 A x).symm

/-- The source spin map S C_F is bounded because C_F has its generated finite core range. -/
def spinAfterCompression (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  sourceRead F (0 : diagonal.domain) (spinInsertion sharp m ell)*GaussGradedCompression.compression F

/-- The real adjoint completion retains the escaped input leg of C_F S. -/
def wholeSpinCurrent (sharp : Bool) (m ell : ℕ) (F : Index) : Op :=
  -star (spinAfterCompression (!sharp) m ell F)-spinAfterCompression sharp m ell F

def wholeSpinResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) : Op :=
  finiteResolvent F z*wholeSpinCurrent sharp m ell F*finiteResolvent F z

attribute [local irreducible] spinAfterCompression wholeSpinCurrent wholeSpinResponse

private theorem after_compression_core (sharp : Bool) (m ell : ℕ) (F : Index) (f : QuantumTest) :
    spinAfterCompression sharp m ell F (embed f)=embed (spinInsertion sharp m ell (compressionCore F f)) := by
  rw [spinAfterCompression]
  unfold compressionCore
  exact read_compression F 0 (spinInsertion sharp m ell) (embed f)

private theorem compression_pair (F : Index) (p q : QuantumTest) :
    sourcePair p (compressionCore F q)=sourcePair (compressionCore F p) q := by
  simp only [sourcePair,compression_core_embed]
  exact (GaussGradedCompression.compression_pair F (embed p) (embed q)).symm

/-- The whole-H operator agrees with the original graded commutator on both arbitrary core legs. -/
theorem original_whole_spin_current_pair (sharp : Bool) (m ell : ℕ) (F : Index) (p q : QuantumTest) :
    inner ℂ (embed p) (wholeSpinCurrent sharp m ell F (embed q))=
      sourcePair p (bracket (compressionCore F) (spinInsertion sharp m ell) q) := by
  rw [wholeSpinCurrent]
  simp only [sub_apply,neg_apply,inner_sub_right,inner_neg_right,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,after_compression_core]
  have hW := original_spin_insertion_pair sharp m ell (compressionCore F p) q
  have hC := compression_pair F p (spinInsertion sharp m ell q)
  have h := hC.trans hW
  simp only [sourcePair] at h
  simp only [sourcePair,bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub,inner_sub_right]
  linear_combination -h

private theorem finite_pair (F : Index) (z : ℂ) (hz : z.im ≠ 0) (k f : H) :
    inner ℂ k (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k) f := by
  have hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have hk := congrArg (fun A : Op => A k)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) (star z) hs)
  have hf := congrArg (fun A : Op => A f)
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
    star z • finiteResolvent F (star z) k=k at hk
  change GaussGradedCompression.compression F (finiteResolvent F z f)-z • finiteResolvent F z f=f at hf
  have hp : inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k))
      (finiteResolvent F z f)=inner ℂ (finiteResolvent F (star z) k)
        (GaussGradedCompression.compression F (finiteResolvent F z f)) :=
    (GaussGradedCompression.compression_selfAdjoint F).isSymmetric _ _
  calc
    _=inner ℂ (GaussGradedCompression.compression F (finiteResolvent F (star z) k)-
      star z • finiteResolvent F (star z) k) (finiteResolvent F z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _=inner ℂ (finiteResolvent F (star z) k)
      (GaussGradedCompression.compression F (finiteResolvent F z f)-z • finiteResolvent F z f) := by
      simp only [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right]
      exact congrArg₂ (fun a b : ℂ => a-b) hp
        (congrArg (fun c : ℂ => c*inner ℂ (finiteResolvent F (star z) k) (finiteResolvent F z f))
          (show (starRingEnd ℂ) (star z)=z from star_star z))
    _=_ := congrArg (fun x => inner ℂ _ x) hf

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_equation (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    compressionCore F (state F z hz g)=coreEquiv.symm g+z • state F z hz g := by
  apply embed_injective
  rw [compression_core_embed,state_embed,map_add,map_smul,state_embed]
  have hc : embed (coreEquiv.symm g)=(g : H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  rw [hc]
  have he := congrArg (fun A : Op => A (g : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (finiteResolvent F z (g : H))-
    z • finiteResolvent F z (g : H)=(g : H) at he
  exact eq_add_of_sub_eq he

private theorem core_endpoints (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain)
    (A AD : End) (hPair : ∀ f q,sourcePair f (A q)= -sourcePair (AD f) q) :
    sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
      (bracket (compressionCore F) A (state F z hz g))=
      -sourcePair (AD (coreEquiv.symm k)) (state F z hz g)-
      sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (A (coreEquiv.symm g)) := by
  have hr (a b c : QuantumTest) : sourcePair a (b-c)=sourcePair a b-sourcePair a c := by
    simp only [sourcePair,map_sub,inner_sub_right]
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,hr]
  rw [compression_pair,compression_equation,compression_equation]
  have ha (a b c : QuantumTest) : sourcePair (a+b) c=sourcePair a c+sourcePair b c := by
    simp only [sourcePair,map_add,inner_add_left]
  have hl (c : ℂ) (a b : QuantumTest) : sourcePair (c • a) b=star c*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
  have hb (a b c : QuantumTest) : sourcePair a (b+c)=sourcePair a b+sourcePair a c := by
    simp only [sourcePair,map_add,inner_add_right]
  have hp (c : ℂ) (a b : QuantumTest) : sourcePair a (c • b)=c*sourcePair a b := by
    simp only [sourcePair,map_smul,inner_smul_right]
  simp only [ha,hl,map_add,map_smul,hb,hp,star_star]
  rw [hPair]
  ring

/-- The genuine whole-H commutator returns both fixed source endpoints, including its adjoint escape leg. -/
theorem actual_whole_spin_endpoints (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    inner ℂ (k : H) (wholeSpinResponse sharp m ell F z (g : H))=
      -sourcePair (spinInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g)-
      sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (spinInsertion sharp m ell (coreEquiv.symm g)) := by
  let hs : (star z).im≠0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  let p := state F (star z) hs k
  let q := state F z hz g
  have hp : embed p=finiteResolvent F (star z) (k : H) := state_embed F (star z) hs k
  have hq : embed q=finiteResolvent F z (g : H) := state_embed F z hz g
  have he := congrArg₂ (fun x y : H => inner ℂ x (wholeSpinCurrent sharp m ell F y)) hp hq
  have hc := core_endpoints F z hz g k (spinInsertion sharp m ell) (spinInsertion (!sharp) m ell)
    (original_spin_insertion_pair sharp m ell)
  have hw := original_whole_spin_current_pair sharp m ell F p q
  unfold wholeSpinResponse
  change inner ℂ (k : H) (finiteResolvent F z
    (wholeSpinCurrent sharp m ell F (finiteResolvent F z (g : H))))=_
  exact (finite_pair F z hz (k : H) _).trans (he.symm.trans (hw.trans hc))

open SourceInverseSourceLeg SourceActualResolventEnergy
open scoped ENNReal

def spinResponse (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (_hz : z.im≠0)
    (g k : diagonal.domain) : ℂ := inner ℂ (k : H) (wholeSpinResponse sharp m ell F z (g : H))

attribute [local irreducible] spinResponse

private theorem spin_endpoints (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    spinResponse sharp m ell F z hz g k=
      -sourcePair (spinInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g)-
      sourcePair (state F (star z) (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
        (spinInsertion sharp m ell (coreEquiv.symm g)) := by
  unfold spinResponse
  exact actual_whole_spin_endpoints sharp m ell F z hz g k

private theorem pair_bound (p q : QuantumTest) : ‖sourcePair p q‖ ≤ ‖embed p‖*‖embed q‖ := by
  unfold sourcePair
  exact norm_inner_le_norm _ _

private theorem minus_square (a b : ℂ) : ‖-a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (-a) b) 2
  rw [norm_neg] at h
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

private theorem current_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g k : diagonal.domain) :
    ‖spinResponse sharp m ell F z hz g k‖^2 ≤
      2*‖embed (spinInsertion (!sharp) m ell (coreEquiv.symm k))‖^2*‖finiteResolvent F z (g : H)‖^2+
      2*‖embed (spinInsertion sharp m ell (coreEquiv.symm g))‖^2*‖finiteResolvent F z (k : H)‖^2 := by
  let hs : (star z).im ≠ 0 := by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
  have ha := pow_le_pow_left₀ (norm_nonneg _)
    (pair_bound (spinInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g)) 2
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (pair_bound (state F (star z) hs k) (spinInsertion sharp m ell (coreEquiv.symm g))) 2
  simp only [mul_pow,state_embed,actual_conjugate_leg_norm F z hz] at ha hb
  rw [spin_endpoints]
  have ht := minus_square
    (sourcePair (spinInsertion (!sharp) m ell (coreEquiv.symm k)) (state F z hz g))
    (sourcePair (state F (star z) hs k) (spinInsertion sharp m ell (coreEquiv.symm g)))
  nlinarith only [ht,ha,hb]

/-- The whole spin compression current is integrated at its actual two fixed endpoints. -/
theorem actual_whole_spin_energy (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖spinResponse sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤
      ENNReal.ofReal ((2*Real.pi/μ)*
        (‖embed (spinInsertion (!sharp) m ell (coreEquiv.symm k))‖^2*‖(g : H)‖^2+
          ‖embed (spinInsertion sharp m ell (coreEquiv.symm g))‖^2*‖(k : H)‖^2)) := by
  let L := 2*‖embed (spinInsertion (!sharp) m ell (coreEquiv.symm k))‖^2
  let G := 2*‖embed (spinInsertion sharp m ell (coreEquiv.symm g))‖^2
  have hL : 0 ≤ L := by dsimp [L];positivity
  have hG : 0 ≤ G := by dsimp [G];positivity
  have he (u : H) : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) u‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖u‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ u
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal L*
      ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2)) := by
    exact measurable_const.mul
      ((((SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal L*ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2)+
        ENNReal.ofReal G*ENNReal.ofReal (‖finiteResolvent F (line μ w) (k : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hL,←ENNReal.ofReal_mul hG,
        ←ENNReal.ofReal_add (mul_nonneg hL (sq_nonneg _)) (mul_nonneg hG (sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (current_bound sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k)
    _=ENNReal.ofReal L*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))+
        ENNReal.ofReal G*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (k : H)‖^2)) := by
      rw [lintegral_add_left hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _=_ := by
      have hx := congrArg₂ (fun a b : ℝ≥0∞ => ENNReal.ofReal L*a+ENNReal.ofReal G*b)
        (he (g : H)) (he (k : H))
      have hy := congrArg₂ (fun a b : ℝ≥0∞ => a+b)
        (ENNReal.ofReal_mul (p := L) (q := (Real.pi/μ)*‖(g : H)‖^2) hL).symm
        (ENNReal.ofReal_mul (p := G) (q := (Real.pi/μ)*‖(k : H)‖^2) hG).symm
      have hn : 0 ≤ L*((Real.pi/μ)*‖(g : H)‖^2) := by positivity
      have ho : 0 ≤ G*((Real.pi/μ)*‖(k : H)‖^2) := by positivity
      apply (hx.trans (hy.trans (ENNReal.ofReal_add hn ho).symm)).trans
      apply congrArg ENNReal.ofReal
      dsimp [L,G]
      ring

/-- One source-fixed threshold pays the whole spin compression response for every F and upper cutoff. -/
theorem actual_whole_spin_tail (sharp : Bool) (μ : ℝ) (hμ : 0 < μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖spinResponse sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (2*Real.pi/μ)*(1+‖(g : H)‖^2+‖(k : H)‖^2)
  have hC : 0 < C := by dsimp [C];positivity
  let δ := Real.sqrt (ε/C)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hε hC)
  have hδ2 : δ^2=ε/C := Real.sq_sqrt (div_pos hε hC).le
  obtain ⟨Ng,hg⟩ := original_spin_insertion_fixed_tail sharp (coreEquiv.symm g) δ hδ
  obtain ⟨Nk,hk⟩ := original_spin_insertion_fixed_tail (!sharp) (coreEquiv.symm k) δ hδ
  refine ⟨max Ng Nk,fun m hm ell hell F => (actual_whole_spin_energy sharp m ell F μ hμ g k).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hgs := pow_le_pow_left₀ (norm_nonneg _) (hg m ((le_max_left _ _).trans hm) ell hell).le 2
  have hks := pow_le_pow_left₀ (norm_nonneg _) (hk m ((le_max_right _ _).trans hm) ell hell).le 2
  calc
    _ ≤ (2*Real.pi/μ)*(δ^2*‖(g : H)‖^2+δ^2*‖(k : H)‖^2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right hks (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hgs (sq_nonneg _))) (by positivity)
    _ ≤ C*δ^2 := by dsimp [C];nlinarith [sq_nonneg δ,show 0 < 2*Real.pi/μ by positivity]
    _=ε := by rw [hδ2];exact mul_div_cancel₀ ε hC.ne'

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem map_sandwich {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a : R) : e r*(e a*e r)=e (r*a*r) := by
  simp only [map_mul,mul_assoc]

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (s : ℝ) :
    sandwichJet F g z A 0 0 s 0=(mixedHilbert s 0).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 s 0*(readOrbitJet F g A 0 0 s 0*resolventJet F z 0 0 s 0)=_
  exact (congrArg₂ (fun r a : Op => r*(a*r))
    (actual_mixed_resolvent F z hz s 0) (actual_read_orbit F g A s 0)).trans
      (map_sandwich _ _ _)

private theorem inverse_flow_core (s : ℝ) (f : QuantumTest) :
    (mixedHilbert s 0).symm (embed f)=embed (coframeFlow (-s) f) := by
  apply (mixedHilbert s 0).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,
    SourceGaugeScaleTransport.hilbertFlow_zero,SourceCoframeScaleTransport.hilbertFlow_on_core,
    coframeFlow]
  rw [SourceCoframeScaleTransport.coreFlow_add]
  have he : (3/2 : ℝ)*s+(3/2 : ℝ)*(-s)=0 := by ring
  rw [he,SourceCoframeScaleTransport.coreFlow_zero]

private theorem orbit_pair (B : Op) (s : ℝ) (g k : QuantumTest) :
    inner ℂ (embed k) ((mixedHilbert s 0).conjStarAlgEquiv B (embed g))=
      inner ℂ (embed (coframeFlow (-s) k)) (B (embed (coframeFlow (-s) g))) := by
  have h := (mixedHilbert s 0).inner_map_map ((mixedHilbert s 0).symm (embed k))
    (B ((mixedHilbert s 0).symm (embed g)))
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℂ (embed k) ((mixedHilbert s 0).conjStarAlgEquiv B (embed g))=_ at h
  simpa only [inverse_flow_core] using h

private theorem negative_flow (f : QuantumTest) (s : ℝ) :
    HasDerivAt (fun r : ℝ => embed (coframeFlow (-r) f))
      (-embed (coframeFlow (-s) (K f))) s := by
  have h := test_coframe_derivative 0 0 f (-s) 0
  have he : (fun r => testJet 0 0 f r 0)=(fun r => embed (coframeFlow r f)) := by
    funext r
    simp only [testJet,sourceTest,pow_zero,Module.End.one_apply,
      SourceGaugeScaleTransport.hilbertFlow_zero]
  rw [he] at h
  have hd : testJet (0+1) 0 f (-s) 0=embed (coframeFlow (-s) (K f)) := by
    simp only [testJet,sourceTest,pow_zero,pow_one,Module.End.one_apply,Nat.zero_add,
      SourceGaugeScaleTransport.hilbertFlow_zero]
  rw [hd] at h
  simpa only [neg_smul,one_smul] using! h.scomp s ((hasDerivAt_id s).neg)

private theorem pullback_derivative (B : Op) (g k : QuantumTest) (s : ℝ) :
    HasDerivAt (fun r : ℝ => inner ℂ (embed (coframeFlow (-r) k))
      (B (embed (coframeFlow (-r) g))))
      (-inner ℂ (embed (coframeFlow (-s) k)) (B (embed (coframeFlow (-s) (K g))))-
      inner ℂ (embed (coframeFlow (-s) (K k))) (B (embed (coframeFlow (-s) g)))) s := by
  have hg := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (negative_flow g s)
  have h := (negative_flow k s).inner ℂ hg
  simp only [map_neg,inner_neg_left,inner_neg_right] at h
  exact h.congr_deriv (by abel)

private def weakJet (J : ℕ → ℝ → Op) (g k : QuantumTest) (n : ℕ) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (J n t (embed g))

set_option backward.isDefEq.respectTransparency.types false in
private theorem weak_derivative (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t) (g k : QuantumTest) (n : ℕ) (t : ℝ) :
    HasDerivAt (weakJet J g k n) (weakJet J g k (n+1) t) t := by
  have hA : HasDerivAt (fun s => J n s (embed g)) (J (n+1) t (embed g)) t :=
    ((ContinuousLinearMap.apply ℂ H (embed g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hJ n t)
  have h := (hasDerivAt_const t (embed k)).inner ℂ hA
  simpa only [inner_zero_left,zero_add,add_zero,weakJet] using! h

private theorem weak_first (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0))
    (g k : QuantumTest) (t : ℝ) :
    weakJet J g k 1 t= -weakJet J (K g) k 0 t-weakJet J g (K k) 0 t := by
  have ho (f h : QuantumTest) (s : ℝ) : weakJet J f h 0 s=
      inner ℂ (embed (coframeFlow (-s) h))
        (J 0 0 (embed (coframeFlow (-s) f))) := by
    rw [weakJet,hO]
    exact orbit_pair _ s f h
  have h := (pullback_derivative (J 0 0) g k t).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (ho g k))
  have hu := (weak_derivative J hJ g k 0 t).unique h
  rw [ho (K g) k,ho g (K k)]
  exact hu

private theorem weak_next (J : ℕ → ℝ → Op)
    (hJ : ∀ n t,HasDerivAt (J n) (J (n+1) t) t)
    (hO : ∀ t,J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0))
    (n : ℕ) (g k : QuantumTest) (t : ℝ) :
    weakJet J g k (n+1) t= -weakJet J (K g) k n t-weakJet J g (K k) n t := by
  induction n generalizing g k t with
  | zero => exact weak_first J hJ hO g k t
  | succ n ih =>
    have hd := (weak_derivative J hJ (K g) k n t).neg.sub (weak_derivative J hJ g (K k) n t)
    exact (weak_derivative J hJ g k (n+1) t).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (ih g k)))

private theorem profile_next (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End)
    (f k : QuantumTest) (n : ℕ) (t : ℝ) :
    coframeProfile F seed z A f k (n+1) t=
      -coframeProfile F seed z A (K f) k n t-coframeProfile F seed z A f (K k) n t := by
  let J := fun n t => sandwichJet F seed z A n 0 t 0
  have hO (t : ℝ) : J 0 t=(mixedHilbert t 0).conjStarAlgEquiv (J 0 0) := by
    have ho := (sandwich_orbit F seed z hz A 0).trans (origin_conjugate _)
    exact (sandwich_orbit F seed z hz A t).trans (congrArg (mixedHilbert t 0).conjStarAlgEquiv ho.symm)
  exact weak_next J (fun n t => sandwich_coframe_derivative F seed z A n 0 t 0) hO n f k t

private theorem profile_origin (F : Index) (seed : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A : End) (f k : QuantumTest) :
    coframeProfile F seed z A f k 0 0=
      inner ℂ (embed k) ((finiteResolvent F z*sourceRead F seed A*finiteResolvent F z) (embed f)) :=
  congrArg (fun B : Op => inner ℂ (embed k) (B (embed f)))
    ((sandwich_orbit F seed z hz A 0).trans (origin_conjugate _))

private theorem profile_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => coframeProfile F seed (line μ w) A f k n 0) := by
  induction n generalizing f k with
  | zero =>
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    have hc : Continuous (fun w : ℝ => inner ℂ (embed k)
        (finiteResolvent F (line μ w) (sourceRead F seed A (finiteResolvent F (line μ w) (embed f))))) :=
      continuous_const.inner (hr.clm_apply ((sourceRead F seed A).continuous.comp (hr.clm_apply continuous_const)))
    exact hc.congr (fun w => (profile_origin F seed (line μ w)
      (by simpa only [line_im] using hμ.ne') A f k).symm)
  | succ n ih =>
    exact ((ih (K f) k).neg.sub (ih f (K k))).congr (fun w =>
      (profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne') A f k n 0).symm)

private def Tail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))≤ENNReal.ofReal ε

private theorem tail_neg (f : ℕ → ℕ → Index → ℝ → ℂ) (hf : Tail f) :
    Tail (fun m ell F w => -f m ell F w) := by simpa only [Tail,norm_neg] using hf

private theorem tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : Tail f) (hg : Tail g) :
    Tail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell] with F hl hr
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem tail_congr (f h : ℕ → ℕ → Index → ℝ → ℂ)
    (he : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),∀ w,f m ell F w=h m ell F w)
    (hh : Tail h) : Tail f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,he m ell] with F hF hEq
  simpa only [hEq] using hF

private theorem read_same_support (F : Index) (seed seed' : diagonal.domain) (A : End) (x : H)
    (hx : x∈supportSpan F) : sourceRead F seed A x=sourceRead F seed' A x := by
  have hp := (inputSpan F seed).orthogonalProjectionOnto_mem_subspace_eq_self ⟨x,Submodule.mem_sup_left hx⟩
  have hp' := (inputSpan F seed').orthogonalProjectionOnto_mem_subspace_eq_self ⟨x,Submodule.mem_sup_left hx⟩
  let a := Submodule.inclusion (input_span_core F seed) ((inputSpan F seed).orthogonalProjectionOnto x)
  let b := Submodule.inclusion (input_span_core F seed') ((inputSpan F seed').orthogonalProjectionOnto x)
  have ha : (a : H)=x := congrArg Subtype.val hp
  have hb : (b : H)=x := congrArg Subtype.val hp'
  have he : a=b := Subtype.ext (ha.trans hb.symm)
  unfold sourceRead coreRead
  exact congrArg (fun q : diagonal.domain => embed (A (coreEquiv.symm q))) he

private theorem source_seed_independent (seed : diagonal.domain) (f k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (z : ℂ),z.im≠0 → ∀ A : End,
      coframeProfile F seed z A f k 0 0=coframeProfile F (coreEquiv f) z A f k 0 0 := by
  filter_upwards [source_eventually_mem_support (coreEquiv f)] with F hF
  intro z hz A
  have hx : finiteResolvent F z (embed f)∈supportSpan F := resolvent_mem_support F z hz _ hF
  have he := congrArg (fun v : H => inner ℂ (embed k) (finiteResolvent F z v))
    (read_same_support F seed (coreEquiv f) A (finiteResolvent F z (embed f)) hx)
  exact (profile_origin F seed z hz A f k).trans
    (he.trans (profile_origin F (coreEquiv f) z hz A f k).symm)

/-- The actual spin compression commutator used by the source Pc remainder. -/
def compressionSpin (sharp : Bool) (m ell : ℕ) (F : Index) : End :=
  bracket (compressionCore F) (spinInsertion sharp m ell)

attribute [local irreducible] compressionSpin

private theorem whole_current_core (sharp : Bool) (m ell : ℕ) (F : Index) (q : QuantumTest) :
    wholeSpinCurrent sharp m ell F (embed q)=embed (compressionSpin sharp m ell F q) := by
  have h : ∀ p : QuantumTest,inner ℂ (embed p) (wholeSpinCurrent sharp m ell F (embed q))=
      inner ℂ (embed p) (embed (compressionSpin sharp m ell F q)) := by
    intro p
    simpa only [compressionSpin,sourcePair] using! original_whole_spin_current_pair sharp m ell F p q
  apply ext_inner_left ℂ
  intro x
  exact SourceCoframeScaleTransport.embed_dense.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) h

private theorem actual_spin_read (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (f k : QuantumTest) :
    coframeProfile F (coreEquiv f) z (compressionSpin sharp m ell F) f k 0 0=
      spinResponse sharp m ell F z hz (coreEquiv f) (coreEquiv k) := by
  let q := coreEquiv.symm (sourceCore F z hz (coreEquiv f))
  have hq : embed q=finiteResolvent F z (embed f) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hs := source_read_resolvent F (coreEquiv f) (compressionSpin sharp m ell F) z hz
  have hw := whole_current_core sharp m ell F q
  rw [hq] at hw
  have he : sourceRead F (coreEquiv f) (compressionSpin sharp m ell F) (finiteResolvent F z (embed f))=
      wholeSpinCurrent sharp m ell F (finiteResolvent F z (embed f)) := hs.trans hw.symm
  have hp := congrArg (fun v : H => inner ℂ (embed k) (finiteResolvent F z v)) he
  unfold spinResponse wholeSpinResponse
  exact (profile_origin F (coreEquiv f) z hz _ f k).trans hp

private theorem spin_base_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) : Tail (fun m ell F w => coframeProfile F seed (line μ w)
      (compressionSpin sharp m ell F) f k 0 0) := by
  apply tail_congr _ (fun m ell F w => spinResponse sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') (coreEquiv f) (coreEquiv k))
  · intro m ell
    filter_upwards [source_seed_independent seed f k] with F hF
    intro w
    exact (hF (line μ w) (by simpa only [line_im] using hμ.ne') _).trans
      (actual_spin_read sharp m ell F _ (by simpa only [line_im] using hμ.ne') f k)
  · intro ε hε
    obtain ⟨N,hN⟩ := actual_whole_spin_tail sharp μ hμ (coreEquiv f) (coreEquiv k) ε hε
    exact ⟨N,fun m hm ell hell => Filter.Eventually.of_forall (hN m hm ell hell)⟩

private theorem all_coframe_tails (A : ℕ → ℕ → Index → End) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (hbase : ∀ f k : QuantumTest,Tail (fun m ell F w => coframeProfile F seed (line μ w) (A m ell F) f k 0 0))
    (n : ℕ) (f k : QuantumTest) :
    Tail (fun m ell F w => coframeProfile F seed (line μ w) (A m ell F) f k n 0) := by
  induction n generalizing f k with
  | zero => exact hbase f k
  | succ n ih =>
    have htail := tail_add _ _
      (fun m ell F => (profile_continuous F seed (A m ell F) μ hμ n (K f) k).neg)
      (tail_neg _ (ih (K f) k)) (tail_neg _ (ih f (K k)))
    apply tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => ?_)) htail
    rw [profile_next F seed (line μ w) (by simpa only [line_im] using hμ.ne')]
    simp only [Pi.neg_apply,sub_eq_add_neg]

/-- Fixed finite coframe jets consume the actual spin endpoints and the original source cofinal event. -/
theorem actual_spin_compression_coframe_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (n : ℕ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeProfile F seed (line μ w)
          (compressionSpin sharp m ell F) f k n 0‖^2))≤ENNReal.ofReal ε :=
  all_coframe_tails (compressionSpin sharp) seed μ hμ (spin_base_tail sharp seed μ hμ) n f k

/-- The same original response supplies measurable finite Pc summands without a reader-norm premise. -/
theorem spin_profile_continuous (F : Index) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (sharp : Bool) (m ell n : ℕ) (f k : QuantumTest) :
    Continuous (fun w : ℝ => coframeProfile F seed (line μ w)
      (compressionSpin sharp m ell F) f k n 0) :=
  profile_continuous F seed (compressionSpin sharp m ell F) μ hμ n f k

end LowEnergy.SourceInverseSpinCompressionBudget
