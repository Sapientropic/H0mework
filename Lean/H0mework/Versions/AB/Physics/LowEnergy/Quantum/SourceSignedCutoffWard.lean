import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceMixedCurrentJets
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePhysicalHamiltonianSquare
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFixedJetBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace LowEnergy.SourceSignedCutoffWard
open MeasureTheory Filter GaussCoreHilbert GaussCoreDifferential GaussFockPair
open GaussDiagonalHistory GaussUnitaryHistory SourceCoframeVolumeCurrent
open SourceMixedNativeReturn SourcePhysicalHamiltonianSquare SourceMinimalGraphParticular SourceEscapeCurrent
open SourceRelativePowerTail SourceFixedJetBudget SourceCoframeStrongJet SourceCoframeScaleTransport
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open scoped InnerProductSpace Topology

/-- Literal original core commutator; the radial contraction is a downstream representation of this action. -/
def cutoffContact (m ell : ℕ) : CoreEnd :=
  diagonalAction*thetaAction m ell-thetaAction m ell*diagonalAction

private theorem star_im_ne (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- Both defects belong to the same finite carrier and their actual opposite-frequency source cores. -/
def wardCross (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) : ℂ :=
  sourcePair (coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k))
    (cutoffContact m ell (coreEquiv.symm (sourceCore F z hz g)))-
  inner ℂ (finiteProjectionDefect F (star z) (star_im_ne z hz) k)
    (relativeTail m ell (finiteResolvent F z (g : H)))+
  inner ℂ (relativeTail m ell (finiteResolvent F (star z) (k : H)))
    (finiteProjectionDefect F z hz g)

private theorem core_embed (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

private theorem power_sub_selfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Q : E →L[ℂ] E) (hQ : IsSelfAdjoint Q) (m n : ℕ) :
    IsSelfAdjoint (Q^m-Q^n) := (hQ.pow m).sub (hQ.pow n)

private theorem tail_selfAdjoint (m ell : ℕ) : IsSelfAdjoint (relativeTail m ell) := by
  have hq : IsSelfAdjoint sourceComplement :=
    ((ContinuousLinearMap.nonneg_iff_isPositive sourceComplement).mp source_complement_nonnegative).isSymmetric.isSelfAdjoint
  simpa only [relativeTail] using! power_sub_selfAdjoint sourceComplement hq (m+1) (ell+1)

private theorem tail_pair (m ell : ℕ) (x y : H) :
    inner ℂ (relativeTail m ell x) y=inner ℂ x (relativeTail m ell y) :=
  (tail_selfAdjoint m ell).isSymmetric x y

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (thetaAction m ell g)=sourcePair (thetaAction m ell f) g := by
  change inner ℂ (embed f) (embed (thetaAction m ell g))=
    inner ℂ (embed (thetaAction m ell f)) (embed g)
  rw [←SourceMixedNativeReturn.theta_core,←SourceMixedNativeReturn.theta_core]
  exact (tail_pair m ell _ _).symm

theorem actual_contact_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (cutoffContact m ell g)=
      sourcePair (diagonalAction f) (thetaAction m ell g)-
        sourcePair (thetaAction m ell f) (diagonalAction g) := by
  change inner ℂ (embed f) (embed (diagonalAction (thetaAction m ell g)-thetaAction m ell (diagonalAction g)))=_
  rw [map_sub,inner_sub_right]
  change sourcePair f (diagonalAction (thetaAction m ell g))-sourcePair f (thetaAction m ell (diagonalAction g))=_
  exact congrArg₂ (fun a b : ℂ => a-b) (diagonalAction_pair f (thetaAction m ell g))
    (theta_pair m ell f (diagonalAction g))

private theorem resolvent_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (z : ℂ) (hz : z.im≠0) (k f : E) :
    inner ℂ k (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k) f := by
  have hk := congrArg (fun A : E →L[ℂ] E => A k) (resolvent_right C hC (star z) (star_im_ne z hz))
  have hf := congrArg (fun A : E →L[ℂ] E => A f) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
    star z • FullYSourceResolventGraphSplice.resolvent C (star z) k=k at hk
  change C (FullYSourceResolventGraphSplice.resolvent C z f)-
    z • FullYSourceResolventGraphSplice.resolvent C z f=f at hf
  have hs : inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k))
      (FullYSourceResolventGraphSplice.resolvent C z f)=
      inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
        (C (FullYSourceResolventGraphSplice.resolvent C z f)) := hC.isSymmetric _ _
  calc
    _ = inner ℂ (C (FullYSourceResolventGraphSplice.resolvent C (star z) k)-
      star z • FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (FullYSourceResolventGraphSplice.resolvent C z f) := congrArg (fun x => inner ℂ x _) hk.symm
    _ = inner ℂ (FullYSourceResolventGraphSplice.resolvent C (star z) k)
      (C (FullYSourceResolventGraphSplice.resolvent C z f)-z • FullYSourceResolventGraphSplice.resolvent C z f) := by
      rw [inner_sub_left,inner_smul_left,inner_sub_right,inner_smul_right,hs,
        starRingEnd_apply,star_star]
    _ = _ := congrArg (fun x => inner ℂ _ x) hf

private theorem green_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E) (hS : ∀ x y : E, inner ℂ (S x) y=inner ℂ x (S y)) (z : ℂ) (p q k g dp dq : E) :
    inner ℂ (k+star z • p+dp) (S q)-inner ℂ (S p) (g+z • q+dq)-
      inner ℂ dp (S q)+inner ℂ (S p) dq=
      inner ℂ (S k) q-inner ℂ p (S g) := by
  rw [inner_add_left,inner_add_left,inner_smul_left,starRingEnd_apply,star_star,
    inner_add_right,inner_add_right,inner_smul_right,←hS p q,
    ←hS k q,hS p g]
  ring

private theorem green_from_contact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : E →L[ℂ] E) (hS : ∀ x y : E, inner ℂ (S x) y=inner ℂ x (S y))
    (z : ℂ) (p q k g dp dq : E) (c : ℂ)
    (hc : c=inner ℂ (k+star z • p+dp) (S q)-inner ℂ (S p) (g+z • q+dq)) :
    c-inner ℂ dp (S q)+inner ℂ (S p) dq=inner ℂ (S k) q-inner ℂ p (S g) := by
  rw [hc]
  exact green_algebra S hS z p q k g dp dq

/-- A complete contact/defect cross returns two original fixed cutoff sources; no defect is discarded. -/
theorem actual_signed_cutoff_ward (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    wardCross m ell F z hz g k=
      inner ℂ (relativeTail m ell (k : H)) (finiteResolvent F z (g : H))-
      inner ℂ (k : H) (finiteResolvent F z (relativeTail m ell (g : H))) := by
  let p := coreEquiv.symm (sourceCore F (star z) (star_im_ne z hz) k)
  let q := coreEquiv.symm (sourceCore F z hz g)
  have hp : embed (diagonalAction p)=(k : H)+star z • finiteResolvent F (star z) (k : H)+
      finiteProjectionDefect F (star z) (star_im_ne z hz) k := by
    simpa only [p] using! source_core_action F (star z) (star_im_ne z hz) k
  have hq : embed (diagonalAction q)=(g : H)+z • finiteResolvent F z (g : H)+
      finiteProjectionDefect F z hz g := by simpa only [q] using! source_core_action F z hz g
  have htp : embed (thetaAction m ell p)=relativeTail m ell (finiteResolvent F (star z) (k : H)) := by
    rw [←SourceMixedNativeReturn.theta_core]
    exact congrArg (relativeTail m ell) (core_embed _)
  have htq : embed (thetaAction m ell q)=relativeTail m ell (finiteResolvent F z (g : H)) := by
    rw [←SourceMixedNativeReturn.theta_core]
    exact congrArg (relativeTail m ell) (core_embed _)
  have hcontact := (actual_contact_pair m ell p q).trans
    (congrArg₂ (fun a b : ℂ => a-b) (congrArg₂ (inner ℂ) hp htq) (congrArg₂ (inner ℂ) htp hq))
  have hw : wardCross m ell F z hz g k=
      inner ℂ (relativeTail m ell (k : H)) (finiteResolvent F z (g : H))-
      inner ℂ (finiteResolvent F (star z) (k : H)) (relativeTail m ell (g : H)) := by
    change sourcePair p (cutoffContact m ell q)-
      inner ℂ (finiteProjectionDefect F (star z) (star_im_ne z hz) k)
        (relativeTail m ell (finiteResolvent F z (g : H)))+
      inner ℂ (relativeTail m ell (finiteResolvent F (star z) (k : H)))
        (finiteProjectionDefect F z hz g)=_
    exact green_from_contact (relativeTail m ell) (tail_pair m ell) z
      (finiteResolvent F (star z) (k : H)) (finiteResolvent F z (g : H)) (k : H) (g : H)
      (finiteProjectionDefect F (star z) (star_im_ne z hz) k) (finiteProjectionDefect F z hz g)
      (sourcePair p (cutoffContact m ell q)) hcontact
  have hr : inner ℂ (k : H) (finiteResolvent F z (relativeTail m ell (g : H)))=
      inner ℂ (finiteResolvent F (star z) (k : H)) (relativeTail m ell (g : H)) :=
    resolvent_pair _ (GaussGradedCompression.compression_selfAdjoint F) z hz _ _
  exact hw.trans (congrArg (fun a : ℂ =>
    inner ℂ (relativeTail m ell (k : H)) (finiteResolvent F z (g : H))-a) hr.symm)

private theorem profile_zero (F : Index) (z : ℂ) (k g : QuantumTest) :
    profileJet 0 0 0 F z k g 0=inner ℂ (embed k) (finiteResolvent F z (embed g)) := by
  have hk : strongJet 0 k 0=embed k :=
    (strong_jet_zero k 0).trans (congrArg embed (coreFlow_zero k))
  have hg : strongJet 0 g 0=embed g :=
    (strong_jet_zero g 0).trans (congrArg embed (coreFlow_zero g))
  exact congrArg₂ (inner ℂ) hk (congrArg (finiteResolvent F z) hg)

private theorem ward_profiles (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) :
    wardCross m ell F z hz g k=
      profileJet 0 0 0 F z (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0-
      profileJet 0 0 0 F z (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0 := by
  have hk := (tail_core m ell (coreEquiv.symm k)).trans
    (congrArg (relativeTail m ell) (core_embed k))
  have hg := (tail_core m ell (coreEquiv.symm g)).trans
    (congrArg (relativeTail m ell) (core_embed g))
  have hl := (profile_zero F z (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g)).trans
    (congrArg₂ (inner ℂ) hk (congrArg (finiteResolvent F z) (core_embed g)))
  have hr := (profile_zero F z (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g))).trans
    (congrArg₂ (inner ℂ) (core_embed k) (congrArg (finiteResolvent F z) hg))
  exact (actual_signed_cutoff_ward m ell F z hz g k).trans
    (congrArg₂ (fun a b : ℂ => a-b) hl hr).symm

private theorem two_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a-b),norm_nonneg a,norm_nonneg b]

private theorem difference_square_integrable (f h : ℝ → ℂ)
    (hf : Integrable (fun w => ‖f w‖^2)) (hh : Integrable (fun w => ‖h w‖^2))
    (hc : Continuous (fun w => f w-h w)) : Integrable (fun w => ‖f w-h w‖^2) := by
  apply ((hf.add hh).const_mul 2).mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact two_square _ _

private theorem ward_square_integrable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    Integrable (fun w : ℝ => ‖wardCross m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2) := by
  have hi := difference_square_integrable
    (fun w => profileJet 0 0 0 F (line μ w) (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0)
    (fun w => profileJet 0 0 0 F (line μ w) (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0)
    (profile_jet_square_integrable 0 0 0 F μ hμ (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0)
    (profile_jet_square_integrable 0 0 0 F μ hμ (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0)
    ((profile_jet_frequency_continuous 0 0 0 F μ hμ (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0).sub
      (profile_jet_frequency_continuous 0 0 0 F μ hμ (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0))
  apply hi.congr
  exact Eventually.of_forall (fun w => congrArg (fun a : ℂ => ‖a‖^2)
    (ward_profiles m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k).symm)

/-- Quantitative frequency budget: F is fixed before integration and is absent from the right side. -/
theorem actual_signed_cutoff_ward_energy (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∫ w : ℝ, ‖wardCross m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2) ≤
      (2*Real.pi/μ)*(‖relativeTail m ell (k : H)‖^2*‖(g : H)‖^2+
        ‖(k : H)‖^2*‖relativeTail m ell (g : H)‖^2) := by
  have hl := profile_jet_square_integrable 0 0 0 F μ hμ (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0
  have hr := profile_jet_square_integrable 0 0 0 F μ hμ (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0
  have hb (w : ℝ) := two_square
    (profileJet 0 0 0 F (line μ w) (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0)
    (profileJet 0 0 0 F (line μ w) (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0)
  have hm := integral_mono (ward_square_integrable m ell F μ hμ g k)
    ((hl.add hr).const_mul 2) (fun w => by rw [ward_profiles]; exact hb w)
  rw [integral_const_mul] at hm
  simp only [Pi.add_apply] at hm
  rw [integral_add hl hr] at hm
  have he := add_le_add
    (actual_profile_jet_energy 0 0 0 F μ hμ (tailAction m ell (coreEquiv.symm k)) (coreEquiv.symm g) 0)
    (actual_profile_jet_energy 0 0 0 F μ hμ (coreEquiv.symm k) (tailAction m ell (coreEquiv.symm g)) 0)
  simp only [profileJetBudget,pow_zero,Module.End.one_apply,tail_core,core_embed] at he
  exact hm.trans ((mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))

/-- The whole signed contact/defect response has a full-frequency tail, uniform in F and upper cutoff. -/
theorem actual_signed_cutoff_ward_tail (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal
        (‖wardCross m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hC : 0<Real.pi/μ := div_pos Real.pi_pos hμ
  have hδ : 0<ε/(4*(Real.pi/μ)) := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨N₁,h₁⟩ := fixed_left_jet_budget_tail 0 0 0 (coreEquiv.symm k) (coreEquiv.symm g) _ hδ
  obtain ⟨N₂,h₂⟩ := fixed_right_jet_budget_tail 0 0 0 (coreEquiv.symm k) (coreEquiv.symm g) _ hδ
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell
  have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell
  simp only [profileJetBudget,pow_zero,Module.End.one_apply,tail_core,core_embed] at hl hr
  rw [←ofReal_integral_eq_lintegral_ofReal (ward_square_integrable m ell F μ hμ g k)
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  apply (actual_signed_cutoff_ward_energy m ell F μ hμ g k).trans
  calc
    _ ≤ (2*Real.pi/μ)*(ε/(4*(Real.pi/μ))+ε/(4*(Real.pi/μ))) := by gcongr
    _ = ε := by field_simp; ring

end LowEnergy.SourceSignedCutoffWard
