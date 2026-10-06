import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeCoframeNeutralSplice
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeReducedGaugeJointTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseCoframeJointTailReturn
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseCoframeNeutralSplice SourceInverseCoframeCompressionBudget
open SourceInverseFirstCurrentJointTail SourceInverseReducedGaugeJointTail
open SourceGaugeCoframeWard SourceGaugeCoframeJets SourceScalarForceBudget SourceJointResidualEnergy
open SourceFourPoleEnergyClosed SourceResolventBandLimit SourceMixedNativeReturn
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ENNReal InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] coframeReducedRemainder neutralRemainder sourceRead
  sandwichJet readOrbitJet resolventJet finiteResolvent jointResidual

/-- The original mass normalizes the single-Q coframe remainder on the unchanged joint source legs. -/
def coframeJointProfile (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H)
    (coframeReducedRemainder sharp m ell F g z (g : H))

private theorem mass_ne : (oscillatorMass : ℂ)≠0 := by
  exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ)≠0)
    (pow_ne_zero 2 GaussNativeEnergy.source_time_nonzero))

private theorem joint_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    jointResidual sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k-
      coframeJointProfile sharp m ell F g k (line μ w)=
    (oscillatorMass : ℂ)⁻¹*
      ((inner ℂ (k : H) (wardOperator sharp m ell F g (line μ w) (g : H))-
        inner ℂ (k : H) (coframeReducedRemainder sharp m ell F g (line μ w) (g : H)))-
        SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w)) := by
  have hf := actual_force_profile_return sharp m ell F μ hμ g k w
  rw [actual_ward_profile sharp m ell F g k (line μ w)
    (by simpa only [line_im] using hμ.ne')] at hf
  have h := congrArg (fun c : ℂ => (oscillatorMass : ℂ)⁻¹*c) hf
  rw [←mul_assoc,inv_mul_cancel₀ mass_ne,one_mul] at h
  unfold coframeJointProfile
  unfold wardProfile at h
  have hd : response F (line μ w) (doubleResponse sharp m ell F g) (g : H) (k : H)=
      SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w) := rfl
  rw [hd] at h
  rw [←h]
  ring

private def Tail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))≤ENNReal.ofReal ε

private theorem tail_smul (f : ℕ → ℕ → Index → ℝ → ℂ) (c : ℂ)
    (hf : Tail f) : Tail (fun m ell F w => c*f m ell F w) := by
  intro ε hε
  have hc : 0<‖c‖^2+1 := by positivity
  obtain ⟨N,hN⟩ := hf (ε/(‖c‖^2+1)) (div_pos hε hc)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  simp only [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply (mul_le_mul_of_nonneg_left hF (by positivity)).trans
  rw [←ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  apply ENNReal.ofReal_le_ofReal
  have hd : 0<‖c‖^2+1 := by positivity
  exact (mul_le_mul_of_nonneg_right (by linarith : ‖c‖^2 ≤ ‖c‖^2+1)
    (div_pos hε hd).le).trans_eq (mul_div_cancel₀ ε hd.ne')

private theorem tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hfmeas : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) volume)
    (hf : Tail f) (hg : Tail g) :
    Tail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell,hfmeas m ell] with F hl hr hmeas
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ,ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x)
        (lintegral_add_left' hmeas _)
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

private def gp (A B : ℕ → ℝ → Op) : ℕ → ℕ → ℕ → ℝ → Op
  | 0,r,u,w => A r w*B u w
  | n+1,r,u,w => gp A B n (r+1) u w+gp A B n r (u+1) w

private theorem gp_continuous (A B : ℕ → ℝ → Op) (hA : ∀ r,Continuous (A r))
    (hB : ∀ u,Continuous (B u)) (n r u : ℕ) : Continuous (gp A B n r u) := by
  induction n generalizing r u with
  | zero => exact (hA r).mul (hB u)
  | succ n ih => exact (ih (r+1) u).add (ih r (u+1))

private theorem inverse_jet_continuous (F : Index) (μ : ℝ) (hμ : 0<μ) (j : ℕ) :
    Continuous (fun w : ℝ => resolventJet F (line μ w) j 0 0 0) := by
  have hz (w : ℝ) : line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact hμ.ne' (by simpa only [line_im,Complex.zero_im] using hi)
  have hd (r w : ℝ) : (r : ℂ)-line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hμ.ne' hi
  have hl : Continuous (line μ) := by unfold line; fun_prop
  have hzi := hl.inv₀ hz
  have hdi (r : ℝ) := (continuous_const.sub hl).inv₀ (hd r)
  unfold resolventJet
  have hs : Continuous (fun w : ℝ => ∑ i : SourceJointResidualEnergy.SpectralIndex F,
      ((((SourceJointResidualEnergy.channelValue F (some i) : ℂ)-line μ w)⁻¹+(line μ w)⁻¹) •
        SourceGaugeCoframeJets.rankJet j 0 (SourceMovingJetFlux.eigenTest F i) (SourceMovingJetFlux.eigenTest F i) 0 0)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hdi _).add hzi).smul continuous_const
  split_ifs
  · exact (hzi.neg.smul continuous_const).add hs
  · exact continuous_const.add hs

private theorem small_sandwich (F : Index) (seed : diagonal.domain) (A : End) (μ w : ℝ) (n : ℕ) (hn : n≤3) :
    sandwichJet F seed (line μ w) A n 0 0 0=
      gp (fun j w => resolventJet F (line μ w) j 0 0 0)
        (fun j w => gp (fun a _ => readOrbitJet F seed A a 0 0 0)
          (fun a w => resolventJet F (line μ w) a 0 0 0) j 0 0 w) n 0 0 w := by
  unfold sandwichJet
  interval_cases n <;> rfl

private theorem small_sandwich_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : ℕ) (hn : n≤3) :
    Continuous (fun w : ℝ => sandwichJet F seed (line μ w) A n 0 0 0) := by
  have hc := gp_continuous (fun j w => resolventJet F (line μ w) j 0 0 0)
    (fun j w => gp (fun a _ => readOrbitJet F seed A a 0 0 0)
      (fun a w => resolventJet F (line μ w) a 0 0 0) j 0 0 w)
    (inverse_jet_continuous F μ hμ)
    (fun j => gp_continuous _ _ (fun _ => continuous_const) (inverse_jet_continuous F μ hμ) j 0 0) n 0 0
  exact hc.congr (fun w => (small_sandwich F seed A μ w n hn).symm)

private theorem coframe_remainder_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    Continuous (fun w : ℝ => coframeReducedRemainder sharp m ell F g (line μ w)) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hn : Continuous (fun w : ℝ => neutralRemainder sharp m ell F g (line μ w)) := by
    unfold neutralRemainder
    exact (hr.mul continuous_const).mul hr
  have hrest : Continuous (fun w : ℝ => coframeRest
      (fun a => sandwichJet F g (line μ w) (compressionNeutral sharp m ell F) a 0 0 0)) := by
    unfold coframeRest
    exact ((small_sandwich_continuous F g _ μ hμ 3 (by omega)).add
      ((small_sandwich_continuous F g _ μ hμ 2 (by omega)).const_smul (12 : ℂ))).add
      ((small_sandwich_continuous F g _ μ hμ 1 (by omega)).const_smul (44 : ℂ))
  apply (hn.add (hrest.const_smul (1/48 : ℂ))).congr
  intro w
  have he := actual_neutral_coframe_remainder sharp m ell F g (line μ w)
    (by simpa only [line_im] using hμ.ne')
  exact (eq_add_of_sub_eq he.symm).symm

private theorem profile_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    Continuous (fun w : ℝ => coframeJointProfile sharp m ell F g k (line μ w)) := by
  unfold coframeJointProfile
  exact (continuous_const.inner
    ((coframe_remainder_continuous sharp m ell F g μ hμ).clm_apply continuous_const)).const_mul _

private theorem joint_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    Continuous (fun w : ℝ => jointResidual sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hc : Continuous (fun w : ℝ => inner ℂ (k : H)
      (finiteResolvent F (line μ w) (jointInsertion sharp m ell F (finiteResolvent F (line μ w) (g : H))))) :=
    continuous_const.inner (hr.clm_apply (continuous_const.clm_apply (hr.clm_apply continuous_const)))
  exact hc.congr (fun w => (actual_joint_as_same_compression sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k).symm)

private theorem double_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    Continuous (fun w : ℝ => SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w)) := by
  unfold SourceScalarDoubleEndpoint.doubleResponse
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact continuous_const.inner (hr.clm_apply (continuous_const.clm_apply (hr.clm_apply continuous_const)))

/-- The original joint differs from the normalized single-Q coframe remainder by an actual common full-frequency tail. -/
theorem actual_joint_coframe_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖jointResidual sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k-
          coframeJointProfile sharp m ell F g k (line μ w)‖^2))≤ENNReal.ofReal ε := by
  have hw := actual_ward_coframe_reduced_difference_tail sharp μ hμ (coreEquiv.symm g) (coreEquiv.symm k)
  have hc (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  simp only [coreEquiv.apply_symm_apply,hc] at hw
  have hd : Tail (fun m ell F w => SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w)) :=
    SourceScalarDoubleEndpoint.actual_double_tail sharp g k μ hμ
  have hdn := tail_smul _ (-1 : ℂ) hd
  have hdm : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal
        (‖(-1 : ℂ)*SourceScalarDoubleEndpoint.doubleResponse sharp m ell F g k (line μ w)‖^2)) volume := by
    intro m ell
    exact Filter.Eventually.of_forall (fun F =>
      (((double_continuous sharp m ell F g k μ hμ).const_mul (-1)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable)
  have ht := tail_smul _ (oscillatorMass : ℂ)⁻¹ (tail_add _ _ hdm hdn hw)
  apply tail_congr _ _ (fun m ell => Filter.Eventually.of_forall (fun F w => ?_)) ht
  rw [joint_return sharp m ell F μ hμ g k w]
  ring

/-- The original closed joint cost tail is equivalent to the normalized single-Q coframe profile tail. -/
theorem actual_joint_coframe_tail_iff (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H)≤ε) ↔
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖coframeJointProfile sharp m ell F g k (line μ w)‖^2))≤ENNReal.ofReal ε) := by
  let J := fun m ell F w => jointResidual sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k
  let P := fun m ell F w => coframeJointProfile sharp m ell F g k (line μ w)
  let D := fun m ell F w => J m ell F w-P m ell F w
  have hD : Tail D := actual_joint_coframe_difference_tail sharp μ hμ g k
  have hDm : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal (‖D m ell F w‖^2)) volume := by
    intro m ell
    exact Filter.Eventually.of_forall (fun F =>
      (((joint_continuous sharp m ell F g k μ hμ).sub
        (profile_continuous sharp m ell F g k μ hμ)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable)
  have hnDm : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal (‖(-1 : ℂ)*D m ell F w‖^2)) volume := by
    intro m ell
    exact Filter.Eventually.of_forall (fun F =>
      ((((joint_continuous sharp m ell F g k μ hμ).sub
        (profile_continuous sharp m ell F g k μ hμ)).const_mul (-1)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable)
  have hJP : Tail J ↔ Tail P := by
    constructor
    · intro hJ
      have ht := tail_add _ _ hnDm (tail_smul D (-1 : ℂ) hD) hJ
      exact tail_congr _ _ (fun _ _ => Filter.Eventually.of_forall (fun _ _ => by dsimp [D]; ring)) ht
    · intro hP
      have ht := tail_add D P hDm hD hP
      exact tail_congr _ _ (fun _ _ => Filter.Eventually.of_forall (fun _ _ => by dsimp [D]; ring)) ht
  have hCJ : (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),closedJointCost sharp m ell F μ (g : H) (k : H)≤ε) ↔ Tail J := by
    constructor <;> intro h ε hε
    · obtain ⟨N,hN⟩ := h ε hε
      refine ⟨N,fun m hm ell hell => ?_⟩
      filter_upwards [hN m hm ell hell] with F hF
      exact (actual_joint_closed_lintegral sharp m ell F μ hμ g k).trans_le (ENNReal.ofReal_le_ofReal hF)
    · obtain ⟨N,hN⟩ := h ε hε
      refine ⟨N,fun m hm ell hell => ?_⟩
      filter_upwards [hN m hm ell hell] with F hF
      exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp
        ((actual_joint_closed_lintegral sharp m ell F μ hμ g k).symm.trans_le hF)
  exact hCJ.trans hJP

end LowEnergy.SourceInverseCoframeJointTailReturn
