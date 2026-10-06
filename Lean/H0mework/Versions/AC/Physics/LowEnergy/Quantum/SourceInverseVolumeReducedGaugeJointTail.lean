import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeCompressionGaugeSplice
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeCompressionGaugeReturn
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeFirstCurrentJointTail
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceGaugeCoframeWard

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseReducedGaugeJointTail
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceInverseCompressionGaugeSplice SourceInverseFirstCurrentJointTail
open SourceGaugeCoframeWard SourceScalarForceBudget SourceJointResidualEnergy
open SourceFourPoleEnergyClosed SourceResolventBandLimit
open SourceInverseCompressionGaugeBudget SourceInverseFirstCurrentGaugeJets
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ENNReal InnerProductSpace

def reducedJointProfile (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*inner ℂ (k : H)
    ((reducedGaugeRemainder sharp m ell F g z-
      finiteResolvent F z*doubleResponse sharp m ell F g*finiteResolvent F z) (g : H))

private theorem mass_ne : (oscillatorMass : ℂ)≠0 := by
  have hn : (GaussNativeEnergy.sourceTime 0 : ℝ)≠0 := by
    rw [GaussNativeEnergy.source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos.ne'
  exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ)≠0) (pow_ne_zero 2 hn))

private theorem response_sandwich (F : Index) (z : ℂ) (A : H →L[ℂ] H) (g k : H) :
    response F z A g k=
      inner ℂ k ((finiteResolvent F z*A*finiteResolvent F z) g) := rfl

/-- The original force, full Ward and double response share one actual finite resolvent. -/
theorem actual_joint_reduced_profile (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    jointResidual sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k-
      reducedJointProfile sharp m ell F g k (line μ w)=
    (oscillatorMass : ℂ)⁻¹*
      (inner ℂ (k : H) (wardOperator sharp m ell F g (line μ w) (g : H))-
        inner ℂ (k : H) (reducedGaugeRemainder sharp m ell F g (line μ w) (g : H))) := by
  have hf := actual_force_profile_return sharp m ell F μ hμ g k w
  rw [actual_ward_profile sharp m ell F g k (line μ w)
    (by simpa only [line_im] using hμ.ne')] at hf
  have h := congrArg (fun c : ℂ => (oscillatorMass : ℂ)⁻¹*c) hf
  rw [←mul_assoc,inv_mul_cancel₀ mass_ne,one_mul] at h
  rw [wardProfile,response_sandwich] at h
  unfold reducedJointProfile
  simp only [sub_apply,inner_sub_right]
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

private def paidDifference (sharp : Bool) (μ : ℝ) (g k : diagonal.domain)
    (m ell : ℕ) (F : Index) (w : ℝ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*
    (inner ℂ (k : H) (wardOperator sharp m ell F g (line μ w) (g : H))-
      inner ℂ (k : H) (reducedGaugeRemainder sharp m ell F g (line μ w) (g : H)))

/-- The generated Ward--remainder correction is paid with the original joint source legs. -/
theorem actual_joint_reduced_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖jointResidual sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k-
          reducedJointProfile sharp m ell F g k (line μ w)‖^2))≤ENNReal.ofReal ε := by
  have hf := SourceInverseCompressionGaugeSplice.actual_ward_reduced_difference_tail
    sharp μ hμ (coreEquiv.symm g) (coreEquiv.symm k)
  change Tail (fun m ell F w =>
    inner ℂ (embed (coreEquiv.symm k))
      (wardOperator sharp m ell F (coreEquiv (coreEquiv.symm g)) (line μ w)
        (embed (coreEquiv.symm g)))-
    inner ℂ (embed (coreEquiv.symm k))
      (reducedGaugeRemainder sharp m ell F (coreEquiv (coreEquiv.symm g)) (line μ w)
        (embed (coreEquiv.symm g)))) at hf
  have hs := tail_smul _ (oscillatorMass : ℂ)⁻¹ hf
  have hc (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  change Tail (fun m ell F w => jointResidual sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k-
      reducedJointProfile sharp m ell F g k (line μ w))
  apply tail_congr _ _ ?_ hs
  intro m ell
  exact Filter.Eventually.of_forall (fun F w => by
    rw [actual_joint_reduced_profile sharp m ell F μ hμ g k w]
    simp only [coreEquiv.apply_symm_apply,hc])

private def correctedProfile (sharp : Bool) (μ : ℝ) (g k : diagonal.domain)
    (m ell : ℕ) (F : Index) (w : ℝ) : ℂ :=
  (oscillatorMass : ℂ)⁻¹*((1/6 : ℂ)*
    inner ℂ (embed (coreEquiv.symm k))
      (gaugeFilter (fun n => correctedCompressionJet sharp m ell F g (line μ w) n 0)
        (embed (coreEquiv.symm g))))

private theorem corrected_continuous (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) (m ell : ℕ) (F : Index) :
    Continuous (correctedProfile sharp μ g k m ell F) := by
  let f := coreEquiv.symm g
  let q := coreEquiv.symm k
  have hc (n : ℕ) : Continuous (fun w : ℝ => inner ℂ (embed q)
      (correctedCompressionJet sharp m ell F g (line μ w) n 0 (embed f))) := by
    have h := (gauge_profile_continuous F g (compressionFirst sharp m ell F) μ hμ (n+1) f q).sub
      (gauge_profile_continuous F g (compressionMatter sharp m ell F) μ hμ n f q)
    apply h.congr
    intro w
    simp only [correctedCompressionJet,SourceInverseCompressionGaugeBudget.gaugeProfile,
      Pi.sub_apply,sub_apply,inner_sub_right]
  have h := ((hc 2).sub ((hc 1).const_mul (3 : ℂ))).add ((hc 0).const_mul (2 : ℂ))
  apply (h.const_mul ((oscillatorMass : ℂ)⁻¹/6)).congr
  intro w
  simp only [correctedProfile,gaugeFilter,sub_apply,add_apply,smul_apply,
    inner_sub_right,inner_add_right,inner_smul_right,Pi.sub_apply,Pi.add_apply,f,q]
  ring

private theorem corrected_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : Tail (correctedProfile sharp μ g k) := by
  have h := actual_corrected_filter_tail sharp g μ hμ (coreEquiv.symm g) (coreEquiv.symm k)
  change Tail (fun m ell F w => (1/6 : ℂ)*inner ℂ (embed (coreEquiv.symm k))
    (gaugeFilter (fun n => correctedCompressionJet sharp m ell F g (line μ w) n 0)
      (embed (coreEquiv.symm g)))) at h
  have hs := tail_smul _ (oscillatorMass : ℂ)⁻¹ h
  exact hs

private theorem old_remaining_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    jointResidual sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k =
      ((oscillatorMass : ℂ)⁻¹/6)*filteredProfile sharp m ell F (line μ w)
        (coreEquiv.symm g) (coreEquiv.symm k)+
      remainingProfile sharp m ell F g k (line μ w) := by
  have h := congrArg (fun c : ℂ => (oscillatorMass : ℂ)⁻¹*c)
    (SourceInverseFirstCurrentForceTail.actual_joint_response sharp m ell F μ hμ g k w)
  rw [←mul_assoc,inv_mul_cancel₀ mass_ne,one_mul] at h
  exact h.trans (by unfold remainingProfile; ring)

private theorem actual_remaining_reduced_profile (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) (m ell : ℕ) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ w : ℝ,
      remainingProfile sharp m ell F g k (line μ w)=
        reducedJointProfile sharp m ell F g k (line μ w)+
          correctedProfile sharp μ g k m ell F w := by
  filter_upwards [actual_ward_reduced_gauge m ell (coreEquiv.symm g) (coreEquiv.symm k)]
    with F hF
  intro w
  have hW := hF sharp (line μ w) (by simpa only [line_im] using hμ.ne')
  have hc (x : diagonal.domain) : embed (coreEquiv.symm x)=(x : H) :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply x)
  simp only [coreEquiv.apply_symm_apply,hc] at hW
  have hOld := old_remaining_return sharp m ell F μ hμ g k w
  have hNew := actual_joint_reduced_profile sharp m ell F μ hμ g k w
  unfold correctedProfile
  rw [hc,hc] at ⊢
  linear_combination (norm := ring) -hOld+hNew+(oscillatorMass : ℂ)⁻¹*hW

/-- Both generated remainder descriptions remove the same compression current from the same Ward word. -/
theorem actual_source_remainder_eq_reduced (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    SourceInverseCompressionGaugeReturn.sourceRemainder sharp m ell F g z=
      reducedGaugeRemainder sharp m ell F g z := by
  have hSource := SourceInverseCompressionGaugeReturn.actual_remainder_split
    sharp m ell F g z hz
  have hReduced := actual_joined_remainder_split sharp m ell F g z hz
  unfold SourceInverseCompressionGaugeReturn.paidCompression at hSource
  exact (add_right_cancel (hSource.symm.trans hReduced))

/-- The original closed joint cost has exactly the reduced gauge profile as its next tail responsibility. -/
theorem actual_joint_reduced_tail_iff (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        closedJointCost sharp m ell F μ (g : H) (k : H)≤ε) ↔
    (∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖reducedJointProfile sharp m ell F g k
          (line μ w)‖^2))≤ENNReal.ofReal ε) := by
  rw [SourceInverseFirstCurrentJointTail.actual_joint_remaining_tail_iff sharp μ hμ g k]
  change Tail (fun m ell F w => remainingProfile sharp m ell F g k (line μ w)) ↔
    Tail (fun m ell F w => reducedJointProfile sharp m ell F g k (line μ w))
  have hc := corrected_tail sharp μ hμ g k
  have hcm : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal
        (‖correctedProfile sharp μ g k m ell F w‖^2)) volume := by
    intro m ell
    exact Filter.Eventually.of_forall (fun F =>
      (((corrected_continuous sharp μ hμ g k m ell F).norm.pow 2).measurable.ennreal_ofReal).aemeasurable)
  have hnm : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),
      AEMeasurable (fun w : ℝ => ENNReal.ofReal
        (‖(-1 : ℂ)*correctedProfile sharp μ g k m ell F w‖^2)) volume := by
    intro m ell
    exact Filter.Eventually.of_forall (fun F =>
      (((corrected_continuous sharp μ hμ g k m ell F).const_mul (-1)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable)
  constructor
  · intro hr
    have hs := tail_add (fun m ell F w => (-1 : ℂ)*correctedProfile sharp μ g k m ell F w)
      (fun m ell F w => remainingProfile sharp m ell F g k (line μ w))
      hnm (tail_smul _ (-1 : ℂ) hc) hr
    apply tail_congr _ _ ?_ hs
    intro m ell
    filter_upwards [actual_remaining_reduced_profile sharp μ hμ g k m ell] with F hF
    intro w
    have he := hF w
    rw [he]
    ring
  · intro hq
    have hs := tail_add (correctedProfile sharp μ g k)
      (fun m ell F w => reducedJointProfile sharp m ell F g k (line μ w))
      hcm hc hq
    apply tail_congr _ _ ?_ hs
    intro m ell
    filter_upwards [actual_remaining_reduced_profile sharp μ hμ g k m ell] with F hF
    intro w
    rw [hF w]
    ring

end LowEnergy.SourceInverseReducedGaugeJointTail
