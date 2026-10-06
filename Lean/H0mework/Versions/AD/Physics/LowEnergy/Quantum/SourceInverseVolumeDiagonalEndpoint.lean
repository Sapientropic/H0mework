import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeEndpoint
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeWindowBalance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseDiagonalEndpoint
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm SourcePhysicalKineticSquare
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarInverseEndpoint
open SourceScalarInverseBulk SourceScalarInverseEnergyExchange SourceInverseWindowBalance
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceRelativePowerTail
open SourceRetardedBandCurrent SourceHardyRetardedTail SourceCoframeVolume SourceCoframeVolumeCurrent MeasureTheory Filter
open scoped InnerProductSpace ENNReal

attribute [local irreducible] GaussDiagonalHistory.diagonalAction
  SourceScalarPositiveBulkWard.state SourceScalarPositiveBulkWard.resolvedBulk

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (theta m ell g)=sourcePair (theta m ell f) g := multiply_pair _ _ _ _
private theorem theta_inverse (m ell : ℕ) (f : QuantumTest) :
    theta m ell (inverseVolumeAction f)=inverseVolumeAction (theta m ell f) := by
  apply DFunLike.ext
  intro z
  exact smul_comm (SourceNativeCutoffContact.theta m ell z : ℂ)
    (reciprocalVolume z : ℂ) (f z)
private theorem endpoint_left (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (inverseVolumeAction (theta m ell f))
      (volumeAction (inverseVolumeAction (theta m ell g)))=sourcePair (endpoint m ell f) g := by
  rw [volume_inverse,theta_pair]
  change sourcePair (theta m ell (inverseVolumeAction (theta m ell f))) g=
    sourcePair (theta m ell (theta m ell (inverseVolumeAction f))) g
  simp only [theta_inverse]
private theorem endpoint_right (m ell : ℕ) (f g : QuantumTest) :
    sourcePair (volumeAction (inverseVolumeAction (theta m ell f)))
      (inverseVolumeAction (theta m ell g))=sourcePair f (endpoint m ell g) := by
  rw [volume_inverse,←theta_pair]
  change sourcePair f (theta m ell (inverseVolumeAction (theta m ell g)))=
    sourcePair f (theta m ell (theta m ell (inverseVolumeAction g)))
  simp only [theta_inverse]
private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g : H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

/-- The diagonal forcing uses the original fixed source and its conjugate pairing, with no resolvent-source substitution. -/
theorem actual_diagonal_fixed_endpoints (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    fixedBulk F z z hz hz g g (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)=
      (-3*(vacuumJetCoefficient : ℂ))*(
        inner ℂ (embed (endpoint m ell (coreEquiv.symm g))) (finiteResolvent F z (g : H))+
        inner ℂ (finiteResolvent F z (g : H)) (embed (endpoint m ell (coreEquiv.symm g)))) := by
  have h := congrArg (fun P : PairMatrix => P (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell))
    (SourceScalarPositiveBulkEndpoint.actual_fixed_bulk_collapse F z z hz hz g g)
  change fixedBulk F z z hz hz g g (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)=
    (-6*(vacuumJetCoefficient : ℂ))*((1/2 : ℂ)*(
      sourcePair (inverseVolumeAction (theta m ell (coreEquiv.symm g)))
        (volumeAction (inverseVolumeAction (theta m ell (state F z hz g))))+
      sourcePair (volumeAction (inverseVolumeAction (theta m ell (state F z hz g))))
        (inverseVolumeAction (theta m ell (coreEquiv.symm g))))) at h
  rw [endpoint_left,endpoint_right] at h
  simp only [sourcePair,state_embed] at h
  exact h.trans (by ring)

private theorem paired_bound (c : ℂ) (a b : H) :
    ‖c*(inner ℂ a b+inner ℂ b a)‖^2 ≤ 4*‖c‖^2*‖a‖^2*‖b‖^2 := by
  have h := (norm_add_le (inner ℂ a b) (inner ℂ b a)).trans
    (add_le_add (norm_inner_le_norm a b) (norm_inner_le_norm b a))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c‖)).trans_eq (by ring)

/-- The full real-frequency forcing estimate is uniform in F and retains the actual fixed endpoint norm. -/
theorem actual_diagonal_fixed_energy (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedBulk F (line μ w) (line μ w)
      (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
      (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖^2)) ≤
      ENNReal.ofReal ((4*‖-3*(vacuumJetCoefficient : ℂ)‖^2)*(Real.pi/μ)*
        ‖embed (endpoint m ell (coreEquiv.symm g))‖^2*‖(g : H)‖^2) := by
  let C := (4*‖-3*(vacuumJetCoefficient : ℂ)‖^2)*‖embed (endpoint m ell (coreEquiv.symm g))‖^2
  have hC : 0 ≤ C := by dsimp [C];positivity
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖(g : H)‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using!
      SourceActualResolventEnergy.actual_square_lintegral F μ hμ (g : H)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [actual_diagonal_fixed_endpoints,←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (paired_bound _ _ _)
    _=ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) (g : H)‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _=_ := by
      rw [he,←ENNReal.ofReal_mul hC]
      congr 1
      dsimp [C]
      ring

private theorem fixed_endpoint_tail (f : QuantumTest) (C : ℝ) (hC : 0 ≤ C) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      C*‖embed (endpoint m ell f)‖^2 ≤ ε := by
  intro ε hε
  have hp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := original_relative_tail (embed (inverseVolumeAction f))
    (Real.sqrt (ε/(C+1))) (Real.sqrt_pos.mpr (div_pos hε hp))
  refine ⟨N,fun m hm ell hell => ?_⟩
  have he : ‖embed (endpoint m ell f)‖ ≤ ‖relativeTail m ell (embed (inverseVolumeAction f))‖ := by
    rw [endpoint,SourceNativeCutoffContact.theta_core,SourceNativeCutoffContact.theta_core]
    exact relative_tail_contraction m ell hell _
  have hb := he.trans (hN m hm ell hell).le
  have hs := Real.sq_sqrt (div_pos hε hp).le
  have hb2 : ‖embed (endpoint m ell f)‖^2 ≤ ε/(C+1) := by
    nlinarith [norm_nonneg (embed (endpoint m ell f)),Real.sqrt_nonneg (ε/(C+1))]
  calc
    _ ≤ (C+1)*‖embed (endpoint m ell f)‖^2 := by nlinarith [sq_nonneg ‖embed (endpoint m ell f)‖]
    _ ≤ (C+1)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hb2 hp.le
    _=ε := mul_div_cancel₀ ε hp.ne'

/-- The actual diagonal source forcing has a common all-F full-frequency tail; N is independent of ell and F. -/
theorem actual_diagonal_fixed_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖fixedBulk F (line μ w) (line μ w)
        (by simpa only [line_im] using hμ.ne') (by simpa only [line_im] using hμ.ne') g g
        (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (4*‖-3*(vacuumJetCoefficient : ℂ)‖^2)*(Real.pi/μ)*‖(g : H)‖^2
  have hC : 0 ≤ C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := fixed_endpoint_tail (coreEquiv.symm g) C hC ε hε
  refine ⟨N,fun m hm ell hell F => (actual_diagonal_fixed_energy m ell F μ hμ g).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have h := hN m hm ell hell
  dsimp [C] at h
  nlinarith only [h]

/-- The remaining signed word retains both raised defects, the full frequency contribution and the original IMS correction. -/
theorem actual_diagonal_remainder_normal (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    dynamicRemainder sharp m ell F z z hz hz g g=
      fixedBulk F z z hz hz g g (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)+
      defectBulk F z z hz hz g g (inverseVolumeAction*theta m ell) (inverseVolumeAction*theta m ell)-
      (3*(vacuumJetCoefficient : ℂ)*(star z+z))*sourcePair (theta m ell (state F z hz g))
        (inverseVolumeAction (theta m ell (state F z hz g)))-
      inverseContact m ell (state F z hz g) (state F z hz g) := by
  have h := actual_dynamic_exchange sharp m ell F z z hz hz g g
  rw [actual_inverse_bulk_normal] at h
  linear_combination h

end LowEnergy.SourceInverseDiagonalEndpoint
