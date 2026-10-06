import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceActualResolventEnergy
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderBounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiZeroOrderTimeTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment SourceInverseSourceLeg
open SourceClockPhiRadiusSourceCurrent SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceClockPhiZeroOrderProfile SourceClockPhiZeroOrderBounded SourceBoundedClockAbel SourcePhysicalKineticSquare
open MeasureTheory Filter SourceClockPhiRadiusResponsePositiveSource SourceClockRadiusAffineCutoff
attribute [local irreducible] finiteResolvent resolventCore state
open scoped InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
def sourceState (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) : QuantumTest :=
  resolventCore F z hz (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i))
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im ≠ 0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem input_embed (g : diagonal.domain) (i : Fin 2) :
    embed (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i))=
      (SourceClockPhiNativeJointPayment.inputSeed g i:H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem retarded_mass (F : Index) (μ : ℝ) (hμ : 0 < μ) (x : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (SourceResolventBandLimit.line μ w) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
  simpa only [SourceResolventBandLimit.line,mul_comm (μ:ℂ) Complex.I] using
    SourceActualResolventEnergy.actual_square_lintegral F μ hμ x
private theorem causal_mass (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ) (x : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (actualFrequency advanced μ w) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
  cases advanced
  · simpa only [actualFrequency,Bool.false_eq_true,ite_false] using retarded_mass F μ hμ x
  · simp only [actualFrequency,ite_true]
    have he (w : ℝ) : ‖finiteResolvent F (star (SourceResolventBandLimit.line μ w)) x‖=
        ‖finiteResolvent F (SourceResolventBandLimit.line μ w) x‖ :=
      actual_conjugate_leg_norm F _ (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') x
    simp_rw [he]
    exact retarded_mass F μ hμ x

theorem actual_two_seed_frequency_mass (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0 < μ)
    (g : diagonal.domain) :
    (∫⁻ w : ℝ,ENNReal.ofReal (∑i : Fin 2,‖embed (sourceState i F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)‖^2))=
      ENNReal.ofReal (Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)) := by
  have he (i : Fin 2) (w : ℝ) : embed (sourceState i F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)=finiteResolvent F (actualFrequency advanced μ w)
        (SourceClockPhiNativeJointPayment.inputSeed g i:H) := by
    rw [sourceState,resolvent_embed,input_embed]
  simp_rw [he]
  have hm (x : H) : Measurable (fun w : ℝ=>ENNReal.ofReal (‖finiteResolvent F
      (actualFrequency advanced μ w) x‖^2)) := by
    have hR : Continuous (fun w : ℝ=>finiteResolvent F (SourceResolventBandLimit.line μ w) x) :=
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F).clm_apply continuous_const
    have hr : Measurable (fun w : ℝ=>ENNReal.ofReal (‖finiteResolvent F (SourceResolventBandLimit.line μ w) x‖^2)) := by
      simpa only [Pi.pow_apply] using (hR.norm.pow 2).measurable.ennreal_ofReal
    cases advanced
    · simpa only [actualFrequency,Bool.false_eq_true,ite_false] using hr
    · have he (w : ℝ) : ‖finiteResolvent F (actualFrequency true μ w) x‖=
          ‖finiteResolvent F (SourceResolventBandLimit.line μ w) x‖ :=
        actual_conjugate_leg_norm F _ (by simpa only [SourceResolventBandLimit.line_im] using hμ.ne') x
      simp_rw [he]
      exact hr
  simp only [Fin.sum_univ_two,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  rw [lintegral_add_right _ (hm (SourceClockPhiNativeJointPayment.inputSeed g 1:H)),
    causal_mass advanced F μ hμ _,causal_mass advanced F μ hμ _]
  change ENNReal.ofReal (Real.pi/μ*‖(g:H)‖^2)+
    ENNReal.ofReal (Real.pi/μ*‖(phiRadiusSource g:H)‖^2)=_
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

private abbrev n : ℝ := sourceTime 0
private theorem lapse_pos : 0 < n := by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def chiZeroWord (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) : ℝ :=
  (n*μ/2)*(∑i : Fin 2,∑j : Fin 2,sourcePair
    ((clockCore*clockCore) (sourceState i F z hz g))
    (inverseVolumeAction (zeroProfile i j m ell (sourceState j F z hz g)))).re

private theorem clock_pair (f g : QuantumTest) : sourcePair (clockCore f) g=sourcePair f (clockCore g) :=
  (multiply_pair _ _ _ _).symm
private theorem clock_square_pair (f g : QuantumTest) :
    sourcePair ((clockCore*clockCore) f) g=sourcePair f ((clockCore*clockCore) g) := by
  change sourcePair (clockCore (clockCore f)) g=sourcePair f (clockCore (clockCore g))
  rw [clock_pair,clock_pair]
private theorem weighted_pair (i j : Fin 2) (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell)
    (f g : QuantumTest) :
    sourcePair ((clockCore*clockCore) f) (inverseVolumeAction (zeroProfile i j m ell g))=
      inner ℂ (embed f) (weightedZero i j m ell hm hml (embed g)) := by
  rw [clock_square_pair,actual_weighted_zero_core]
  rfl
private theorem entry_price (i j : Fin 2) (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell)
    (f g : QuantumTest) :
    ‖sourcePair ((clockCore*clockCore) f) (inverseVolumeAction (zeroProfile i j m ell g))‖ ≤
      (176/(m+2:ℝ))*(‖embed f‖*‖embed g‖) := by
  rw [weighted_pair i j m ell hm hml]
  have hb : ‖weightedZero i j m ell hm hml (embed g)‖ ≤ (176/(m+2:ℝ))*‖embed g‖ :=
    ((weightedZero i j m ell hm hml).le_opNorm (embed g)).trans
      (mul_le_mul_of_nonneg_right (actual_weighted_zero_norm i j m ell hm hml) (norm_nonneg _))
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring))

theorem actual_chi_zero_point_price (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell)
    (μ : ℝ) (hμ : 0 < μ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    |chiZeroWord m ell μ F z hz g| ≤
      (176*n*μ/(m+2:ℝ))*(∑i : Fin 2,‖embed (sourceState i F z hz g)‖^2) := by
  let X : Fin 2→QuantumTest := fun i=>sourceState i F z hz g
  have hc : 0≤n*μ/2 := by have hn:=lapse_pos;positivity
  have hs : |(∑i : Fin 2,∑j : Fin 2,sourcePair ((clockCore*clockCore) (X i))
      (inverseVolumeAction (zeroProfile i j m ell (X j)))).re| ≤
      (176/(m+2:ℝ))*(2*∑i : Fin 2,‖embed (X i)‖^2) := by
    have hnorm : |(∑i : Fin 2,∑j : Fin 2,sourcePair ((clockCore*clockCore) (X i))
        (inverseVolumeAction (zeroProfile i j m ell (X j)))).re| ≤
        ∑i : Fin 2,∑j : Fin 2,(176/(m+2:ℝ))*(‖embed (X i)‖*‖embed (X j)‖) := (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun i _=>(norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _=>entry_price i j m ell hm hml (X i) (X j))))))
    have hy (x y : ℝ) : x*y≤(x^2+y^2)/2 := by nlinarith only [sq_nonneg (x-y)]
    have hys := Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>
      Finset.sum_le_sum (s:=Finset.univ) (fun j (_:j∈(Finset.univ:Finset (Fin 2)))=>
        mul_le_mul_of_nonneg_left (hy ‖embed (X i)‖ ‖embed (X j)‖)
          (by positivity : (0:ℝ)≤176/(m+2:ℝ))))
    refine hnorm.trans (hys.trans_eq ?_)
    simp only [Fin.sum_univ_two]
    ring
  unfold chiZeroWord
  rw [abs_mul,abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left hs hc).trans_eq (by dsimp only [X];ring)

theorem actual_chi_zero_allF_budget (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell)
    (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) (F : Index) :
    (∫⁻ w : ℝ,ENNReal.ofReal (|chiZeroWord m ell μ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g|)) ≤
      ENNReal.ofReal (176*n*Real.pi/(m+2:ℝ)*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)) := by
  let c : ℝ := 176*n*μ/(m+2:ℝ)
  have hc : 0≤c := by have hn:=lapse_pos;dsimp [c];positivity
  have hp (w : ℝ) : ENNReal.ofReal (|chiZeroWord m ell μ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g|) ≤
      ENNReal.ofReal c*ENNReal.ofReal (∑i : Fin 2,‖embed (sourceState i F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)‖^2) := by
    rw [←ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal (actual_chi_zero_point_price m ell hm hml μ hμ F _ _ g)
  calc _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal c*ENNReal.ofReal (∑i : Fin 2,‖embed (sourceState i F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)‖^2) := lintegral_mono hp
       _ = ENNReal.ofReal c*ENNReal.ofReal (Real.pi/μ*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)) := by
         rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,actual_two_seed_frequency_mass advanced F μ hμ g]
       _ = _ := by
         rw [←ENNReal.ofReal_mul hc]
         congr 1
         dsimp only [c]
         field_simp

theorem actual_chi_zero_common_tail (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m : ℕ,N ≤ m → ∀ ell : ℕ,m ≤ ell →
      ∀ F : Index,∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (|chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := 176*n*Real.pi*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨max N 1,fun m hm ell hml F advanced=>?_⟩
  have hm1 : 1 ≤ m := (le_max_right N 1).trans hm
  have hNm : (N:ℝ) ≤ m := by exact_mod_cast (le_max_left N 1).trans hm
  have hd : 0 < (m+2:ℝ) := by positivity
  have hlarge : C/ε < (m+2:ℝ) := by linarith only [hN,hNm]
  have hsmall : C/(m+2:ℝ) ≤ ε := by
    apply (div_le_iff₀ hd).mpr
    exact ((div_lt_iff₀ hε).mp hlarge).le.trans_eq (mul_comm _ _)
  have hp := actual_chi_zero_allF_budget m ell hm1 hml advanced μ hμ g F
  have he : 176*n*Real.pi/(m+2:ℝ)*(‖(g:H)‖^2+‖(phiRadiusSource g:H)‖^2)=C/(m+2:ℝ) := by dsimp only [C];ring
  rw [he] at hp
  exact hp.trans (ENNReal.ofReal_le_ofReal hsmall)

end LowEnergy.SourceClockPhiZeroOrderTimeTail
