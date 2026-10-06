import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelWholePhiZeroOrder
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderTimeTail
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderBounded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAbelNativeCurrentZeroTail
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy GaussNativePotential SourceScalarPairedTransport SourceScalarDoubleCurrent
open SourceClockPhiZeroOrderProfile SourceBoundedClockAbel SourcePhysicalKineticSquare SourceClockPhiZeroOrderBounded
open SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceLocalizedInverseFormPayment FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] finiteResolvent resolventCore state
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev X (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) : QuantumTest :=
  SourceClockPhiZeroOrderTimeTail.sourceState i F z hz g
private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (actualFrequency advanced μ w).im ≠ 0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star (F : Index) (z : ℂ) : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (F : Index) :
    Continuous (fun w : ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true]
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have he : (fun w : ℝ=>finiteResolvent F (star (line μ w)))=
        (fun w : ℝ=>(finiteResolvent F (line μ w)).adjoint) := funext (fun w=>finite_star F (line μ w))
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))
private theorem X_embed (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    embed (X i F z hz g)=finiteResolvent F z (SourceClockPhiNativeJointPayment.inputSeed g i:H) := by
  have hr (f : QuantumTest) : embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
    unfold resolventCore state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  unfold X SourceClockPhiZeroOrderTimeTail.sourceState
  rw [hr]
  congr 1
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem clock_pair (f g : QuantumTest) : sourcePair (clockCore f) g=sourcePair f (clockCore g) :=
  (multiply_pair _ _ _ _).symm
private theorem chi_entry (i j : Fin 2) (m ell : ℕ) (hm : 1 ≤ m) (hml : m ≤ ell) (f g : QuantumTest) :
    sourcePair ((clockCore*clockCore) f) (U (zeroProfile i j m ell g))=
      inner ℂ (embed f) (weightedZero i j m ell hm hml (embed g)) := by
  rw [actual_weighted_zero_core]
  change sourcePair (clockCore (clockCore f)) (U (zeroProfile i j m ell g))=
    sourcePair f (clockCore (clockCore (U (zeroProfile i j m ell g))))
  rw [clock_pair,clock_pair]
/-- The original same-F Abel current and the entire original UZ matrix remain together. -/
def currentZeroWord (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im ≠ 0)
    (g : diagonal.domain) : ℝ :=
  (n/8)*(∑i : Fin 2,∑j : Fin 2,sourcePair
    (BoundedClockNativeCore.currentCore μ F (X i F z hz g))
    (U (zeroProfile i j m ell (X j F z hz g)))).im

theorem actual_zero_current_source (μ : ℝ) (hμ : 0 < μ) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    SourceClockAbelWholePhiZeroOrder.zeroWord m ell μ F z hz g=
      currentZeroWord m ell μ F z hz g+
        SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F z hz g := by
  have h := congrArg (fun T : H →L[ℂ] H=>∑i : Fin 2,∑j : Fin 2,inner ℂ
    (T (embed (X i F z hz g))) (embed (U (zeroProfile i j m ell (X j F z hz g)))))
    (actual_bounded_clock_abel_source μ hμ F).2.2.2.1
  simp only [smul_apply,sub_apply,
    ←BoundedClockNativeCore.currentCore_embed μ hμ F,
    ←BoundedClockNativeCore.abelCore_embed μ hμ F,
    (actual_bounded_clock_abel_source μ hμ F).1] at h
  have hr := congrArg Complex.re h
  simp only [inner_smul_left,inner_sub_left,Complex.conj_I,map_mul,map_ofNat,Complex.conj_ofReal,
    Finset.sum_sub_distrib,←Finset.mul_sum,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,Complex.mul_im,zero_mul,mul_zero,neg_zero,zero_sub,sub_zero,Complex.sub_re] at hr
  change (n*μ/2)*(∑i : Fin 2,∑j : Fin 2,sourcePair
    (BoundedClockNativeCore.abelCore μ F (X i F z hz g))
    (U (zeroProfile i j m ell (X j F z hz g)))).re=
    (n/8)*(∑i : Fin 2,∑j : Fin 2,sourcePair
      (BoundedClockNativeCore.currentCore μ F (X i F z hz g))
      (U (zeroProfile i j m ell (X j F z hz g)))).im+
    (n*μ/2)*(∑i : Fin 2,∑j : Fin 2,sourcePair
      ((clockCore*clockCore) (X i F z hz g))
      (U (zeroProfile i j m ell (X j F z hz g)))).re
  simp only [zero_add, zero_mul, sub_zero] at hr
  simp only [sourcePair]
  have hr' : (∑i : Fin 2,∑j : Fin 2,inner ℂ
    (embed (BoundedClockNativeCore.currentCore μ F (X i F z hz g)))
    (embed (U (zeroProfile i j m ell (X j F z hz g))))).im=
    4*μ*((∑i : Fin 2,∑j : Fin 2,inner ℂ
      (embed (BoundedClockNativeCore.abelCore μ F (X i F z hz g)))
      (embed (U (zeroProfile i j m ell (X j F z hz g))))).re-
      (∑i : Fin 2,∑j : Fin 2,inner ℂ
        (embed ((clockCore*clockCore) (X i F z hz g)))
        (embed (U (zeroProfile i j m ell (X j F z hz g))))).re) := by
    simp only [Module.End.mul_apply]
    convert hr using 1; ring
  linear_combination (norm:=ring) -(n/8)*hr'

/-- The source chi error is internally paid; only the actual J/U/Z zero word remains
inside the same native positive part and literal original second-pressure debit. -/
theorem actual_native_current_zero_common_payment (μ : ℝ) (hμ : 0 < μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0 < η) :
    ∀ ε : ℝ,0 < ε → ∃ N : ℕ,∀ m : ℕ,N ≤ m → ∀ ell : ℕ,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀ advanced : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F
          (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
        currentZeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := SourceClockAbelWholePhiZeroOrder.actual_native_zero_common_payment μ hμ g η hη (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := SourceClockPhiZeroOrderTimeTail.actual_chi_zero_common_tail μ hμ g (ε/2) (by positivity)
  refine ⟨max N₀ (max N₁ 1),fun m hm ell hml=>?_⟩
  have hm1 : 1 ≤ m := (le_trans (le_max_right N₁ 1) (le_max_right N₀ (max N₁ 1))).trans hm
  have hm₁ : N₁ ≤ m := (le_trans (le_max_left N₁ 1) (le_max_right N₀ (max N₁ 1))).trans hm
  filter_upwards [h₀ m (le_trans (le_max_left N₀ (max N₁ 1)) hm) ell hml] with F hA
  intro advanced
  let price : ℝ→ℝ := fun w=>|SourceClockAbelNativeCurvature.nativePi m ell μ F
    (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
    SourceClockAbelWholePhiZeroOrder.zeroWord m ell μ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g|-
    η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g
  have hp (w : ℝ) : ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
      currentZeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
      η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g) ≤
      ENNReal.ofReal (|SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|)+ENNReal.ofReal (price w) := by
    have he := actual_zero_current_source μ hμ m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g
    have ht := abs_add_le (SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g+
      SourceClockAbelWholePhiZeroOrder.zeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)
      (-SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)
    rw [he] at ht
    simp only [abs_neg] at ht
    have hcancel : SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
        (currentZeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
        SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)+
        -SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g=
      SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
        currentZeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g := by ring
    rw [hcancel] at ht
    have hb : |SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+
        currentZeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g ≤
      |SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|+price w := by
      change _ ≤ |SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|+
        (|SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+
          SourceClockAbelWholePhiZeroOrder.zeroWord m ell μ F (actualFrequency advanced μ w)
            (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)
      rw [he]
      linarith only [ht]
    exact (ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_add_le
  have hmχ : Measurable (fun w : ℝ=>ENNReal.ofReal (|SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|)) := by
    have he (w : ℝ) : SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g=
      (n*μ/2)*(∑i : Fin 2,∑j : Fin 2,inner ℂ
        (finiteResolvent F (actualFrequency advanced μ w) (SourceClockPhiNativeJointPayment.inputSeed g i:H))
        (weightedZero i j m ell hm1 hml
          (finiteResolvent F (actualFrequency advanced μ w) (SourceClockPhiNativeJointPayment.inputSeed g j:H)))).re := by
      unfold SourceClockPhiZeroOrderTimeTail.chiZeroWord
      change (n*μ/2)*(∑i : Fin 2,∑j : Fin 2,sourcePair ((clockCore*clockCore) (X i F _ _ g))
        (U (zeroProfile i j m ell (X j F _ _ g)))).re=_
      simp_rw [chi_entry _ _ m ell hm1 hml,X_embed]
    simp_rw [he]
    have hi (i j : Fin 2) : Continuous (fun w : ℝ=>inner ℂ
        (finiteResolvent F (actualFrequency advanced μ w) (SourceClockPhiNativeJointPayment.inputSeed g i:H))
        (weightedZero i j m ell hm1 hml (finiteResolvent F (actualFrequency advanced μ w)
          (SourceClockPhiNativeJointPayment.inputSeed g j:H)))) :=
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const).inner
        ((weightedZero i j m ell hm1 hml).continuous.comp
          ((frequency_continuous advanced μ hμ F).clm_apply continuous_const))
    have hc := continuous_finsetSum Finset.univ (fun i _=>continuous_finsetSum Finset.univ
      (fun j _=>hi i j))
    exact (((Complex.continuous_re.comp hc).const_mul _).abs.measurable.ennreal_ofReal)
  calc _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (|SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|)+ENNReal.ofReal (price w) := lintegral_mono hp
       _ = (∫⁻ w : ℝ,ENNReal.ofReal (|SourceClockPhiZeroOrderTimeTail.chiZeroWord m ell μ F
        (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|))+
        (∫⁻ w : ℝ,ENNReal.ofReal (price w)) := lintegral_add_left hmχ _
       _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add
          (h₁ m hm₁ ell hml F advanced) (hA advanced)
       _ = _ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring

end LowEnergy.SourceClockAbelNativeCurrentZeroTail
