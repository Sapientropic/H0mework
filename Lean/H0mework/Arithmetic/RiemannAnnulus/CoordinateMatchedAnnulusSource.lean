import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import H0mework.Arithmetic.Muntz.CoPoissonMuntzFactorization
import H0mework.Arithmetic.BurnolPhysical.ConcreteAnnulusCoPoisson
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusAdditiveFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ContDiff SchwartzMap

noncomputable section

def burnolCoordinateMellinWeight (coordinate : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (coordinate - 1)

/-- Every Mellin coordinate generates a smooth compact annulus source whose
coordinate read is nonzero.  The source is obtained from the local separation
of the nonvanishing Mellin weight, not supplied by the caller. -/
theorem exists_smooth_annulus_mellin_test
    (coordinate : ℂ) :
    ∃ test : ℝ → ℝ,
      ContDiff ℝ ∞ test ∧
      HasCompactSupport test ∧
      tsupport test ⊆ Ioo (1 : ℝ) 3 ∧
      (∫ t : ℝ, test t • burnolCoordinateMellinWeight coordinate t) ≠ 0 := by
  by_contra noTest
  push Not at noTest
  have weightLocallyIntegrable : LocallyIntegrableOn
      (burnolCoordinateMellinWeight coordinate)
      (Ioo (1 : ℝ) 3) volume := by
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioo
    exact continuousOn_of_forall_continuousAt fun t membership =>
      Complex.continuousAt_ofReal_cpow_const t (coordinate - 1)
        (Or.inr (ne_of_gt (by linarith [membership.1] : 0 < t)))
  have weightZero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    weightLocallyIntegrable (fun test smooth compact supported =>
      noTest test smooth compact supported)
  have intervalMeasure :
      (volume : Measure ℝ) (Ioo (1 : ℝ) 3) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  have weightZeroRestricted : ∀ᵐ t ∂(volume : Measure ℝ).restrict
      (Ioo (1 : ℝ) 3),
      burnolCoordinateMellinWeight coordinate t = 0 := by
    filter_upwards [ae_restrict_of_ae weightZero,
      ae_restrict_mem measurableSet_Ioo] with t zeroRead membership
    exact zeroRead membership
  obtain ⟨t, membership, zeroRead⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      intervalMeasure weightZeroRestricted
  exact (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (by linarith [membership.1] : 0 < t))))) zeroRead

/-- The same annulus can be chosen with both the target Mellin read and its
ordinary integral nonzero.  The second condition makes the large-scale
co-Poisson tail an actual nonzero energy witness. -/
theorem exists_smooth_annulus_joint_mellin_integral_test
    (coordinate : ℂ) :
    ∃ test : ℝ → ℝ,
      ContDiff ℝ ∞ test ∧
      HasCompactSupport test ∧
      tsupport test ⊆ Ioo (1 : ℝ) 3 ∧
      (∫ t : ℝ, test t • burnolCoordinateMellinWeight coordinate t) ≠ 0 ∧
      (∫ t : ℝ, test t) ≠ 0 := by
  obtain ⟨f, fSmooth, fCompact, fSupport, fMellin⟩ :=
    exists_smooth_annulus_mellin_test coordinate
  obtain ⟨g, gSmooth, gCompact, gSupport, gMellinOne⟩ :=
    exists_smooth_annulus_mellin_test (1 : ℂ)
  have gIntegral : (∫ t : ℝ, g t) ≠ 0 := by
    have complexNonzero : (∫ t : ℝ, (g t : ℂ)) ≠ 0 := by
      simpa [burnolCoordinateMellinWeight] using gMellinOne
    intro realZero
    apply complexNonzero
    calc
      (∫ t : ℝ, (g t : ℂ)) = Complex.ofReal (∫ t : ℝ, g t) :=
        integral_complex_ofReal
      _ = 0 := by rw [realZero]; rfl
  have fIntegrable : Integrable f :=
    fSmooth.continuous.integrable_of_hasCompactSupport fCompact
  have gIntegrable : Integrable g :=
    gSmooth.continuous.integrable_of_hasCompactSupport gCompact
  let fw : ℝ → ℂ := fun t =>
    f t • burnolCoordinateMellinWeight coordinate t
  let gw : ℝ → ℂ := fun t =>
    g t • burnolCoordinateMellinWeight coordinate t
  have fwIntegrable : Integrable fw := by
    by_contra notIntegrable
    rw [integral_undef notIntegrable] at fMellin
    exact fMellin rfl
  have gwIntegrable : Integrable gw := by
    have supportSubset : Function.support gw ⊆ Icc (1 : ℝ) 3 := by
      intro t membership
      have gNonzero : g t ≠ 0 := by
        intro gZero
        exact membership (by simp [gw, gZero])
      have inside := gSupport (subset_tsupport g gNonzero)
      exact ⟨inside.1.le, inside.2.le⟩
    have continuousOn : ContinuousOn gw (Icc (1 : ℝ) 3) := by
      intro t membership
      apply ContinuousAt.continuousWithinAt
      dsimp [gw, burnolCoordinateMellinWeight]
      apply ContinuousAt.smul gSmooth.continuous.continuousAt
      exact Complex.continuousAt_ofReal_cpow_const t (coordinate - 1)
        (Or.inr (ne_of_gt
          (lt_of_lt_of_le (by norm_num) membership.1)))
    exact (integrableOn_iff_integrable_of_support_subset supportSubset).mp
      (continuousOn.integrableOn_compact isCompact_Icc)
  by_cases fIntegral : (∫ t : ℝ, f t) ≠ 0
  · exact ⟨f, fSmooth, fCompact, fSupport, fMellin, fIntegral⟩
  · let h : ℝ → ℝ := fun t => f t + g t
    push Not at fIntegral
    have hSmooth : ContDiff ℝ ∞ h := by
      dsimp [h]
      fun_prop
    have hCompact : HasCompactSupport h := fCompact.add gCompact
    have hSupport : tsupport h ⊆ Ioo (1 : ℝ) 3 := by
      exact (tsupport_add f g).trans (union_subset fSupport gSupport)
    have hIntegral : (∫ t : ℝ, h t) ≠ 0 := by
      dsimp [h]
      rw [integral_add fIntegrable gIntegrable, fIntegral, zero_add]
      simpa using gIntegral
    by_cases hMellin :
        (∫ t : ℝ, h t • burnolCoordinateMellinWeight coordinate t) ≠ 0
    · exact ⟨h, hSmooth, hCompact, hSupport, hMellin, hIntegral⟩
    · let k : ℝ → ℝ := fun t => f t + 2 * g t
      push Not at hMellin
      have kSmooth : ContDiff ℝ ∞ k := by
        dsimp [k]
        fun_prop
      have twiceCompact : HasCompactSupport (fun t : ℝ => 2 * g t) :=
        gCompact.mul_left
      have kCompact : HasCompactSupport k := fCompact.add twiceCompact
      have twiceSupport : tsupport (fun t : ℝ => 2 * g t) ⊆
          Ioo (1 : ℝ) 3 := by
        exact (tsupport_smul_subset_right (fun _ : ℝ => (2 : ℝ)) g).trans
          gSupport
      have kSupport : tsupport k ⊆ Ioo (1 : ℝ) 3 := by
        exact (tsupport_add f (fun t => 2 * g t)).trans
          (union_subset fSupport twiceSupport)
      have kIntegral : (∫ t : ℝ, k t) ≠ 0 := by
        dsimp [k]
        rw [integral_add fIntegrable (gIntegrable.const_mul 2),
          integral_const_mul, fIntegral, zero_add]
        exact mul_ne_zero (by norm_num) gIntegral
      have hMellinEq : (∫ t : ℝ, fw t) + ∫ t : ℝ, gw t = 0 := by
        rw [← hMellin]
        rw [← integral_add fwIntegrable gwIntegrable]
        apply integral_congr_ae
        filter_upwards with t
        simp only [fw, gw, h, real_smul]
        push_cast
        ring
      have kMellin :
          (∫ t : ℝ, k t • burnolCoordinateMellinWeight coordinate t) ≠ 0 := by
        have targetEq :
            (∫ t : ℝ, k t • burnolCoordinateMellinWeight coordinate t) =
              ∫ t : ℝ, gw t := by
          calc
            _ = (∫ t : ℝ, fw t) + 2 * ∫ t : ℝ, gw t := by
              rw [← integral_const_mul]
              rw [← integral_add fwIntegrable (gwIntegrable.const_mul 2)]
              apply integral_congr_ae
              filter_upwards with t
              simp only [fw, gw, k, real_smul]
              push_cast
              ring
            _ = _ := by linear_combination hMellinEq
        rw [targetEq]
        intro gwZero
        have fwZero : (∫ t : ℝ, fw t) = 0 := by
          rw [gwZero, add_zero] at hMellinEq
          exact hMellinEq
        exact fMellin fwZero
      exact ⟨k, kSmooth, kCompact, kSupport, kMellin, kIntegral⟩

def burnolCoordinateMatchedRealTest (coordinate : ℂ) : ℝ → ℝ :=
  Classical.choose (exists_smooth_annulus_joint_mellin_integral_test coordinate)

theorem burnolCoordinateMatchedRealTest_spec (coordinate : ℂ) :
    ContDiff ℝ ∞ (burnolCoordinateMatchedRealTest coordinate) ∧
      HasCompactSupport (burnolCoordinateMatchedRealTest coordinate) ∧
      tsupport (burnolCoordinateMatchedRealTest coordinate) ⊆
        Ioo (1 : ℝ) 3 ∧
      (∫ t : ℝ, burnolCoordinateMatchedRealTest coordinate t •
        burnolCoordinateMellinWeight coordinate t) ≠ 0 ∧
      (∫ t : ℝ, burnolCoordinateMatchedRealTest coordinate t) ≠ 0 :=
  Classical.choose_spec
    (exists_smooth_annulus_joint_mellin_integral_test coordinate)

theorem burnolCoordinateMatchedRealTest_eq_zero_of_not_mem
    (coordinate : ℂ) {t : ℝ}
    (outside : t ∉ Ioo (1 : ℝ) 3) :
    burnolCoordinateMatchedRealTest coordinate t = 0 := by
  by_contra nonzero
  exact outside ((burnolCoordinateMatchedRealTest_spec coordinate).2.2.1
    (subset_tsupport _ nonzero))

def burnolCoordinateMatchedEvenRaw (coordinate : ℂ) (t : ℝ) : ℂ :=
  ((burnolCoordinateMatchedRealTest coordinate t +
      burnolCoordinateMatchedRealTest coordinate (-t) : ℝ) : ℂ)

theorem burnolCoordinateMatchedEvenRaw_contDiff (coordinate : ℂ) :
    ContDiff ℝ ∞ (burnolCoordinateMatchedEvenRaw coordinate) := by
  have sourceSmooth := (burnolCoordinateMatchedRealTest_spec coordinate).1
  have realSmooth : ContDiff ℝ ∞ (fun t : ℝ =>
      burnolCoordinateMatchedRealTest coordinate t +
        burnolCoordinateMatchedRealTest coordinate (-t)) := by
    fun_prop
  unfold burnolCoordinateMatchedEvenRaw
  exact Complex.ofRealCLM.contDiff.comp realSmooth

theorem burnolCoordinateMatchedEvenRaw_hasCompactSupport (coordinate : ℂ) :
    HasCompactSupport (burnolCoordinateMatchedEvenRaw coordinate) := by
  have sourceCompact := (burnolCoordinateMatchedRealTest_spec coordinate).2.1
  have reflectedCompact : HasCompactSupport
      (fun t : ℝ => burnolCoordinateMatchedRealTest coordinate (-t)) := by
    change HasCompactSupport
      (burnolCoordinateMatchedRealTest coordinate ∘ (Homeomorph.neg ℝ))
    exact sourceCompact.comp_homeomorph (Homeomorph.neg ℝ)
  have realCompact : HasCompactSupport (fun t : ℝ =>
      burnolCoordinateMatchedRealTest coordinate t +
        burnolCoordinateMatchedRealTest coordinate (-t)) :=
    sourceCompact.add reflectedCompact
  exact realCompact.comp_left rfl

def burnolCoordinateMatchedAnnulusSchwartz (coordinate : ℂ) :
    SchwartzMap ℝ ℂ :=
  (burnolCoordinateMatchedEvenRaw_hasCompactSupport coordinate).toSchwartzMap
    (burnolCoordinateMatchedEvenRaw_contDiff coordinate)

@[simp] theorem burnolCoordinateMatchedAnnulusSchwartz_apply
    (coordinate : ℂ) (t : ℝ) :
    burnolCoordinateMatchedAnnulusSchwartz coordinate t =
      burnolCoordinateMatchedEvenRaw coordinate t := by
  rfl

/-- The coordinate-matched source is an actual Burnol compact-annulus source:
it is even and vanishes on both required gaps. -/
def burnolCoordinateMatchedAnnulusSource (coordinate : ℂ) :
    burnolCompactAnnulusSource :=
  ⟨burnolCoordinateMatchedAnnulusSchwartz coordinate, by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      simp [burnolCoordinateMatchedEvenRaw, add_comm]
    · intro t inside
      have outside (u : ℝ) (bound : |u| ≤ (1 / 4 : ℝ)) :
          u ∉ Ioo (1 : ℝ) 3 := by
        intro membership
        have large : 1 < |u| := membership.1.trans_le (le_abs_self u)
        linarith
      rw [burnolCoordinateMatchedAnnulusSchwartz_apply]
      simp only [burnolCoordinateMatchedEvenRaw]
      rw [burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
          (outside t inside),
        burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
          (outside (-t) (by simpa using inside))]
      simp
    · intro t outsideBound
      have outside (u : ℝ) (bound : (4 : ℝ) ≤ |u|) :
          u ∉ Ioo (1 : ℝ) 3 := by
        intro membership
        have upper : |u| < 3 := by
          rcases le_total u 0 with nonpositive | nonnegative
          · rw [abs_of_nonpos nonpositive]
            linarith [membership.1, membership.2]
          · rw [abs_of_nonneg nonnegative]
            exact membership.2
        linarith
      rw [burnolCoordinateMatchedAnnulusSchwartz_apply]
      simp only [burnolCoordinateMatchedEvenRaw]
      rw [burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
          (outside t outsideBound),
        burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
          (outside (-t) (by simpa using outsideBound))]
      simp⟩

theorem burnolCoordinateMatchedAnnulusSchwartz_integral_eq
    (coordinate : ℂ) :
    (∫ x : ℝ, burnolCoordinateMatchedAnnulusSchwartz coordinate x) =
      (2 : ℂ) * Complex.ofReal
        (∫ x : ℝ, burnolCoordinateMatchedRealTest coordinate x) := by
  let test := burnolCoordinateMatchedRealTest coordinate
  have testIntegrable : Integrable test :=
    (burnolCoordinateMatchedRealTest_spec coordinate).1.continuous
      |>.integrable_of_hasCompactSupport
        (burnolCoordinateMatchedRealTest_spec coordinate).2.1
  have reflectedIntegrable : Integrable (fun x : ℝ => test (-x)) := by
    have reflectedCompact : HasCompactSupport (fun x : ℝ => test (-x)) := by
      change HasCompactSupport (test ∘ Homeomorph.neg ℝ)
      exact (burnolCoordinateMatchedRealTest_spec coordinate).2.1.comp_homeomorph
        (Homeomorph.neg ℝ)
    have reflectedContinuous : Continuous (fun x : ℝ => test (-x)) := by
      exact (burnolCoordinateMatchedRealTest_spec coordinate).1.continuous.comp
        continuous_neg
    exact reflectedContinuous.integrable_of_hasCompactSupport reflectedCompact
  have reflectedIntegral : (∫ x : ℝ, test (-x)) = ∫ x : ℝ, test x :=
    integral_neg_eq_self test volume
  calc
    (∫ x : ℝ, burnolCoordinateMatchedAnnulusSchwartz coordinate x) =
        ∫ x : ℝ, ((test x + test (-x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rfl
    _ = Complex.ofReal (∫ x : ℝ, test x + test (-x)) :=
      integral_complex_ofReal
    _ = Complex.ofReal
        ((∫ x : ℝ, test x) + ∫ x : ℝ, test (-x)) := by
      rw [integral_add testIntegrable reflectedIntegrable]
    _ = (2 : ℂ) * Complex.ofReal (∫ x : ℝ, test x) := by
      rw [reflectedIntegral]
      push_cast
      ring

theorem burnolCoordinateMatchedAnnulusSchwartz_integral_ne_zero
    (coordinate : ℂ) :
    (∫ x : ℝ, burnolCoordinateMatchedAnnulusSchwartz coordinate x) ≠ 0 := by
  rw [burnolCoordinateMatchedAnnulusSchwartz_integral_eq]
  exact mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr
      (burnolCoordinateMatchedRealTest_spec coordinate).2.2.2.2)

/-- The actual compact source has nonzero Mellin coupling at the coordinate
that generated it. -/
theorem burnolCoordinateMatchedAnnulusSource_mellin_ne_zero
    (coordinate : ℂ) :
    coPoissonMuntzEvenSourceMellin
        (burnolCoordinateMatchedAnnulusSource coordinate).1 coordinate ≠ 0 := by
  let test := burnolCoordinateMatchedRealTest coordinate
  let weighted : ℝ → ℂ := fun t =>
    test t • burnolCoordinateMellinWeight coordinate t
  have sourceNonzero : (∫ t : ℝ, weighted t) ≠ 0 :=
    (burnolCoordinateMatchedRealTest_spec coordinate).2.2.2.1
  have sourceIntegral :
      (∫ t : ℝ in Ioi 0, weighted t) = ∫ t : ℝ, weighted t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t outside
    have testZero : test t = 0 := by
      apply burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
      intro membership
      exact outside (by linarith [membership.1] : 0 < t)
    simp [weighted, testZero]
  have targetRead :
      coPoissonMuntzEvenSourceMellin
          (burnolCoordinateMatchedAnnulusSource coordinate).1 coordinate =
        (2 : ℂ) * ∫ t : ℝ, weighted t := by
    unfold coPoissonMuntzEvenSourceMellin mellin
    calc
      (∫ t : ℝ in Ioi 0,
          (t : ℂ) ^ (coordinate - 1) •
            coPoissonMuntzEvenSource
              (burnolCoordinateMatchedAnnulusSource coordinate).1 t) =
        ∫ t : ℝ in Ioi 0, (2 : ℂ) * weighted t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t positive
          have reflectedZero : test (-t) = 0 := by
            apply burnolCoordinateMatchedRealTest_eq_zero_of_not_mem coordinate
            intro membership
            have positive' : 0 < t := positive
            have negativePositive : 0 < -t := by linarith [membership.1]
            linarith
          change (t : ℂ) ^ (coordinate - 1) •
              (burnolCoordinateMatchedEvenRaw coordinate t +
                burnolCoordinateMatchedEvenRaw coordinate (-t)) = _
          simp only [burnolCoordinateMatchedEvenRaw, neg_neg]
          change (t : ℂ) ^ (coordinate - 1) *
              (((test t + test (-t) : ℝ) : ℂ) +
                ((test (-t) + test t : ℝ) : ℂ)) =
            (2 : ℂ) * (test t •
              burnolCoordinateMellinWeight coordinate t)
          rw [reflectedZero]
          simp only [add_zero, zero_add]
          unfold burnolCoordinateMellinWeight
          simp only [real_smul]
          ring
      _ = (2 : ℂ) * ∫ t : ℝ in Ioi 0, weighted t := by
        rw [integral_const_mul]
      _ = (2 : ℂ) * ∫ t : ℝ, weighted t := by rw [sourceIntegral]
  rw [targetRead]
  exact mul_ne_zero (by norm_num) sourceNonzero

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
