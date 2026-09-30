import H0mework.Versions.Y.Arithmetic.Mellin.PositiveMellinTate
import H0mework.Arithmetic.CoPoisson.MellinConvergence
import H0mework.Arithmetic.Tempered.RemainderReality

/-!
# Conjugate--Tate naturality of the actual Müntz relation

Pointwise conjugation followed by the actual weight-half Tate involution
sends the selected low chart at `z` to the source-generated high chart at
`1/2 - conj z`.  Mellin evaluation is conjugated, while the complete actual
co-Poisson--Müntz relation is transported by Fourier transform after Schwartz
conjugation.  This file does not identify the generated high chart with the
independent reversal-low chart and claims no quotient map, antiunitary,
Riesz-vector naturality, support, or radial cancellation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped SchwartzMap ENNReal

noncomputable section

def positiveMellinPointwiseConjugation :
    ClozelPositiveMellinFunction →ₛₗ[starRingEnd ℂ]
      ClozelPositiveMellinFunction where
  toFun f t := star (f t)
  map_add' left right := by
    funext t
    simp
  map_smul' scalar value := by
    funext t
    simp [smul_eq_mul]

@[simp] theorem positiveMellinPointwiseConjugation_apply
    (f : ClozelPositiveMellinFunction) (t : PositiveMellinReal) :
    positiveMellinPointwiseConjugation f t = star (f t) :=
  rfl

@[simp] theorem positiveMellinPointwiseConjugation_involutive
    (f : ClozelPositiveMellinFunction) :
    positiveMellinPointwiseConjugation
        (positiveMellinPointwiseConjugation f) = f := by
  funext t
  simp

theorem positiveMellinExtension_pointwiseConjugation
    (f : ClozelPositiveMellinFunction) (t : ℝ) :
    positiveMellinExtension (positiveMellinPointwiseConjugation f) t =
      star (positiveMellinExtension f t) := by
  by_cases positive : 0 < t
  · simp [positiveMellinExtension, positive]
  · simp [positiveMellinExtension, positive]

private theorem positiveReal_cpow_star
    (t : ℝ) (positive : 0 < t) (z : ℂ) :
    (t : ℂ) ^ (star z) = star ((t : ℂ) ^ z) := by
  have source := Complex.cpow_conj (t : ℂ) z (by
    rw [Complex.arg_ofReal_of_nonneg positive.le]
    exact Real.pi_ne_zero.symm)
  have realFixed : star (t : ℂ) = (t : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  change (t : ℂ) ^ star z = star (star (t : ℂ) ^ z) at source
  rw [realFixed] at source
  exact source

theorem mellinConvergent_pointwiseConjugation
    (f : ClozelPositiveMellinFunction) (z : ℂ)
    (convergent : MellinConvergent (positiveMellinExtension f) z) :
    MellinConvergent
      (positiveMellinExtension (positiveMellinPointwiseConjugation f))
      (star z) := by
  unfold MellinConvergent at convergent ⊢
  have conjugated : IntegrableOn
      (fun t : ℝ => star
        ((t : ℂ) ^ (z - 1) • positiveMellinExtension f t))
      (Ioi 0) :=
    Complex.conjCLE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      convergent
  apply conjugated.congr_fun
  · intro t positive
    simp only [smul_eq_mul, star_mul]
    rw [positiveMellinExtension_pointwiseConjugation]
    rw [show star z - 1 = star (z - 1) by simp]
    rw [positiveReal_cpow_star t positive (z - 1)]
    ring
  · exact measurableSet_Ioi

theorem mellin_pointwiseConjugation
    (f : ClozelPositiveMellinFunction) (z : ℂ) :
    mellin
        (positiveMellinExtension (positiveMellinPointwiseConjugation f))
        (star z) =
      star (mellin (positiveMellinExtension f) z) := by
  unfold mellin
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (star z - 1) •
          positiveMellinExtension
            (positiveMellinPointwiseConjugation f) t) =
        ∫ t : ℝ in Ioi 0,
          star ((t : ℂ) ^ (z - 1) •
            positiveMellinExtension f t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t positive
      simp only [smul_eq_mul, star_mul]
      rw [positiveMellinExtension_pointwiseConjugation]
      rw [show star z - 1 = star (z - 1) by simp]
      rw [positiveReal_cpow_star t positive (z - 1)]
      ring
    _ = star (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (z - 1) • positiveMellinExtension f t) := by
      exact integral_conj

def conjugateQuarterMellinTest (z : ℂ) :
    QuarterMellinL2Test z →ₛₗ[starRingEnd ℂ]
      QuarterMellinL2Test (star z) where
  toFun value :=
    ⟨positiveMellinPointwiseConjugation value.1,
      ⟨by
        have source := value.2.1.star
        change MemLp
          (positiveMellinLogQuarterTransform
            (positiveMellinPointwiseConjugation value.1))
          (2 : ℝ≥0∞) (volume : Measure ℝ)
        apply (memLp_congr_ae (ae_of_all _ fun x => ?_)).mpr source
        change (Real.exp (x / 4) : ℂ) * star (value.1 ⟨Real.exp x, Real.exp_pos x⟩) =
          star ((Real.exp (x / 4) : ℂ) *
            value.1 ⟨Real.exp x, Real.exp_pos x⟩)
        rw [star_mul, Complex.star_def, Complex.conj_ofReal]
        ring,
        mellinConvergent_pointwiseConjugation value.1 z value.2.2⟩⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add positiveMellinPointwiseConjugation left.1 right.1
  map_smul' scalar value := by
    apply Subtype.ext
    funext t
    simp [positiveMellinPointwiseConjugation, smul_eq_mul]

theorem quarterMellinL2Functional_conjugate
    (z : ℂ) (value : QuarterMellinL2Test z) :
    quarterMellinL2Functional (star z)
        (conjugateQuarterMellinTest z value) =
      star (quarterMellinL2Functional z value) := by
  exact mellin_pointwiseConjugation value.1 z

def conjugateQuarterMellinTateInput
    (z : ℂ) (value : QuarterMellinL2Test z) :
    positiveMellinConvergentSubmodule
      ((1 / 2 : ℂ) - ((1 / 2 : ℂ) - star z)) :=
  ⟨positiveMellinPointwiseConjugation value.1, by
    rw [show (1 / 2 : ℂ) - ((1 / 2 : ℂ) - star z) = star z by ring]
    exact (conjugateQuarterMellinTest z value).2.2⟩

def conjugateTateQuarterMellinTest (z : ℂ) :
    QuarterMellinL2Test z →ₛₗ[starRingEnd ℂ]
      QuarterMellinL2Test ((1 / 2 : ℂ) - star z) where
  toFun value :=
    ⟨positiveTateInvolution
        (positiveMellinPointwiseConjugation value.1),
      ⟨positiveTateInvolution_mem_quarterL2 _
          (conjugateQuarterMellinTest z value).2.1,
        (positiveMellinTateMap ((1 / 2 : ℂ) - star z)
          (conjugateQuarterMellinTateInput z value)).2⟩⟩
  map_add' left right := by
    apply Subtype.ext
    funext t
    simp only [positiveTateInvolution, positiveMellinPointwiseConjugation,
      LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Pi.add_apply,
      map_add]
  map_smul' scalar value := by
    apply Subtype.ext
    funext t
    simp only [positiveTateInvolution, positiveMellinPointwiseConjugation,
      LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, starRingEnd_apply]
    rw [star_mul]
    ring

theorem conjugateTateQuarterMellinTest_functional
    (z : ℂ) (value : QuarterMellinL2Test z) :
    quarterMellinL2Functional ((1 / 2 : ℂ) - star z)
        (conjugateTateQuarterMellinTest z value) =
      star (quarterMellinL2Functional z value) := by
  change positiveMellinFunctional ((1 / 2 : ℂ) - star z)
      (positiveMellinTateMap ((1 / 2 : ℂ) - star z)
        (conjugateQuarterMellinTateInput z value)) = _
  calc
    _ = positiveMellinFunctional
          ((1 / 2 : ℂ) - ((1 / 2 : ℂ) - star z))
          (conjugateQuarterMellinTateInput z value) :=
      positiveMellinFunctional_tateMap _ _
    _ = _ := by
      change mellin
          (positiveMellinExtension
            (positiveMellinPointwiseConjugation value.1))
          ((1 / 2 : ℂ) - ((1 / 2 : ℂ) - star z)) = _
      rw [show (1 / 2 : ℂ) - ((1 / 2 : ℂ) - star z) = star z by ring]
      exact mellin_pointwiseConjugation value.1 z

theorem scaledSchwartzTest_conjugation
    (scale : ℝ) (nonzero : scale ≠ 0) (test : SchwartzMap ℝ ℂ) :
    scaledSchwartzTest scale nonzero (schwartzConjugation test) =
      schwartzConjugation (scaledSchwartzTest scale nonzero test) := by
  ext x
  simp

theorem clozelTemperedRemainder_conjugation
    (test : SchwartzMap ℝ ℂ) :
    clozelTemperedRemainder (schwartzConjugation test) =
      star (clozelTemperedRemainder test) := by
  have fixed := congrArg
    (fun distribution : ComplexTempered =>
      distribution (schwartzConjugation test))
    clozelTemperedRemainder_isReal
  simpa only [IsReal, realConjugation_apply,
    schwartzConjugation_involutive] using fixed.symm

theorem coPoissonQuarterMellinMap_conjugation
    (test : SchwartzMap ℝ ℂ) :
    coPoissonQuarterMellinMap (schwartzConjugation test) =
      positiveMellinPointwiseConjugation
        (coPoissonQuarterMellinMap test) := by
  funext t
  change clozelTemperedRemainder
      (scaledSchwartzTest (Real.sqrt t.1)
        (Real.sqrt_pos.2 t.2).ne' (schwartzConjugation test)) =
    star (clozelTemperedRemainder
      (scaledSchwartzTest (Real.sqrt t.1)
        (Real.sqrt_pos.2 t.2).ne' test))
  rw [scaledSchwartzTest_conjugation,
    clozelTemperedRemainder_conjugation]

def schwartzTateConjugation :
    SchwartzMap ℝ ℂ →ₛₗ[starRingEnd ℂ] SchwartzMap ℝ ℂ where
  toFun test := FourierTransform.fourier (schwartzConjugation test)
  map_add' left right := by
    rw [map_add, FourierTransform.fourier_add]
  map_smul' scalar test := by
    rw [schwartzConjugation_smul, FourierTransform.fourier_smul]
    rfl

theorem conjugateTateQuarterMellinTest_relation
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    conjugateTateQuarterMellinTest z
        (coPoissonQuarterMellinConvergentMap z positive belowHalf test) =
      coPoissonQuarterMellinConvergentMap
        ((1 / 2 : ℂ) - star z)
        (by norm_num [Complex.sub_re]; linarith)
        (by norm_num [Complex.sub_re]; linarith)
        (schwartzTateConjugation test) := by
  apply Subtype.ext
  change positiveTateInvolution
      (positiveMellinPointwiseConjugation
        (coPoissonQuarterMellinMap test)) =
    coPoissonQuarterMellinMap
      (FourierTransform.fourier (schwartzConjugation test))
  rw [← coPoissonQuarterMellinMap_conjugation]
  exact (coPoissonQuarterMellinMap_fourier_tate
    (schwartzConjugation test)).symm

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
