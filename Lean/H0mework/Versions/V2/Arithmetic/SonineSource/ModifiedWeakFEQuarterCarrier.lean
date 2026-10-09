import H0mework.Versions.R2.Arithmetic.MellinBoundary.PositiveMellinQuarterMaterial
import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzZeroGraphCokernel
import H0mework.Versions.V2.Arithmetic.SonineSource.ModifiedWeakFEUnitDetector

/-!
# Quarter-L2 landing of the modified WeakFE source detector

The actual modified WeakFE kernel is, away from its single convention point,
the sum of the Gaussian remainder and the two canonical pole corrections.
All three summands lie in the quarter-weight `L2` carrier.  Hence the
source-generated Mellin-unit detector lands in the same lawful carrier as the
old normalized probe.

The excluded point is retained as an almost-everywhere identification; it is
not silently promoted to pointwise equality.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual
open scoped ENNReal

noncomputable section

def positiveClozelHighCorrection : ClozelPositiveMellinFunction :=
  fun t => clozelHighCorrection t.1

theorem positiveMellinLogQuarterTransform_highCorrection
    (x : ℝ) :
    positiveMellinLogQuarterTransform positiveClozelHighCorrection x =
      (Ioi 0).indicator
        (fun y : ℝ => (Real.exp (-y / 4) : ℂ)) x := by
  unfold positiveMellinLogQuarterTransform positiveClozelHighCorrection
    clozelHighCorrection
  change (Real.exp (x / 4) : ℂ) *
      (Ioi 1).indicator
        (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) (Real.exp x) = _
  by_cases positive : 0 < x
  · have expMem : Real.exp x ∈ Ioi (1 : ℝ) :=
      Real.one_lt_exp_iff.mpr positive
    have xMem : x ∈ Ioi (0 : ℝ) := mem_Ioi.mpr positive
    rw [indicator_of_mem expMem, indicator_of_mem xMem,
      complexExp_cpow_neg_half, ← ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · have nonpositive : x ≤ 0 := le_of_not_gt positive
    have expNotMem : Real.exp x ∉ Ioi (1 : ℝ) :=
      notMem_Ioi.mpr (Real.exp_le_one_iff.mpr nonpositive)
    have xNotMem : x ∉ Ioi (0 : ℝ) := notMem_Ioi.mpr nonpositive
    rw [indicator_of_notMem expNotMem,
      indicator_of_notMem xNotMem, mul_zero]

theorem positiveMellinLogQuarterTransform_highCorrection_sqNorm
    (x : ℝ) :
    ‖positiveMellinLogQuarterTransform positiveClozelHighCorrection x‖ ^ 2 =
      (Ioi 0).indicator (fun y : ℝ => Real.exp (-y / 2)) x := by
  rw [positiveMellinLogQuarterTransform_highCorrection]
  by_cases positive : 0 < x
  · have xMem : x ∈ Ioi (0 : ℝ) := mem_Ioi.mpr positive
    rw [indicator_of_mem xMem, indicator_of_mem xMem,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
    congr 1
    ring
  · have xNotMem : x ∉ Ioi (0 : ℝ) := notMem_Ioi.mpr (le_of_not_gt positive)
    rw [indicator_of_notMem xNotMem, indicator_of_notMem xNotMem,
      norm_zero, zero_pow (by norm_num)]

theorem positiveClozelHighCorrection_mem_quarterL2 :
    positiveClozelHighCorrection ∈ positiveMellinQuarterL2Submodule := by
  have measurable : AEStronglyMeasurable
      (positiveMellinLogQuarterTransform positiveClozelHighCorrection)
      (volume : Measure ℝ) := by
    rw [show positiveMellinLogQuarterTransform
        positiveClozelHighCorrection =
      (Ioi 0).indicator
        (fun y : ℝ => (Real.exp (-y / 4) : ℂ)) by
      funext x
      exact positiveMellinLogQuarterTransform_highCorrection x]
    exact (Continuous.aestronglyMeasurable <| by fun_prop).indicator
      measurableSet_Ioi
  change MemLp
    (positiveMellinLogQuarterTransform positiveClozelHighCorrection)
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [memLp_two_iff_integrable_sq_norm measurable]
  have exponentialIntegrable : IntegrableOn
      (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 (by norm_num)
  have indicatorIntegrable : Integrable
      ((Ioi 0).indicator (fun x : ℝ => Real.exp (-x / 2))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    have functionEq :
        (fun x : ℝ => Real.exp (-x / 2)) =
          (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) := by
      funext x
      congr 1
      ring
    rw [functionEq]
    exact exponentialIntegrable
  apply indicatorIntegrable.congr
  exact ae_of_all _ fun x =>
    (positiveMellinLogQuarterTransform_highCorrection_sqNorm x).symm

def positiveGeneratedRiemannModifiedKernel
    (owner : GlobalGermOwner) : ClozelPositiveMellinFunction :=
  fun t => (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1

theorem generatedRiemannModifiedKernel_eq_remainder_add_corrections
    (owner : GlobalGermOwner) (t : ℝ)
    (positive : 0 < t) (notOne : t ≠ 1) :
    (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t =
      generatedClozelGaussianRemainderKernel owner t +
        clozelLowCorrection t + clozelHighCorrection t := by
  unfold generatedClozelGaussianRemainderKernel
    clozelLowCorrection clozelHighCorrection
  rw [GeneratedRiemannWeakFEPairAt.generate_pair, WeakFEPair.f_modif]
  rcases lt_or_gt_of_ne notOne with below | above
  · rw [Pi.add_apply,
      indicator_of_notMem (notMem_Ioi.mpr below.le),
      indicator_of_mem (mem_Ioo.mpr ⟨positive, below⟩),
      indicator_of_mem (mem_Ioc.mpr ⟨positive, below.le⟩),
      indicator_of_notMem (notMem_Ioi.mpr below.le)]
    simp [HurwitzZeta.hurwitzEvenFEPair,
      Complex.ofReal_cpow positive.le]
    ring
  · rw [Pi.add_apply,
      indicator_of_mem (mem_Ioi.mpr above),
      indicator_of_notMem (notMem_Ioo_of_ge above.le),
      indicator_of_notMem (notMem_Ioc_of_gt above),
      indicator_of_mem (mem_Ioi.mpr above)]
    simp [HurwitzZeta.hurwitzEvenFEPair]

theorem positiveGeneratedRiemannModifiedKernel_logQuarter_ae_sum
    (owner : GlobalGermOwner) :
    positiveMellinLogQuarterTransform
        (positiveGeneratedRiemannModifiedKernel owner) =ᵐ[volume]
      positiveMellinLogQuarterTransform
        (positiveGeneratedClozelGaussianRemainder owner +
          positiveClozelLowCorrection + positiveClozelHighCorrection) := by
  have almostEverywhereNeZero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 :=
    compl_mem_ae_iff.mpr
      (Subsingleton.measure_zero (s := ({0} : Set ℝ)) (by simp) volume)
  filter_upwards [almostEverywhereNeZero] with x xNe
  have expNe : Real.exp x ≠ 1 := by
    intro equality
    apply xNe
    apply Real.exp_injective
    simpa using equality
  have source := generatedRiemannModifiedKernel_eq_remainder_add_corrections
    owner (Real.exp x) (Real.exp_pos x) expNe
  change (Real.exp (x / 4) : ℂ) *
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif
        (Real.exp x) = _
  rw [source]
  rw [map_add, map_add]
  change (Real.exp (x / 4) : ℂ) *
      (generatedClozelGaussianRemainderKernel owner (Real.exp x) +
        clozelLowCorrection (Real.exp x) +
        clozelHighCorrection (Real.exp x)) =
      (Real.exp (x / 4) : ℂ) *
          generatedClozelGaussianRemainderKernel owner (Real.exp x) +
        (Real.exp (x / 4) : ℂ) * clozelLowCorrection (Real.exp x) +
        (Real.exp (x / 4) : ℂ) * clozelHighCorrection (Real.exp x)
  ring

theorem positiveGeneratedRiemannModifiedKernel_mem_quarterL2
    (owner : GlobalGermOwner) :
    positiveGeneratedRiemannModifiedKernel owner ∈
      positiveMellinQuarterL2Submodule := by
  have sumMem :
      positiveGeneratedClozelGaussianRemainder owner +
          positiveClozelLowCorrection + positiveClozelHighCorrection ∈
        positiveMellinQuarterL2Submodule :=
    positiveMellinQuarterL2Submodule.add_mem
      (positiveMellinQuarterL2Submodule.add_mem
        (positiveGeneratedClozelGaussianRemainder_mem_quarterL2 owner)
        positiveClozelLowCorrection_mem_quarterL2)
      positiveClozelHighCorrection_mem_quarterL2
  change MemLp
    (positiveMellinLogQuarterTransform
      (positiveGeneratedRiemannModifiedKernel owner))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  exact (memLp_congr_ae
    (positiveGeneratedRiemannModifiedKernel_logQuarter_ae_sum owner)).mpr
      sumMem

theorem positiveSourceModifiedUnitDetector_mem_quarterL2
    (owner : GlobalGermOwner) (z : ℂ) :
    positiveSourceModifiedUnitDetector owner z ∈
      positiveMellinQuarterL2Submodule := by
  have scaled := positiveMellinQuarterL2Submodule.smul_mem
    (sourceModifiedUnitCoefficient z)
    (positiveGeneratedRiemannModifiedKernel_mem_quarterL2 owner)
  change (sourceModifiedUnitCoefficient z •
      positiveGeneratedRiemannModifiedKernel owner) ∈
    positiveMellinQuarterL2Submodule
  exact scaled

def selectedSourceModifiedUnitQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (selectedCoPoissonMuntzParameter observation) :=
  ⟨positiveSourceModifiedUnitDetector owner
      (selectedCoPoissonMuntzParameter observation),
    ⟨positiveSourceModifiedUnitDetector_mem_quarterL2 owner _,
      by
        have convergent :=
          (selectedSourceModifiedUnitElement observation nontrivial).2
        change MellinConvergent
          (positiveMellinExtension
            (positiveSourceModifiedUnitDetector owner
              (selectedCoPoissonMuntzParameter observation)))
          (selectedCoPoissonMuntzParameter observation) at convergent
        exact convergent⟩⟩

def reversalSourceModifiedUnitQuarterTest
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    QuarterMellinL2Test (reversalCoPoissonMuntzParameter observation) :=
  ⟨positiveSourceModifiedUnitDetector owner
      (reversalCoPoissonMuntzParameter observation),
    ⟨positiveSourceModifiedUnitDetector_mem_quarterL2 owner _,
      by
        have convergent :=
          (reversalSourceModifiedUnitElement observation nontrivial).2
        change MellinConvergent
          (positiveMellinExtension
            (positiveSourceModifiedUnitDetector owner
              (reversalCoPoissonMuntzParameter observation)))
          (reversalCoPoissonMuntzParameter observation) at convergent
        exact convergent⟩⟩

theorem selectedSourceModifiedUnitQuarterTest_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (selectedCoPoissonMuntzParameter observation)
      (selectedSourceModifiedUnitQuarterTest observation nontrivial) = 1 :=
  by
    have source := selectedSourceModifiedUnitElement_functional_one
      observation nontrivial
    change mellin
      (positiveMellinExtension
        (positiveSourceModifiedUnitDetector owner
          (selectedCoPoissonMuntzParameter observation)))
      (selectedCoPoissonMuntzParameter observation) = 1 at source
    exact source

theorem reversalSourceModifiedUnitQuarterTest_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional
        (reversalCoPoissonMuntzParameter observation)
      (reversalSourceModifiedUnitQuarterTest observation nontrivial) = 1 :=
  by
    have source := reversalSourceModifiedUnitElement_functional_one
      observation nontrivial
    change mellin
      (positiveMellinExtension
        (positiveSourceModifiedUnitDetector owner
          (reversalCoPoissonMuntzParameter observation)))
      (reversalCoPoissonMuntzParameter observation) = 1 at source
    exact source

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
