import H0mework.Probability.Source.ConditionalNext
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNext

open SourceWeightedRecovery
open scoped Classical
noncomputable section

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

private theorem probability_upper {A : Type*} (p : PMF A) (point : A) : (p point).toReal ≤ 1 := by
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (p.coe_le_one point)

theorem entropy_nonnegative {A : Type*} [Fintype A] (p : PMF A) : 0 ≤ entropy p :=
  neg_nonneg.mpr (Finset.sum_nonpos fun point _ =>
    Real.mul_log_nonpos ENNReal.toReal_nonneg (probability_upper p point))

theorem entropy_zero_iff_singleton {A : Type*} [Fintype A] (p : PMF A) (atom : A)
    (supported : atom ∈ p.support) : entropy p = 0 ↔ p.support = {atom} := by
  constructor
  · intro zero
    have total : (∑ point, (p point).toReal * Real.log (p point).toReal) = 0 := neg_eq_zero.mp zero
    have term := (Finset.sum_eq_zero_iff_of_nonpos
      (fun point (_ : point ∈ (Finset.univ : Finset A)) =>
        Real.mul_log_nonpos ENNReal.toReal_nonneg (probability_upper p point))).mp total atom (Finset.mem_univ _)
    have positive : 0 < (p atom).toReal := ENNReal.toReal_pos supported (p.apply_ne_top atom)
    have unit : (p atom).toReal = 1 := le_antisymm (probability_upper p atom)
      (le_of_not_gt fun below => (ne_of_lt (Real.mul_log_neg positive below)) term)
    exact (p.apply_eq_one_iff atom).mp ((ENNReal.toReal_eq_one_iff _).mp unit)
  · intro singleton
    apply neg_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro point _
    by_cases same : point = atom
    · subst point
      rw [(p.apply_eq_one_iff atom).mpr singleton]
      simp only [ENNReal.toReal_one, Real.log_one, mul_zero]
    · have zero : p point = 0 := (p.apply_eq_zero_iff point).mpr (by simpa [singleton] using same)
      simp only [zero, ENNReal.toReal_zero, zero_mul]

universe u v w
variable {Source : Type u} [Fintype Source] {Observed : Type v} {Next : Type w} [Fintype Next]
variable (source : PMF Source) (read : Source → Observed) (nextRead : Source → Next)
variable (positive : ∀ point, point ∈ source.support)

def conditionalEntropy : ℝ :=
  ∑ point, (source point).toReal *
    entropy (conditionalNext source read nextRead (read point)
      (observed_supported source read point (positive point)))

theorem conditionalEntropy_nonnegative : 0 ≤ conditionalEntropy source read nextRead positive :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (entropy_nonnegative _)

theorem conditionalEntropy_zero_iff : conditionalEntropy source read nextRead positive = 0 ↔
    ∀ left right, read left = read right → nextRead left = nextRead right := by
  constructor
  · intro zero left right same
    have term := (Finset.sum_eq_zero_iff_of_nonneg
      (fun point (_ : point ∈ (Finset.univ : Finset Source)) =>
        mul_nonneg ENNReal.toReal_nonneg (entropy_nonnegative
          (conditionalNext source read nextRead (read point)
            (observed_supported source read point (positive point)))))).mp zero left (Finset.mem_univ _)
    have nullEntropy := (mul_eq_zero.mp term).resolve_left
      (ne_of_gt (ENNReal.toReal_pos (positive left) (source.apply_ne_top left)))
    have leftMember := (conditionalNext_support source read nextRead (read left)
      (observed_supported source read left (positive left)) (nextRead left)).mpr
        ⟨left, rfl, positive left, rfl⟩
    have rightMember := (conditionalNext_support source read nextRead (read left)
      (observed_supported source read left (positive left)) (nextRead right)).mpr
        ⟨right, same.symm, positive right, rfl⟩
    have singleton := (entropy_zero_iff_singleton _ (nextRead left) leftMember).mp nullEntropy
    exact (Set.mem_singleton_iff.mp (singleton ▸ rightMember)).symm
  · intro determined
    apply Finset.sum_eq_zero
    intro point _
    have member := (conditionalNext_support source read nextRead (read point)
      (observed_supported source read point (positive point)) (nextRead point)).mpr
        ⟨point, rfl, positive point, rfl⟩
    have singleton : (conditionalNext source read nextRead (read point)
        (observed_supported source read point (positive point))).support = {nextRead point} := by
      apply Set.ext
      intro value
      constructor
      · intro inside
        obtain ⟨other, same, _, target⟩ := (conditionalNext_support source read nextRead (read point)
          (observed_supported source read point (positive point)) value).mp inside
        exact Set.mem_singleton_iff.mpr (target.symm.trans (determined other point same))
      · intro inside
        exact Set.mem_singleton_iff.mp inside ▸ member
    rw [(entropy_zero_iff_singleton _ (nextRead point) member).mpr singleton, mul_zero]

end
end SourceConditionalNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
