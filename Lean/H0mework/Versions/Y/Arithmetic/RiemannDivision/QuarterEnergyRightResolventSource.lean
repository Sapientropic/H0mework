import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import H0mework.Arithmetic.Mellin.QuarterEnergy
import H0mework.Versions.Y.Arithmetic.BurnolCarrier.CompactAnnulusZeroConsumer

/-!
# Source-generated right resolvent of the quarter-energy action

For a spectral coordinate strictly to the right of the quarter line, the
one-sided exponentially weighted orbit integral is an actual element of the
existing log-energy carrier.  Translating it writes a finite orbit segment
as its exact boundary.  No spectral vector, boundary membership, or
cancellation is supplied by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

def positiveMellinQuarterLogTranslationMap (shift : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => shift + x, continuous_const.add continuous_id⟩

theorem positiveMellinQuarterLogTranslationMap_continuous :
    Continuous positiveMellinQuarterLogTranslationMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun point : ℝ × ℝ => point.1 + point.2
  fun_prop

theorem positiveMellinQuarterEnergyTranslation_stronglyContinuous
    (value : PositiveMellinQuarterEnergy) :
    Continuous fun shift : ℝ =>
      positiveMellinQuarterEnergyTranslation shift value := by
  change Continuous fun shift : ℝ =>
    Lp.compMeasurePreserving
      (positiveMellinQuarterLogTranslationMap shift)
      (measurePreserving_add_left (volume : Measure ℝ) shift) value
  exact (continuous_const (y := value)).compMeasurePreservingLp
    positiveMellinQuarterLogTranslationMap_continuous
    (fun shift => measurePreserving_add_left (volume : Measure ℝ) shift)
    (by norm_num)

def positiveMellinQuarterRightResolventWeight
    (coordinate : ℂ) (shift : ℝ) : ℂ :=
  Complex.exp (((1 / 4 : ℂ) - coordinate) * (shift : ℂ))

theorem positiveMellinQuarterRightResolventWeight_continuous
    (coordinate : ℂ) :
    Continuous (positiveMellinQuarterRightResolventWeight coordinate) := by
  unfold positiveMellinQuarterRightResolventWeight
  fun_prop

theorem norm_positiveMellinQuarterRightResolventWeight
    (coordinate : ℂ) (shift : ℝ) :
    ‖positiveMellinQuarterRightResolventWeight coordinate shift‖ =
      Real.exp (-(coordinate.re - 1 / 4) * shift) := by
  unfold positiveMellinQuarterRightResolventWeight
  rw [Complex.norm_exp]
  congr 1
  norm_num

theorem positiveMellinQuarterRightResolventWeight_add
    (coordinate : ℂ) (first second : ℝ) :
    positiveMellinQuarterRightResolventWeight coordinate (first + second) =
      positiveMellinQuarterRightResolventWeight coordinate first *
        positiveMellinQuarterRightResolventWeight coordinate second := by
  unfold positiveMellinQuarterRightResolventWeight
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def positiveMellinQuarterRightResolventCharacter
    (coordinate : ℂ) (shift : ℝ) : ℂ :=
  positiveMellinQuarterRightResolventWeight coordinate (-shift)

theorem positiveMellinQuarterRightResolventCharacter_mul_weight_add
    (coordinate : ℂ) (base shift : ℝ) :
    positiveMellinQuarterRightResolventCharacter coordinate shift *
        positiveMellinQuarterRightResolventWeight coordinate (base + shift) =
      positiveMellinQuarterRightResolventWeight coordinate base := by
  rw [positiveMellinQuarterRightResolventCharacter,
    positiveMellinQuarterRightResolventWeight_add]
  have inverse :
      positiveMellinQuarterRightResolventWeight coordinate (-shift) *
          positiveMellinQuarterRightResolventWeight coordinate shift = 1 := by
    rw [← positiveMellinQuarterRightResolventWeight_add]
    simp [positiveMellinQuarterRightResolventWeight]
  calc
    _ = positiveMellinQuarterRightResolventWeight coordinate base *
        (positiveMellinQuarterRightResolventWeight coordinate (-shift) *
          positiveMellinQuarterRightResolventWeight coordinate shift) := by ring
    _ = _ := by rw [inverse, mul_one]

def positiveMellinQuarterRightResolventIntegrand
    (coordinate : ℂ) (value : PositiveMellinQuarterEnergy) (shift : ℝ) :
    PositiveMellinQuarterEnergy :=
  positiveMellinQuarterRightResolventWeight coordinate shift •
    positiveMellinQuarterEnergyTranslation shift value

theorem positiveMellinQuarterRightResolventIntegrand_continuous
    (coordinate : ℂ) (value : PositiveMellinQuarterEnergy) :
    Continuous
      (positiveMellinQuarterRightResolventIntegrand coordinate value) := by
  unfold positiveMellinQuarterRightResolventIntegrand
  exact (positiveMellinQuarterRightResolventWeight_continuous coordinate).smul
    (positiveMellinQuarterEnergyTranslation_stronglyContinuous value)

theorem positiveMellinQuarterEnergyTranslation_resolventIntegrand
    (coordinate : ℂ) (value : PositiveMellinQuarterEnergy)
    (base shift : ℝ) :
    positiveMellinQuarterEnergyTranslation shift
        (positiveMellinQuarterRightResolventIntegrand
          coordinate value base) =
      positiveMellinQuarterRightResolventCharacter coordinate shift •
        positiveMellinQuarterRightResolventIntegrand
          coordinate value (base + shift) := by
  unfold positiveMellinQuarterRightResolventIntegrand
  rw [map_smul]
  have composition := LinearMap.congr_fun
    (positiveMellinQuarterEnergyTranslation_comp shift base) value
  change positiveMellinQuarterEnergyTranslation shift
      (positiveMellinQuarterEnergyTranslation base value) =
    positiveMellinQuarterEnergyTranslation (base + shift) value at composition
  rw [composition, smul_smul]
  congr 1
  exact (positiveMellinQuarterRightResolventCharacter_mul_weight_add
    coordinate base shift).symm

theorem positiveMellinQuarterRightResolventIntegrand_integrableOn
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : PositiveMellinQuarterEnergy) :
    IntegrableOn
      (positiveMellinQuarterRightResolventIntegrand coordinate value)
      (Ioi (0 : ℝ)) := by
  let decay : ℝ → ℝ := fun shift =>
    Real.exp (-(coordinate.re - 1 / 4) * shift) * ‖value‖
  have decayIntegrable : IntegrableOn decay (Ioi (0 : ℝ)) := by
    have base := exp_neg_integrableOn_Ioi 0
      (sub_pos.mpr rightQuarter)
    exact base.mul_const ‖value‖
  apply Integrable.mono' decayIntegrable.norm
    ((positiveMellinQuarterRightResolventIntegrand_continuous
      coordinate value).aestronglyMeasurable.restrict)
  filter_upwards with shift
  have leftRead :
      ‖positiveMellinQuarterRightResolventIntegrand
          coordinate value shift‖ = decay shift := by
    simp only [positiveMellinQuarterRightResolventIntegrand, norm_smul,
      positiveMellinQuarterEnergyTranslation_norm,
      norm_positiveMellinQuarterRightResolventWeight, decay]
  rw [leftRead, Real.norm_of_nonneg]
  positivity

theorem positiveMellinQuarterRightResolventIntegrand_tailShift
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : PositiveMellinQuarterEnergy) (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    (∫ base : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventIntegrand
          coordinate value (base + shift)) =
      ∫ base : ℝ in Ioi shift,
        positiveMellinQuarterRightResolventIntegrand coordinate value base := by
  let integrand := positiveMellinQuarterRightResolventIntegrand coordinate value
  have integrable : IntegrableOn integrand (Ioi (0 : ℝ)) :=
    positiveMellinQuarterRightResolventIntegrand_integrableOn
      coordinate rightQuarter value
  have tailSubset : Ioi shift ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_le_of_lt shiftNonnegative hx
  have tailIntegrable : IntegrableOn integrand (Ioi shift) :=
    integrable.mono_set tailSubset
  have indicatorIntegrable : Integrable ((Ioi shift).indicator integrand) :=
    tailIntegrable.integrable_indicator measurableSet_Ioi
  have translated :=
    (measurePreserving_add_left (volume : Measure ℝ) shift).integral_comp
      (Homeomorph.addLeft shift).measurableEmbedding
      ((Ioi shift).indicator integrand)
  rw [integral_indicator measurableSet_Ioi] at translated
  calc
    (∫ base : ℝ in Ioi (0 : ℝ), integrand (base + shift)) =
        ∫ base : ℝ,
          (Ioi shift).indicator integrand (shift + base) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with base
      by_cases positive : 0 < base
      · have shifted : shift < shift + base := by linarith
        simp [positive, shifted, add_comm]
      · have shifted : ¬ shift < shift + base := by linarith
        simp [positive, shifted]
    _ = ∫ base : ℝ in Ioi shift, integrand base := by
      simpa only [integrand] using translated

/-- Source-generated one-sided resolvent in the actual quarter-energy
carrier.  It is an orbit integral, not a supplied spectral vector. -/
def positiveMellinQuarterRightResolvent
    (coordinate : ℂ) (value : PositiveMellinQuarterEnergy) :
    PositiveMellinQuarterEnergy :=
  -∫ shift : ℝ in Ioi (0 : ℝ),
    positiveMellinQuarterRightResolventIntegrand coordinate value shift

/-- The finite source segment written by one positive translation of the
one-sided resolvent. -/
def positiveMellinQuarterRightResolventBoundarySource
    (coordinate : ℂ) (value : PositiveMellinQuarterEnergy) (shift : ℝ) :
    PositiveMellinQuarterEnergy :=
  ∫ base : ℝ in Ioc (0 : ℝ) shift,
    positiveMellinQuarterRightResolventIntegrand coordinate value base

theorem positiveMellinQuarterRightResolvent_sourceBoundary
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : PositiveMellinQuarterEnergy)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    positiveMellinQuarterEnergyTranslation shift
        (positiveMellinQuarterRightResolvent coordinate value) -
      positiveMellinQuarterRightResolventCharacter coordinate shift •
        positiveMellinQuarterRightResolvent coordinate value =
      positiveMellinQuarterRightResolventCharacter coordinate shift •
        positiveMellinQuarterRightResolventBoundarySource
          coordinate value shift := by
  let integrand := positiveMellinQuarterRightResolventIntegrand coordinate value
  let character := positiveMellinQuarterRightResolventCharacter coordinate shift
  have integrable : IntegrableOn integrand (Ioi (0 : ℝ)) :=
    positiveMellinQuarterRightResolventIntegrand_integrableOn
      coordinate rightQuarter value
  have segmentSubset : Ioc (0 : ℝ) shift ⊆ Ioi (0 : ℝ) := by
    intro base membership
    exact membership.1
  have tailSubset : Ioi shift ⊆ Ioi (0 : ℝ) := by
    intro base membership
    exact lt_of_le_of_lt shiftNonnegative membership
  have segmentIntegrable : IntegrableOn integrand (Ioc (0 : ℝ) shift) :=
    integrable.mono_set segmentSubset
  have tailIntegrable : IntegrableOn integrand (Ioi shift) :=
    integrable.mono_set tailSubset
  have split :
      (∫ base : ℝ in Ioi (0 : ℝ), integrand base) =
        (∫ base : ℝ in Ioc (0 : ℝ) shift, integrand base) +
          ∫ base : ℝ in Ioi shift, integrand base := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi shiftNonnegative]
    apply setIntegral_union
    · rw [Set.disjoint_left]
      intro base first second
      exact (not_lt_of_ge first.2) second
    · exact measurableSet_Ioi
    · exact segmentIntegrable
    · exact tailIntegrable
  have shifted :
      (∫ base : ℝ in Ioi (0 : ℝ), integrand (base + shift)) =
        ∫ base : ℝ in Ioi shift, integrand base := by
    exact positiveMellinQuarterRightResolventIntegrand_tailShift
      coordinate rightQuarter value shift shiftNonnegative
  have mapIntegral :
      positiveMellinQuarterEnergyTranslation shift
          (∫ base : ℝ in Ioi (0 : ℝ), integrand base) =
        ∫ base : ℝ in Ioi (0 : ℝ),
          positiveMellinQuarterEnergyTranslation shift (integrand base) := by
    exact (LinearIsometry.integral_comp_comm
      (positiveMellinQuarterEnergyTranslationIsometry shift).toLinearIsometry
      integrand).symm
  unfold positiveMellinQuarterRightResolvent
    positiveMellinQuarterRightResolventBoundarySource
  change positiveMellinQuarterEnergyTranslation shift
        (-(∫ base : ℝ in Ioi (0 : ℝ), integrand base)) -
      character • (-(∫ base : ℝ in Ioi (0 : ℝ), integrand base)) =
    character • (∫ base : ℝ in Ioc (0 : ℝ) shift, integrand base)
  rw [map_neg, mapIntegral]
  have translatedIntegral :
      (∫ base : ℝ in Ioi (0 : ℝ),
          positiveMellinQuarterEnergyTranslation shift (integrand base)) =
        character • ∫ base : ℝ in Ioi shift, integrand base := by
    calc
      _ = ∫ base : ℝ in Ioi (0 : ℝ),
          character • integrand (base + shift) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro base _
        exact positiveMellinQuarterEnergyTranslation_resolventIntegrand
          coordinate value base shift
      _ = character • ∫ base : ℝ in Ioi (0 : ℝ),
          integrand (base + shift) := by
        rw [integral_smul]
      _ = _ := by rw [shifted]
  rw [translatedIntegral, split]
  module

theorem positiveMellinQuarterRightResolvent_norm_le
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : PositiveMellinQuarterEnergy) :
    ‖positiveMellinQuarterRightResolvent coordinate value‖ ≤
      (coordinate.re - 1 / 4)⁻¹ * ‖value‖ := by
  unfold positiveMellinQuarterRightResolvent
  rw [norm_neg]
  calc
    ‖∫ shift : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventIntegrand coordinate value shift‖ ≤
        ∫ shift : ℝ in Ioi (0 : ℝ),
          ‖positiveMellinQuarterRightResolventIntegrand
            coordinate value shift‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ shift : ℝ in Ioi (0 : ℝ),
        Real.exp (-(coordinate.re - 1 / 4) * shift) * ‖value‖ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro shift _
      simp only [positiveMellinQuarterRightResolventIntegrand, norm_smul,
        positiveMellinQuarterEnergyTranslation_norm,
        norm_positiveMellinQuarterRightResolventWeight]
    _ = (coordinate.re - 1 / 4)⁻¹ * ‖value‖ := by
      rw [integral_mul_const]
      have integralValue := integral_exp_mul_Ioi
        (show -(coordinate.re - 1 / 4) < 0 by linarith) 0
      rw [integralValue]
      simp only [mul_zero, Real.exp_zero]
      field_simp [sub_ne_zero.mpr (ne_of_gt rightQuarter)]

open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState

/-- Direct zero-owned source consumer.  An actual compact co-Poisson
relation is first annihilated at the same zeta-zero coordinate; its
source-generated right resolvent then writes the finite orbit boundary. -/
theorem zeroOwnedCompactRelation_rightResolvent_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
    let z := observation.coordinate / 2
    let relation := coPoissonQuarterMellinConvergentMap z
      (by rw [Complex.div_re]; norm_num; linarith)
      (by
        rw [Complex.div_re]
        norm_num
        linarith [observation.coordinate_re_lt_one])
      burnolEvenAnnulusCompactSource.1
    let energy := quarterMellinL2Feature z relation
    quarterMellinL2Functional z relation = 0 ∧
      positiveMellinQuarterEnergyTranslation shift
          (positiveMellinQuarterRightResolvent z energy) -
        positiveMellinQuarterRightResolventCharacter z shift •
          positiveMellinQuarterRightResolvent z energy =
        positiveMellinQuarterRightResolventCharacter z shift •
          positiveMellinQuarterRightResolventBoundarySource z energy shift ∧
      ‖positiveMellinQuarterRightResolvent z energy‖ ≤
        (z.re - 1 / 4)⁻¹ * ‖energy‖ := by
  dsimp only
  have rightQuarter' : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith
  refine ⟨burnolCompactAnnulusSource_selectedZeroMellinRead_eq_zero
      observation nontrivial,
    positiveMellinQuarterRightResolvent_sourceBoundary
      (observation.coordinate / 2) rightQuarter' _ shift shiftNonnegative,
    positiveMellinQuarterRightResolvent_norm_le
      (observation.coordinate / 2) rightQuarter' _⟩

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
