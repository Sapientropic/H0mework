import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusClosedRange
import H0mework.Versions.R2.Arithmetic.Muntz.CoPoissonMuntzZeroAnnihilation
import H0mework.Versions.R2.Arithmetic.RiemannSpectral.AdditiveFourierFixedSourceState

/-! # Direct zero-owned consumer of the additive Burnol co-Poisson range -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open MeasureTheory

noncomputable section

/-- The previously certified concrete annulus is an actual member of the
new source family. -/
def burnolEvenAnnulusCompactSource : burnolCompactAnnulusSource :=
  ⟨burnolEvenAnnulusSchwartz,
    ⟨burnolEvenAnnulusSchwartz_even,
      fun x inside => by
        simp only [burnolEvenAnnulusSchwartz, add_apply,
          burnolAnnulusSchwartzReflection_apply, burnolAnnulusSchwartz_apply]
        rw [burnolAnnulusBump_zero_of_abs_le_quarter inside,
          burnolAnnulusBump_zero_of_abs_le_quarter (by simpa using inside)]
        norm_num,
      fun x outside => by
        have outer : (3 / 4 : ℝ) ≤ |x| := by linarith
        have outerNeg : (3 / 4 : ℝ) ≤ |-x| := by simpa using outer
        simp only [burnolEvenAnnulusSchwartz, add_apply,
          burnolAnnulusSchwartzReflection_apply, burnolAnnulusSchwartz_apply]
        rw [burnolAnnulusBump_zero_of_three_quarters_le_abs outer,
          burnolAnnulusBump_zero_of_three_quarters_le_abs outerNeg]
        norm_num⟩⟩

theorem burnolEvenAnnulusCompactCoSum_eq :
    burnolCompactAdditiveCoSum burnolEvenAnnulusCompactSource =
      burnolAdditiveCoSum := by
  rfl

theorem burnolEvenAnnulusCompactL2_eq :
    burnolCompactAdditiveL2 burnolEvenAnnulusCompactSource =
      burnolAdditiveFullEvenL2 := by
  apply Lp.ext
  filter_upwards [burnolCompactAdditiveL2_coeFn
      burnolEvenAnnulusCompactSource,
    burnolAdditiveFullEvenL2_coeFn] with t left right
  rw [left, right]
  rfl

theorem burnolEvenAnnulusCompactPhysicalState_eq :
    burnolCompactAdditivePhysicalState burnolEvenAnnulusCompactSource =
      burnolAdditiveEvenPhysicalState := by
  apply Subtype.ext
  exact burnolEvenAnnulusCompactL2_eq

theorem burnolCompactCoPoissonClosedRange_ne_bot :
    burnolCompactCoPoissonClosedRange ≠ ⊥ := by
  intro bottom
  let index : BurnolCompactCoPoissonGeneratorIndex :=
    (burnolEvenAnnulusCompactSource, 0)
  have membership := burnolCompactCoPoissonGenerator_mem_closedRange index
  rw [bottom, ClosedSubmodule.mem_bot] at membership
  have generatorEq : burnolCompactCoPoissonGenerator index =
      burnolAdditiveEvenPhysicalState := by
    change burnolCompactAdditivePhysicalState burnolEvenAnnulusCompactSource = _
    exact burnolEvenAnnulusCompactPhysicalState_eq
  rw [generatorEq] at membership
  exact burnolAdditiveActualNonzeroPhysicalState.2
    (congrArg Subtype.val membership)

theorem burnolCompactAnnulusSource_selectedZeroMellinRead_eq_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (observation.coordinate / 2)
        (coPoissonQuarterMellinConvergentMap
          (observation.coordinate / 2)
          (selectedPositiveParameter_re_pos observation nontrivial)
          (by
            have strip := observation.coordinate_re_lt_one
            rw [Complex.div_re]
            norm_num
            linarith)
          burnolEvenAnnulusCompactSource.1) = 0 := by
  exact LinearMap.congr_fun
    (selectedZero_quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      observation nontrivial) burnolEvenAnnulusCompactSource.1

/-- The same actual compact source generates a nonzero additive Burnol
closed range and a zero-owned Müntz annihilation.  The theorem deliberately
stops before claiming an additive completed-Mellin evaluator. -/
theorem zeroOwnedBurnolCompactCoPoissonRange_directConsumer
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat,
      observation.coordinate = -2 * (n + 1)) :
    quarterMellinL2Functional (observation.coordinate / 2)
          (coPoissonQuarterMellinConvergentMap
            (observation.coordinate / 2)
            (selectedPositiveParameter_re_pos observation nontrivial)
            (by
              have strip := observation.coordinate_re_lt_one
              rw [Complex.div_re]
              norm_num
              linarith)
            burnolEvenAnnulusCompactSource.1) = 0 ∧
      burnolCompactCoPoissonClosedRange ≠ ⊥ :=
  ⟨burnolCompactAnnulusSource_selectedZeroMellinRead_eq_zero
      observation nontrivial,
    burnolCompactCoPoissonClosedRange_ne_bot⟩

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
