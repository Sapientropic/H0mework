import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Raw

/-! The actual finite Volterra window reads the generated source tail. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem sourceVolterraResolvent_positive_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ∀ᵐ t ∂volume, ∀ positive : 0 < t,
      sourceVolterraResolvent coordinate value t =
        -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf value := by
  filter_upwards [sourceVolterraResolvent_coeFn coordinate value] with t rawRead positive
  rw [rawRead, burnolFourierRightDivisionRaw_eq_tail _ _ positive,
    burnolRadiusMellinTailEvaluator_eq_integral]
  rw [show 2 * (coordinate.value / 2) = coordinate.value by ring,
    show -2 * (coordinate.value / 2) = -coordinate.value by ring]

theorem sourceVolterraWindow_positive_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ∀ᵐ t ∂volume, ∀ inside : t ∈ Ioo (1 / 4 : ℝ) 4,
      sourceVolterraWindow coordinate value t =
        -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          burnolRadiusMellinTailEvaluator t (by linarith [inside.1])
            coordinate.value coordinate.rightHalf value := by
  filter_upwards [sourceAnnulusCut_coeFn (sourceVolterraResolvent coordinate value),
    sourceVolterraResolvent_positive_profile coordinate value] with t cutRead rawRead inside
  have positive : 0 < t := by linarith [inside.1]
  change sourceAnnulusCut (sourceVolterraResolvent coordinate value) t = _
  rw [cutRead, if_pos (by simpa only [abs_of_pos positive] using ⟨inside.1, inside.2.le⟩)]
  exact rawRead positive

theorem sourceAnnulusCut_idempotent (value : BurnolL2) :
    sourceAnnulusCut (sourceAnnulusCut value) = sourceAnnulusCut value := by
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (sourceAnnulusCut value),
    sourceAnnulusCut_coeFn value] with x twice once
  rw [twice]
  by_cases inside : (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4
  · rw [if_pos inside]
  · rw [if_neg inside, once, if_neg inside]

/-- Annulus support itself eliminates the upper endpoint tail. -/
theorem source_annulus_outer_tail_zero (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (supported : sourceAnnulusCut value = value) :
    burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value = 0 := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  apply integral_eq_zero_of_ae
  have profile := sourceAnnulusCut_coeFn value
  rw [supported] at profile
  filter_upwards [ae_restrict_of_ae profile, ae_restrict_mem measurableSet_Ioi]
    with t sourceRead outside
  have out : ¬ ((1 / 4 : ℝ) < |t| ∧ |t| ≤ 4) := by
    intro h
    have positive : 0 < t := by linarith [show (4 : ℝ) < t from outside]
    rw [abs_of_pos positive] at h
    exact (not_le_of_gt outside) h.2
  rw [sourceRead, if_neg out, mul_zero]
  rfl

/-- Every annulus-supported source has the finite Volterra profile, with its upper tail generated zero. -/
theorem sourceVolterraWindow_annulus_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (supported : sourceAnnulusCut value = value) :
    ∀ᵐ t ∂volume, ∀ inside : t ∈ Ioo (1 / 4 : ℝ) 4,
      sourceVolterraWindow coordinate value t =
        -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          (burnolRadiusMellinTailEvaluator t (by linarith [inside.1])
            coordinate.value coordinate.rightHalf value -
          burnolRadiusMellinTailEvaluator 4 (by norm_num)
            coordinate.value coordinate.rightHalf value) := by
  simpa only [source_annulus_outer_tail_zero coordinate value supported, sub_zero] using
    sourceVolterraWindow_positive_profile coordinate value

theorem sourceVolterraWindow_cut_profile
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    ∀ᵐ t ∂volume, ∀ inside : t ∈ Ioo (1 / 4 : ℝ) 4,
      sourceVolterraWindow coordinate (sourceAnnulusCut value) t =
        -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          (burnolRadiusMellinTailEvaluator t (by linarith [inside.1])
            coordinate.value coordinate.rightHalf (sourceAnnulusCut value) -
          burnolRadiusMellinTailEvaluator 4 (by norm_num)
            coordinate.value coordinate.rightHalf (sourceAnnulusCut value)) :=
  sourceVolterraWindow_annulus_profile coordinate (sourceAnnulusCut value)
    (sourceAnnulusCut_idempotent value)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
