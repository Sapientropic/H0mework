import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Shell

/-! The same actual Pa shell is a continuous compact family for Volterra synthesis. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem volterraShell_reciprocal_admitted (u : ℝ) (inside : u ∈ Icc (1 / 4 : ℝ) 4) :
    u⁻¹ ∈ Icc (1 / 4 : ℝ) 4 := by
  have positive : 0 < u := lt_of_lt_of_le (by norm_num) inside.1
  constructor
  · rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive]
    exact inside.2
  · rw [show (4 : ℝ) = (1 / 4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ positive (by norm_num : (0 : ℝ) < 1 / 4)]
    exact inside.1

private theorem unitTailPrimitive_continuousOn (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) :
    ContinuousOn (burnolUnitTailPrimitiveValue coordinate value) (Icc (1 / 4 : ℝ) 4) := by
  have weight : ContinuousOn (burnolUnitPowerWeight coordinate) (Icc (1 / 4 : ℝ) 4) :=
    (Complex.continuous_ofReal.continuousOn.cpow_const
      (fun _ inside => Complex.ofReal_mem_slitPlane.mpr
        (lt_of_lt_of_le (by norm_num) inside.1))).neg
  have scale : ContinuousOn (burnolSourceScalePrimitive value) (Icc (1 / 4 : ℝ) 4) :=
    (burnolSourceScalePrimitive_continuous value).mono
      (fun _ inside => lt_of_lt_of_le (by norm_num) inside.1)
  have integrated : ContinuousOn (fun upper => ∫ u : ℝ in Ioc 0 upper,
      burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive value u) (Icc (0 : ℝ) 4) :=
    intervalIntegral.continuousOn_primitive
      ((integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
        (burnolUnitTailSlope_integrable coordinate value 4))
  exact (weight.smul scale).sub
    (integrated.mono (Icc_subset_Icc (by norm_num) le_rfl))

theorem closedShell_inverse_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (fun u : Icc (1 / 4 : ℝ) 4 =>
      closedShellState coordinate (u : ℝ)⁻¹ (volterraShell_reciprocal_admitted u u.property)) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun u : Icc (1 / 4 : ℝ) 4 =>
    burnolUnitTailResponse coordinate (u : ℝ)⁻¹ - burnolUnitTailResponse coordinate 4)
  simp only [burnolUnitTailResponse, inv_inv]
  have primitive : Continuous (fun u : Icc (1 / 4 : ℝ) 4 =>
      burnolUnitTailPrimitiveValue coordinate burnolUnitCountingPrimitiveL2 (u : ℝ)) :=
    (unitTailPrimitive_continuousOn coordinate burnolUnitCountingPrimitiveL2).domRestrict
  exact primitive.sub continuous_const

/-- The unique physical shell family is zero off the synthesis interval. -/
def volterraPhysicalShell (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) :
    BurnolPaAmbientCarrier :=
  if inside : u ∈ Icc (1 / 4 : ℝ) 4 then
    -closedShellState coordinate u⁻¹ (volterraShell_reciprocal_admitted u inside) else 0

theorem volterraPhysicalShell_mem (coordinate : BurnolCompletedMellinCoordinate) (u : ℝ) :
    volterraPhysicalShell coordinate u ∈ burnolCompactCoPoissonClosedRange := by
  unfold volterraPhysicalShell
  split_ifs with inside
  · exact burnolCompactCoPoissonClosedRange.toSubmodule.neg_mem
      (closedShellState_mem coordinate u⁻¹ (volterraShell_reciprocal_admitted u inside))
  · exact burnolCompactCoPoissonClosedRange.toSubmodule.zero_mem

theorem volterraPhysicalShell_continuousOn (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (volterraPhysicalShell coordinate) (Icc (1 / 4 : ℝ) 4) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (closedShell_inverse_continuous coordinate).neg using 1
  funext u
  exact dif_pos u.property

theorem volterraPhysicalShell_stronglyMeasurable (coordinate : BurnolCompletedMellinCoordinate) :
    StronglyMeasurable (volterraPhysicalShell coordinate) := by
  apply stronglyMeasurable_of_restrict_of_restrict_compl measurableSet_Icc
  · exact (volterraPhysicalShell_continuousOn coordinate).domRestrict.stronglyMeasurable
  · have zero : ((Icc (1 / 4 : ℝ) 4)ᶜ).domRestrict (volterraPhysicalShell coordinate) =
        fun _ => 0 := by
      funext u
      exact dif_neg u.property
    rw [zero]
    exact stronglyMeasurable_const

theorem volterraPhysicalShell_measurable (coordinate : BurnolCompletedMellinCoordinate) :
    @Measurable ℝ BurnolPaAmbientCarrier _ (borel BurnolPaAmbientCarrier)
      (volterraPhysicalShell coordinate) := by
  borelize ↥BurnolPaAmbientCarrier
  exact (volterraPhysicalShell_stronglyMeasurable coordinate).measurable

theorem volterraPhysicalShell_norm_bounded (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ u : ℝ, ‖volterraPhysicalShell coordinate u‖ ≤ bound := by
  rcases isCompact_Icc.exists_bound_of_continuousOn
    (volterraPhysicalShell_continuousOn coordinate) with ⟨bound, bounds⟩
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro u
  by_cases inside : u ∈ Icc (1 / 4 : ℝ) 4
  · exact (bounds u inside).trans (le_max_left _ _)
  · rw [volterraPhysicalShell, dif_neg inside, norm_zero]
    exact le_max_right _ _

theorem volterraPhysicalShell_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (volterraPhysicalShell coordinate) volume := by
  have integrable : IntegrableOn (volterraPhysicalShell coordinate) (Icc (1 / 4 : ℝ) 4) volume :=
    (volterraPhysicalShell_continuousOn coordinate).integrableOn_Icc
  have same : (Icc (1 / 4 : ℝ) 4).indicator (volterraPhysicalShell coordinate) =
      volterraPhysicalShell coordinate := by
    funext u
    by_cases inside : u ∈ Icc (1 / 4 : ℝ) 4
    · exact indicator_of_mem inside _
    · simp only [indicator_of_notMem inside, volterraPhysicalShell, dif_neg inside]
  exact same ▸ (integrable_indicator_iff measurableSet_Icc).mpr integrable

/-- Every integrable source weight synthesizes a Bochner-integrable actual physical family. -/
theorem volterraPhysicalShell_smul_integrable (coordinate : BurnolCompletedMellinCoordinate)
    (weight : ℝ → ℂ) (weightIntegrable : IntegrableOn weight (Icc (1 / 4 : ℝ) 4)) :
    Integrable (fun u => weight u • volterraPhysicalShell coordinate u) volume := by
  rcases volterraPhysicalShell_norm_bounded coordinate with ⟨bound, _, bounds⟩
  have weighted : IntegrableOn (fun u => weight u • volterraPhysicalShell coordinate u)
      (Icc (1 / 4 : ℝ) 4) := by
    apply (weightIntegrable.norm.mul_const bound).mono'
      (weightIntegrable.aestronglyMeasurable.smul
        (volterraPhysicalShell_stronglyMeasurable coordinate).aestronglyMeasurable)
    filter_upwards with u
    change ‖weight u • volterraPhysicalShell coordinate u‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounds u) (norm_nonneg _)
  have same : (Icc (1 / 4 : ℝ) 4).indicator
      (fun u => weight u • volterraPhysicalShell coordinate u) =
        fun u => weight u • volterraPhysicalShell coordinate u := by
    funext u
    by_cases inside : u ∈ Icc (1 / 4 : ℝ) 4
    · exact indicator_of_mem inside _
    · simp only [indicator_of_notMem inside, volterraPhysicalShell, dif_neg inside, smul_zero]
  exact same ▸ (integrable_indicator_iff measurableSet_Icc).mpr weighted

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
