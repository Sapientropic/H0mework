import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.WholePairing
import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.Flux

/-! The actual compact fixed source reads the complete window used by the Pa Ward. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem compact_inPa (source : burnolCompactAnnulusSource) :
    burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
  simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
    burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))

theorem sourceSecondWindow_compact_profile (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) = burnolCompactAdditivePhysicalState source) :
    (sourceSecondWindow coordinate ⟨burnolCompactAdditivePhysicalState source, compact_inPa source⟩ : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (1 / 4 : ℝ) 4)] secondCoefficient coordinate source := by
  have profile := (ae_restrict_iff' measurableSet_Ioo).mp
    (sourceSecondWindow_contact_profile coordinate (burnolCompactAdditivePhysicalState source)
      (compact_inPa source))
  filter_upwards [ae_restrict_of_ae profile, ae_restrict_of_ae (volume.ae_ne (4 : ℝ)),
    ae_restrict_mem measurableSet_Ioc] with t read different ht
  have openRange : t ∈ Ioo (1 / 4 : ℝ) 4 := ⟨ht.1, lt_of_le_of_ne ht.2 different⟩
  have positive : 0 < t := lt_trans (by norm_num) ht.1
  rw [read openRange, dif_pos positive]
  exact secondContact_compact coordinate source fixed ⟨ht.1.le, ht.2⟩

theorem sourceSecondWindow_compact_integrals (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) = burnolCompactAdditivePhysicalState source) :
    let J := sourceSecondWindow coordinate
      ⟨burnolCompactAdditivePhysicalState source, compact_inPa source⟩
    contactIntegral J = (∫ t : ℝ in (1 / 4)..4, secondCoefficient coordinate source t) ∧
    contactReciprocalIntegral J =
      (∫ t : ℝ in (1 / 4)..4, secondCoefficient coordinate source t / (t : ℂ)) := by
  intro J
  have profile := sourceSecondWindow_compact_profile coordinate source fixed
  constructor
  · rw [contactIntegral_eq_integral]
    apply intervalIntegral.integral_congr_ae_restrict
    simpa only [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)] using profile
  · rw [contactReciprocalIntegral_eq_integral]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)]
    filter_upwards [profile] with t read
    rw [read]

theorem originalFiniteContactKernel_compact_read {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2 * (k + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (N : ℕ)
    (source : burnolCompactAnnulusSource) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    let W : BurnolL2 := (one +
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius one : BurnolPaAmbientCarrier)
    contactBilinearRead (originalFiniteContactKernel observation nontrivial rightHalf N)
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source))) =
      ∫ t : ℝ in (1 / 4)..4, source.1 t *
        ((∑ n ∈ Finset.range N, burnolTateReciprocalL2 (burnolAnnulusSamplingL2 W n) t) -
          ((1 / 2 : ℂ) * ∫ x : ℝ, W x)) := by
  intro one W
  rw [burnolCompactPa_tate_source, contactBilinearRead_eq_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)]
  filter_upwards [ae_restrict_of_ae (source.1.coeFn_toLp 2 volume),
    originalFiniteContactKernel_coeFn observation nontrivial rightHalf N] with t read kernel
  rw [read, kernel]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
