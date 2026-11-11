import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.ShellContinuity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.SourceIntegral

/-! The original shell family generates a physical Pa realization of every even annulus Volterra source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def sourceVolterraPhysical (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) : BurnolPaAmbientCarrier :=
  ∫ u : ℝ in Icc (1 / 4 : ℝ) 4,
    volterraSourceDensity coordinate value u • volterraPhysicalShell coordinate u

theorem sourceVolterraPhysical_integrable
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    IntegrableOn (fun u => volterraSourceDensity coordinate value u •
      volterraPhysicalShell coordinate u) (Icc (1 / 4 : ℝ) 4) :=
  (volterraPhysicalShell_smul_integrable coordinate (volterraSourceDensity coordinate value)
    (volterraSourceDensity_integrableOn coordinate value)).restrict

/-- Closed-range landing is produced by the actual continuous shell synthesis. -/
theorem sourceVolterraPhysical_mem
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceVolterraPhysical coordinate value ∈ burnolCompactCoPoissonClosedRange := by
  apply burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mp
  unfold sourceVolterraPhysical
  rw [← burnolCompactCoPoissonClosedRange.toSubmodule.starProjection.integral_comp_comm
    (sourceVolterraPhysical_integrable coordinate value)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u _
  exact burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr
    (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _
      (volterraPhysicalShell_mem coordinate u))

/-- The original source map reads the synthesized physical state as the actual Volterra window. -/
theorem sourceVolterraPhysical_source
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value = value) (supported : sourceAnnulusCut value = value) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (sourceVolterraPhysical coordinate value)) =
      sourceVolterraWindow coordinate value := by
  let sourceMap : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    burnolTateReciprocalL2.comp burnolMobiusSourceL2
  let family : ℝ → BurnolL2 := fun u => sourceMap
    (volterraSourceDensity coordinate value u • volterraPhysicalShell coordinate u)
  have integrable : IntegrableOn family (Icc (1 / 4 : ℝ) 4) :=
    sourceMap.integrable_comp (sourceVolterraPhysical_integrable coordinate value)
  have raw : ∀ᵐ u ∂volume.restrict (Icc (1 / 4 : ℝ) 4),
      (family u : ℝ → ℂ) =ᵐ[volume] fun t => sourceVolterraBandKernel coordinate value u t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u admitted
    change (sourceMap (volterraSourceDensity coordinate value u •
      volterraPhysicalShell coordinate u) : ℝ → ℂ) =ᵐ[volume] _
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul (volterraSourceDensity coordinate value u)
      (sourceMap (volterraPhysicalShell coordinate u)),
      volterraPhysicalShell_tate_source_raw coordinate u admitted]
        with t scale shell
    change sourceMap (volterraPhysicalShell coordinate u) t = _ at shell
    rw [scale, Pi.smul_apply, smul_eq_mul, shell]
    rfl
  change sourceMap (sourceVolterraPhysical coordinate value) = _
  unfold sourceVolterraPhysical
  rw [← sourceMap.integral_comp_comm (sourceVolterraPhysical_integrable coordinate value)]
  apply Lp.ext
  exact (source_l2_bochner_coeFn (volume.restrict (Icc (1 / 4 : ℝ) 4)) family integrable
    (fun point => sourceVolterraBandKernel coordinate value point.1 point.2)
    (sourceVolterraBandKernel_measurable coordinate value) raw).trans
      (sourceVolterraWindow_band_integral_profile coordinate value even supported).symm

theorem sourceVolterraPhysical_annulus
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    sourceVolterraPhysical coordinate (sourceAnnulusCut value) =
      sourceVolterraPhysical coordinate value := by
  unfold sourceVolterraPhysical
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (sourceAnnulusCut_coeFn value),
    ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (1 / 4 : ℝ))] with u cut inside notQuarter
  have positive : 0 < u := lt_of_lt_of_le (by norm_num) inside.1
  have band : (1 / 4 : ℝ) < |u| ∧ |u| ≤ 4 := by
    rw [abs_of_pos positive]
    exact ⟨lt_of_le_of_ne inside.1 notQuarter.symm, inside.2⟩
  simp only [volterraSourceDensity, cut, if_pos band]

/-- The caller need only supply the original even L² source; its finite face is generated here. -/
theorem sourceVolterraPhysical_source_cut
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value = value) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (sourceVolterraPhysical coordinate value)) =
      sourceVolterraWindow coordinate (sourceAnnulusCut value) := by
  rw [← sourceVolterraPhysical_annulus coordinate value]
  exact sourceVolterraPhysical_source coordinate (sourceAnnulusCut value)
    (sourceAnnulusCut_even value even) (sourceAnnulusCut_idempotent value)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
