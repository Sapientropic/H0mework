import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Family.ClozelBurnolCompactAnnulusEulerFamily
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Synthesis.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.RecipeInverse
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalPaPhysicalGreen
open scoped Topology SchwartzMap

def inverseSource (c : BurnolCompletedMellinCoordinate) (source : burnolCompactAnnulusSource) :
    burnolCompactAnnulusSource :=
  (1/2 : ℂ) • CompactSourceEuler.sourceEuler source - (c.value/2-1/4) • source

theorem inverseSource_apply (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    (inverseSource c source).1 x =
      (1/2 : ℂ) * ((x : ℂ) * deriv source.1 x + (1-c.value)*source.1 x) := by
  change (1/2 : ℂ) * CompactSourceEuler.rawEuler source.1 x -
    (c.value/2-1/4)*source.1 x = _
  rw [CompactSourceEuler.rawEuler_apply]
  ring

private def primitive (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (1-c.value) * source.1 x

private theorem primitive_hasDerivAt (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1/4 : ℝ) 4) :
    HasDerivAt (primitive c source)
      (burnolFirstSourceDensity c (inverseSource c source) t) t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have exponent : (1 : ℂ)-c.value ≠ 0 := by
    intro zero
    have same : c.value = 1 := (sub_eq_zero.mp zero).symm
    have bound := c.belowOne
    rw [same] at bound
    norm_num at bound
  have power := hasDerivAt_ofReal_cpow_const positive.ne' exponent
  have generated := power.mul (source.1.hasDerivAt t)
  have shift : (1 : ℂ)-c.value-1 = -c.value := by ring
  have scalar : (t : ℂ) ^ (1-c.value) = (t : ℂ)*(t : ℂ)^(-c.value) := by
    symm
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
  have value :
      (1-c.value)*(t : ℂ)^(1-c.value-1)*source.1 t +
        (t : ℂ)^(1-c.value)*deriv source.1 t =
          burnolFirstSourceDensity c (inverseSource c source) t := by
    rw [shift, scalar]
    unfold burnolFirstSourceDensity
    rw [max_eq_right (show (1/8 : ℝ) ≤ t by linarith [inside.1]), inverseSource_apply]
    ring
  exact generated.congr_deriv value

/-- The original recipe and its Euler derivative generate the exact inverse coefficient. -/
theorem firstSourceCoefficient_inverse (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1/4 : ℝ) 4) :
    burnolFirstSourceCoefficient c (inverseSource c source) t = 2*source.1 t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have derivative := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t) (b := (4 : ℝ))
    (fun x member => primitive_hasDerivAt c source (show x ∈ Icc (1/4 : ℝ) 4 from by
      rw [uIcc_of_le inside.2] at member
      exact ⟨inside.1.trans member.1, member.2⟩))
    ((burnolFirstSourceDensity_continuous c (inverseSource c source)).intervalIntegrable t 4)
  have outer : primitive c source 4 = 0 := by
    unfold primitive
    rw [source.2.2.2 4 (by norm_num), mul_zero]
  rw [outer, zero_sub] at derivative
  unfold burnolFirstSourceCoefficient
  rw [max_eq_right (show (1/8 : ℝ) ≤ t by linarith [inside.1]), derivative]
  unfold primitive
  have powers : (t : ℂ)^(c.value-1)*(t : ℂ)^(1-c.value) = 1 := by
    rw [← Complex.cpow_add _ _ nonzero]
    convert Complex.cpow_zero (t : ℂ) using 1
    congr 1
    ring
  calc
    _ = (2 : ℂ) * ((t : ℂ)^(c.value-1)*(t : ℂ)^(1-c.value))*source.1 t := by ring
    _ = _ := by rw [powers]; ring

private theorem compact_mem (source : burnolCompactAnnulusSource) :
    burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
  simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
    burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))

theorem compact_source_even (source : burnolCompactAnnulusSource) :
    reflectL2 (source.1.toLp 2 volume) = source.1.toLp 2 volume := by
  have paid := original_tate_source_even (burnolCompactAdditivePhysicalState source)
  rw [burnolCompactPa_tate_source] at paid
  exact paid

theorem compact_source_supported (source : burnolCompactAnnulusSource) :
    sourceAnnulusCut (source.1.toLp 2 volume) = source.1.toLp 2 volume := by
  have paid := sourceAnnulusCut_original_pa (burnolCompactAdditivePhysicalState source)
    (compact_mem source)
  rw [burnolCompactPa_tate_source] at paid
  exact paid

private theorem correction_source_inverse (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection c
      ⟨burnolCompactAdditivePhysicalState (inverseSource c source),
        compact_mem (inverseSource c source)⟩)) = source.1.toLp 2 volume := by
  apply Lp.ext
  filter_upwards [burnolPaSourceCorrection_compact_tate c (inverseSource c source),
    source.1.coeFn_toLp 2 volume] with x profile read
  rw [profile, read]
  by_cases band : (1/4 : ℝ) ≤ |x| ∧ |x| < 4
  · rw [if_pos band, firstSourceCoefficient_inverse c source ⟨band.1,band.2.le⟩]
    have even : source.1 |x| = source.1 x := by
      rcases le_total 0 x with positive | negative
      · rw [abs_of_nonneg positive]
      · rw [abs_of_nonpos negative, source.2.1]
    rw [even]
    ring
  · rw [if_neg band]
    rcases lt_or_ge |x| (1/4 : ℝ) with inner | exterior
    · exact (source.2.2.1 x inner.le).symm
    · exact (source.2.2.2 x (le_of_not_gt (fun below => band ⟨exterior,below⟩))).symm

/-- The Euler-generated input lands at the original physical source, without a range premise. -/
theorem sourceVolterraPhysical_inverse (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    sourceVolterraPhysical c ((inverseSource c source).1.toLp 2 volume) =
      burnolCompactAdditivePhysicalState source := by
  have paid := sourceVolterraPhysical_original_correction c
    (burnolCompactAdditivePhysicalState (inverseSource c source)) (compact_mem _)
  rw [burnolCompactPa_tate_source] at paid
  rw [paid]
  apply original_pa_tate_source_injective _ _ (burnolPaSourceCorrection_mem c _) (compact_mem source)
  rw [correction_source_inverse, burnolCompactPa_tate_source]

/-- The same physical inverse retains the literal annulus source face. -/
theorem sourceVolterraWindow_inverse (c : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    sourceVolterraWindow c ((inverseSource c source).1.toLp 2 volume) =
      source.1.toLp 2 volume := by
  have paid := sourceVolterraPhysical_source c ((inverseSource c source).1.toLp 2 volume)
    (compact_source_even _) (compact_source_supported _)
  rw [sourceVolterraPhysical_inverse, burnolCompactPa_tate_source] at paid
  exact paid.symm

end OriginalRSourceJointContact.RecipeInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
