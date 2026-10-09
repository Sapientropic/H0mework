import H0mework.Versions.V2.Arithmetic.RiemannUnitFourier.Count
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.StepRealization

/-! The existing complete-source recovery gives the actual original L² unit response its finite Dirichlet profile. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
theorem burnolUnitTailResponse_coeFn (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius⁻¹ ≤ 4) :
    (burnolUnitTailResponse coordinate radius : ℝ → ℂ) =ᵐ[volume]
      burnolUnitTailDirichletRaw coordinate.value radius := by
  let source := burnolRadiusNormalizedUnitTail coordinate radius positive
  let value := burnolUnitTailResponse coordinate radius
  have represents : (source : ℝ → ℂ) =ᵐ[volume] burnolRadiusUnitTailRaw coordinate.value radius :=
    burnolRadiusUnitTail_coeFn coordinate radius positive
  have even : reflectL2 source = source :=
    burnolReflectL2_eq_of_even_raw source _ represents (fun x => by simp only [burnolRadiusUnitTailRaw, abs_neg])
  have quarterBound : (1 / 4 : ℝ) ≤ radius := by
    rw [inv_le_comm₀ positive (by norm_num)] at bounded
    norm_num at bounded
    exact bounded
  have gap : (source : ℝ → ℂ) =ᵐ[volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_of_ae represents,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))] with x read inside
    rw [read]
    exact if_neg (not_lt.mpr ((abs_le.mpr inside).trans quarterBound))
  have realization (test : SchwartzMap ℝ ℂ) : burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * value x := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using
      burnolUnitTailResponse_realizes coordinate radius positive bounded test
  obtain ⟨raw, rawRep, _, valueRep⟩ :=
    burnolRemainderSourceRead_realization_ae source value even gap realization
  have same : raw =ᵐ[volume] burnolRadiusUnitTailRaw coordinate.value radius := rawRep.symm.trans represents
  have coSum := burnolInnerGapForward_ae_congr raw (burnolRadiusUnitTailRaw coordinate.value radius) same
  have mean : (∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) =
      -(radius : ℂ) ^ (-coordinate.value) / coordinate.value := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * burnolRadiusUnitTailRaw coordinate.value radius u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae same] with x hx
        rw [hx]
      _ = _ := burnolRadiusUnitTail_reciprocalMean coordinate radius positive
  change (value : ℝ → ℂ) =ᵐ[volume] burnolUnitTailDirichletRaw coordinate.value radius
  filter_upwards [valueRep, coSum] with x valueAt sumAt
  rw [valueAt, sumAt, mean, burnolRadiusUnitTail_finiteCoSum coordinate.value radius x positive]
  unfold burnolUnitTailDirichletRaw
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
