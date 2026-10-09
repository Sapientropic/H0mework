import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszCanonicalRaw
import H0mework.Versions.V2.Arithmetic.BurnolPhysical.L2DirectDilation
import H0mework.Versions.V2.Arithmetic.MellinProjection.PaBoundaryCommutator

/-! # Actual signed dilation of the canonical Riesz raw state -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory
noncomputable section

def burnolRieszDilationRaw (coordinate : BurnolCompletedMellinCoordinate)
    (shift x : ℝ) : ℂ :=
  (Real.exp (shift / 2) : ℂ) * burnolRieszStateRaw coordinate (Real.exp shift * x)

theorem burnolRieszDilation_ae_raw (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) :
      ℝ → ℂ) =ᵐ[volume] burnolRieszDilationRaw coordinate shift := by
  have scale : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  filter_upwards [burnolMultiplicativeDilation_coeFn shift
      (burnolCompletedMellinRieszVector coordinate : BurnolL2),
    scale.ae (burnolRieszState_ae_raw coordinate)] with x dilation source
  rw [dilation]
  change (Real.exp (shift / 2) : ℂ) *
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) (Real.exp shift * x) = _
  rw [source]
  rfl

def burnolRieszPairedDilationRaw (coordinate : BurnolCompletedMellinCoordinate)
    (shift x : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (burnolRieszDilationRaw coordinate shift x + burnolRieszDilationRaw coordinate (-shift) x)

theorem burnolRieszPairedDilation_ae_raw (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (pairedBurnolMultiplicativeDilation shift
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) : ℝ → ℂ) =ᵐ[volume]
      burnolRieszPairedDilationRaw coordinate shift := by
  let first := burnolMultiplicativeDilation shift
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  let second := burnolMultiplicativeDilation (-shift)
    (burnolCompletedMellinRieszVector coordinate : BurnolL2)
  change (((1 / 2 : ℂ) • (first + second) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (first + second),
    Lp.coeFn_add first second, burnolRieszDilation_ae_raw coordinate shift,
    burnolRieszDilation_ae_raw coordinate (-shift)] with x hs ha hf hi
  rw [hs]
  change (1 / 2 : ℂ) * (first + second : BurnolL2) x = _
  rw [ha]
  change (1 / 2 : ℂ) * (first x + second x) = _
  change first x = _ at hf
  change second x = _ at hi
  rw [hf, hi]
  rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
