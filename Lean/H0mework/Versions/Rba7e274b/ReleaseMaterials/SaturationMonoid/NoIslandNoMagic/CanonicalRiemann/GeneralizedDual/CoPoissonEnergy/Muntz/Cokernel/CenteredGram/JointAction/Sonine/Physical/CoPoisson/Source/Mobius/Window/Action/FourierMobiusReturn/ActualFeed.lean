import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.RawReturn
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.Primitive
import Mathlib.MeasureTheory.Measure.Prod
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalFourierMobiusReturnSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open OriginalRieszSource

def actualFourierReturnTimeRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  -(∫ tau : ℝ in Ioi 0,Complex.exp ((-star coordinate.value/2)*(tau:ℂ))*
    generatedFourierMobiusRaw coordinate (Real.exp (-tau/2)*x))

 theorem generated_fourier_mobius_measurable (coordinate : BurnolCompletedMellinCoordinate) : Measurable (generatedFourierMobiusRaw coordinate) := by
  unfold generatedFourierMobiusRaw
  apply Measurable.indicator _ (measurableSet_symmetricInterval 4)
  exact ((finite_edge_continuous.const_mul _).sub
    (Complex.continuous_ofReal.mul (finite_source_derivative_continuous coordinate))).sub
      ((finite_source_continuous coordinate).const_mul (star coordinate.value)) |>.sub continuous_const |>.measurable

-- The actual source input replaces the complete R time kernel by the same finite generated word.
theorem actual_R_fourier_source_feed (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolDirectRightResolvent (star coordinate.value/2)
      (Paid.M (fourierL2 (C.wholeContactResponse coordinate))):ℝ→ℂ)=ᵐ[volume] actualFourierReturnTimeRaw coordinate := by
  let value := Paid.M (fourierL2 (C.wholeContactResponse coordinate))
  have sections : ∀ᵐ tau : ℝ ∂volume.restrict (Ioi 0),∀ᵐ x : ℝ ∂volume,
      value (Real.exp (-tau/2)*x)=generatedFourierMobiusRaw coordinate (Real.exp (-tau/2)*x) := by
    filter_upwards with tau
    exact (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ)) (r:=Real.exp (-tau/2))
      (Real.exp_ne_zero _)).ae_eq (actual_fourier_mobius_source coordinate)
  have measured : MeasurableSet {p : ℝ×ℝ |
      value (Real.exp (-p.1/2)*p.2)=generatedFourierMobiusRaw coordinate (Real.exp (-p.1/2)*p.2)} :=
    measurableSet_eq_fun ((Lp.stronglyMeasurable value).measurable.comp (by fun_prop))
      ((generated_fourier_mobius_measurable coordinate).comp (by fun_prop))
  have swapped := (Measure.ae_ae_comm measured).mp sections
  filter_upwards [original_R_raw coordinate value,swapped] with x actual same
  rw [actual]
  unfold actualReturnTimeRaw actualFourierReturnTimeRaw
  congr 1
  apply integral_congr_ae
  filter_upwards [same] with tau read
  rw [read]

end OriginalFourierMobiusReturnSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
