import H0mework.Versions.Y.Arithmetic.RieszResponse.ResponseRead
import H0mework.Versions.Y.Arithmetic.RieszSourceKernel.Generated

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteResponse

open Complex FourierTransform MeasureTheory
open scoped FourierTransform Topology
open OriginalRieszSource
noncomputable section

def sourceRead (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) : ℂ :=
  (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) :
    TemperedDistribution ℝ ℂ) test

def forcingRead (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) : ℂ :=
  Kernel.A coordinate * Response.Psi (coPoissonSchwartzEnergyTranslation (-shift) test) +
    Kernel.beta coordinate * (𝓕 Response.Psi) (coPoissonSchwartzEnergyTranslation (-shift) test)

theorem forcing_readback (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    forcingRead coordinate test shift =
      GapEuler.euler
        (burnolMultiplicativeDilation shift (burnolCompletedMellinRieszVector coordinate : BurnolL2) :
          TemperedDistribution ℝ ℂ) test +
      (star coordinate.value - 1 / 2) * sourceRead coordinate test shift := by
  have generated := congrArg (fun value : TemperedDistribution ℝ ℂ =>
    value (coPoissonSchwartzEnergyTranslation (-shift) test)) (Kernel.original_kernel_euler coordinate)
  simp only [add_apply, smul_apply, smul_eq_mul] at generated
  rw [original_euler_action, sourceRead, original_read]
  exact generated.symm

theorem source_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    HasDerivAt (sourceRead coordinate test)
      (forcingRead coordinate test shift -
        (star coordinate.value - 1 / 2) * sourceRead coordinate test shift) shift := by
  have native := Dilation.original_weak_derivative
    (burnolCompletedMellinRieszVector coordinate : BurnolL2) test shift
  change HasDerivAt (sourceRead coordinate test) _ shift at native
  rw [forcing_readback, add_sub_cancel_right]
  exact native

theorem sourceRead_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) : Continuous (sourceRead coordinate test) := by
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  exact read.continuous.comp
    (burnolMultiplicativeDilation_stronglyContinuous
      (burnolCompletedMellinRieszVector coordinate : BurnolL2))

theorem forcingRead_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (test : SchwartzMap ℝ ℂ) : Continuous (forcingRead coordinate test) := by
  let cotest := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
    (SchwartzMap.derivCLM ℂ ℂ test)
  have base := sourceRead_continuous coordinate test
  have moment := sourceRead_continuous coordinate cotest
  have continuous : Continuous (fun shift : ℝ =>
      -(1 / 2 : ℂ) * sourceRead coordinate test shift - sourceRead coordinate cotest shift +
        (star coordinate.value - 1 / 2) * sourceRead coordinate test shift) :=
    ((continuous_const.mul base).sub moment).add (continuous_const.mul base)
  apply continuous.congr
  intro shift
  rw [forcing_readback, Dilation.euler_test]
  rfl

end
end OriginalRieszFiniteResponse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
