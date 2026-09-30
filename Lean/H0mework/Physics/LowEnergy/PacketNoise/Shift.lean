import H0mework.Physics.LowEnergy.FullQuantum.SpatialWeak.Symbol
import H0mework.Physics.LowEnergy.FullQuantum.HistoryPrepared.Source
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! A physical plane-wave transfer acts on the same whole L² carrier by a genuine Fourier translation. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen SpatialWeak YangMills.FullPairing
noncomputable section

def frequencyShift (shift : Position) : FullMatterL2 →ₗᵢ[ℂ] FullMatterL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun frequency : Position => frequency-shift)
    (measurePreserving_sub_right volume shift)

theorem frequencyShift_ae (shift : Position) (field : FullMatterL2) :
    frequencyShift shift field =ᵐ[volume] fun frequency => field (frequency-shift) :=
  Lp.coeFn_compMeasurePreserving field (measurePreserving_sub_right volume shift)

def phaseShift (shift : Position) : FullMatterL2 →ₗᵢ[ℂ] FullMatterL2 :=
  fourier.symm.toLinearIsometry.comp ((frequencyShift shift).comp fourier.toLinearIsometry)

theorem phaseShift_fourier (shift : Position) (field : FullMatterL2) :
    fourier (phaseShift shift field)=frequencyShift shift (fourier field) := fourier.apply_symm_apply _

theorem phaseShift_norm (shift : Position) (field : FullMatterL2) : ‖phaseShift shift field‖=‖field‖ :=
  (phaseShift shift).norm_map field

def shiftSymbol (point : ProofFreeRicherAnholonomicSource.BasePoint) (shift : Position) : FiberOperators :=
  ∑ j, ((physicalMomentum shift j : ℝ) : ℂ) • spatial point j

theorem symbol_shift (point : ProofFreeRicherAnholonomicSource.BasePoint) (energy damping : ℝ)
    (frequency shift : Position) :
    symbol point energy damping frequency=
      symbol point energy damping (frequency-shift)-shiftSymbol point shift := by
  rw [symbol_affine,symbol_affine,shiftSymbol]
  have momentum (j : Fin 3) : physicalMomentum (frequency-shift) j=
      physicalMomentum frequency j-physicalMomentum shift j := by
    simp only [physicalMomentum,PiLp.sub_apply]
    ring
  have moved : (∑ j, (physicalMomentum (frequency-shift) j : ℂ) • spatial point j)=
      (∑ j, (physicalMomentum frequency j : ℂ) • spatial point j)-
        (∑ j, (physicalMomentum shift j : ℂ) • spatial point j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [momentum,Complex.ofReal_sub]
    exact _root_.sub_smul (R := ℂ) (M := FiberOperators)
      (physicalMomentum frequency j : ℂ) (physicalMomentum shift j : ℂ) (spatial point j)
  rw [moved]
  abel

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
