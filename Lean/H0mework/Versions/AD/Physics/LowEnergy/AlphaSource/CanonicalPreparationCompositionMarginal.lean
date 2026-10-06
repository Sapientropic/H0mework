import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionKernel
import Mathlib.MeasureTheory.Group.Prod

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionReadback
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder
open PreparationActualFactor CanonicalPreparationSquareCutoff MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

def frequencyProductIntegrand (t : ℝ) (p : PhysicalMomentum)
    (w : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  partialFourier (p+(t*Real.pi) • (w.2-w.1)) w.1 *
    partialFourier (p-(t*Real.pi) • w.1) (w.2-w.1)

theorem frequencyProductIntegrand_shear (t : ℝ) (p : PhysicalMomentum) :
    frequencyProductIntegrand t p=
      compositionIntegrand t 0 p ∘ (fun w : PhysicalMomentum × PhysicalMomentum => (w.1,w.2-w.1)) := by
  funext w
  simp only [frequencyProductIntegrand,compositionIntegrand,Function.comp_apply,
    inner_zero_left,Real.fourierChar.map_zero_eq_one,one_smul]

theorem frequencyProductIntegrand_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (frequencyProductIntegrand t p) := by
  rw [frequencyProductIntegrand_shear]
  exact (compositionIntegrand_measurable t 0 p).comp_measurable
    (continuous_fst.prodMk (continuous_snd.sub continuous_fst)).measurable

theorem frequencyProductIntegrand_integrable (t : ℝ) (p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) :
    Integrable (frequencyProductIntegrand t p) (volume.prod volume) := by
  rw [frequencyProductIntegrand_shear]
  exact (measurePreserving_prod_sub (volume : Measure PhysicalMomentum) volume).integrable_comp_of_integrable
    (compositionIntegrand_integrable t 0 p unitInterval)

def compositionFrequency (t : ℝ) (p k : PhysicalMomentum) : ℂ :=
  ∫ q : PhysicalMomentum,frequencyProductIntegrand t p (q,k)

theorem compositionFrequency_measurable (t : ℝ) (p : PhysicalMomentum) :
    StronglyMeasurable (compositionFrequency t p) :=
  (frequencyProductIntegrand_measurable t p).integral_prod_left'

theorem compositionFrequency_integrable (t : ℝ) (p : PhysicalMomentum)
    (unitInterval : |t| ≤ 1) : Integrable (compositionFrequency t p) :=
  (frequencyProductIntegrand_integrable t p unitInterval).integral_prod_right

end LowEnergy.PreparationVacuumCompositionReadback
