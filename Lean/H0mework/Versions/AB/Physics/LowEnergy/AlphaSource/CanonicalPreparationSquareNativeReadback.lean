import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSquareWeak
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLocalizedFactor

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumQuadraticForm
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumWeylDomain
open PreparationVacuumWeylOperator PreparationVacuumRemainder PreparationVacuumCompositionReadback
open PreparationVacuumNativeClosure PreparationActualFactor CanonicalPreparationSquareCutoff
open GaussDensityCore MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

def originalFactorPoint (f : ScalarTest) : sourceClosedFactor.domain :=
  ⟨localCore f,localCoreFactor.le_closure.1 (LinearMap.mem_range_self localCore f)⟩

theorem originalFactorPoint_source (f : ScalarTest) :
    (originalFactorPoint f).val=localCore f := rfl

theorem sourceClosedFactor_actual_square (g f : ScalarTest) :
    inner ℂ (sourceClosedFactor (originalFactorPoint g)) (sourceClosedFactor (originalFactorPoint f))=
      squareWeakForm (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [originalFactorPoint,originalFactorPoint,sourceClosedFactor_original,sourceClosedFactor_original]
  exact actualWeylL2_square_pair _ _

theorem squareWeakForm_actual_C1 (g f : 𝓢(PhysicalMomentum,ℂ)) :
    squareWeakForm g f=∫ xy : PhysicalMomentum × PhysicalMomentum,
      conj (g xy.1)*compositionFrequency 1 (physicalMidpoint xy.1 xy.2) (xy.1-xy.2)*f xy.2
        ∂volume.prod volume := by
  rw [squareWeakForm]
  apply integral_congr_ae
  filter_upwards with xy
  rw [squareWeakIntegrand,actualProductKernel_frequency_readback]

theorem sourceClosedFactor_actual_C1 (g f : ScalarTest) :
    inner ℂ (sourceClosedFactor (originalFactorPoint g)) (sourceClosedFactor (originalFactorPoint f))=
      ∫ xy : PhysicalMomentum × PhysicalMomentum,
        conj (sourceVacuumInputFrequency (sourceVacuumInputCore g) xy.1)*
          compositionFrequency 1 (physicalMidpoint xy.1 xy.2) (xy.1-xy.2)*
            sourceVacuumInputFrequency (sourceVacuumInputCore f) xy.2 ∂volume.prod volume := by
  rw [sourceClosedFactor_actual_square,squareWeakForm_actual_C1]

end LowEnergy.PreparationVacuumQuadraticForm
