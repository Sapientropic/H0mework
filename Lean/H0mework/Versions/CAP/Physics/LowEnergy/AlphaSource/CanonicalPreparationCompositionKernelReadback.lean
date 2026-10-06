import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionMarginal

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionReadback
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumRemainder
open PreparationActualFactor CanonicalPreparationSquareCutoff MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace ComplexConjugate SchwartzMap
attribute [local irreducible] partialFourier symbolSlice b1 weylKernel

theorem originalProductIntegrand_frequency (xi eta q : PhysicalMomentum) :
    actualProductIntegrand xi eta (xi-q)=
      frequencyProductIntegrand 1 (physicalMidpoint xi eta) (q,xi-eta) := by
  have leftShift : physicalMidpoint xi eta+Real.pi • (xi-eta-q)=
      physicalMidpoint xi (xi-q) := by
    simp only [physicalMidpoint,←smul_add]
    congr 1
    abel
  have rightShift : physicalMidpoint xi eta-Real.pi • q=
      physicalMidpoint (xi-q) eta := by
    simp only [physicalMidpoint,←smul_sub]
    congr 1
    abel
  have leftFrequency : xi-(xi-q)=q := by abel
  have rightFrequency : xi-q-eta=xi-eta-q := by abel
  simp only [actualProductIntegrand,weylKernel,frequencyProductIntegrand,one_mul,
    leftShift,rightShift,leftFrequency,rightFrequency]

theorem actualProductKernel_frequency_readback (xi eta : PhysicalMomentum) :
    actualProductKernel xi eta=
      compositionFrequency 1 (physicalMidpoint xi eta) (xi-eta) := by
  rw [compositionFrequency]
  have pointwise : (fun q : PhysicalMomentum =>
      frequencyProductIntegrand 1 (physicalMidpoint xi eta) (q,xi-eta))=
      (fun q => actualProductIntegrand xi eta (xi-q)) := by
    funext q
    exact (originalProductIntegrand_frequency xi eta q).symm
  rw [pointwise,integral_sub_left_eq_self]
  rfl

theorem originalProductFrequency_slice_integrable (xi eta : PhysicalMomentum) :
    Integrable (fun q : PhysicalMomentum =>
      frequencyProductIntegrand 1 (physicalMidpoint xi eta) (q,xi-eta)) := by
  have original := (actualProductIntegrand_integrable xi eta).comp_sub_left xi
  exact original.congr (Eventually.of_forall (originalProductIntegrand_frequency xi eta))

end LowEnergy.PreparationVacuumCompositionReadback
