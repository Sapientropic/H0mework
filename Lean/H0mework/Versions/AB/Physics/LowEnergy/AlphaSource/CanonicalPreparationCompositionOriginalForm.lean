import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionNativeOperator
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSquareNativeReadback

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCompositionNative
open PreparationVacuumCompositionBounded PreparationVacuumFrequencyN2
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumRemainder
open PreparationVacuumNativeClosure PreparationVacuumQuadraticForm
open CanonicalPreparationSquareCutoff GaussDensityCore MeasureTheory Filter
open scoped ComplexConjugate FourierTransform SchwartzMap
attribute [local irreducible] actualFullCompositionKernelDefect

def originalDefectPair (g f : 𝓢(PhysicalMomentum,ℂ))
    (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1)*actualFullCompositionKernelDefect xy.1 xy.2*f xy.2

theorem actualPair_toLp (g f : 𝓢(PhysicalMomentum,ℂ)) :
    actualPair (g.toLp 2) (f.toLp 2)=ᵐ[volume.prod volume] originalDefectPair g f := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (g.coeFn_toLp 2 volume),
    Measure.quasiMeasurePreserving_snd.ae (f.coeFn_toLp 2 volume)] with xy hg hf
  simp only [actualPair,originalDefectPair,hg,hf]

attribute [local irreducible] actualPair originalDefectPair

theorem originalDefectPair_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (originalDefectPair g f) (volume.prod volume) := by
  have original : Integrable (actualPair (g.toLp 2 volume) (f.toLp 2 volume))
      (volume.prod volume) := actualPair_integrable (g.toLp 2 volume) (f.toLp 2 volume)
  exact original.congr (actualPair_toLp g f)

def originalDefectForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ xy : PhysicalMomentum × PhysicalMomentum,originalDefectPair g f xy ∂volume.prod volume

theorem sourceNativeComposition_original (g f : ScalarTest) :
    inner ℂ (localCore g) (sourceNativeComposition (localCore f))=
      originalDefectForm (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [sourceNativeComposition_readback,localInput_original,localInput_original]
  simpa only [actualPair,originalDefectForm] using integral_congr_ae
    (actualPair_toLp (sourceVacuumInputFrequency (sourceVacuumInputCore g))
      (sourceVacuumInputFrequency (sourceVacuumInputCore f)))

theorem sourceSignedComposition_original (g f : ScalarTest) :
    inner ℂ (localCore g) (sourceSignedComposition (localCore f))=
      -originalDefectForm (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [sourceSignedComposition,neg_apply,inner_neg_right,
    sourceNativeComposition_original]

def originalPrincipalPair (g f : 𝓢(PhysicalMomentum,ℂ))
    (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1)*originalPrincipalSquareKernel xy.1 xy.2*f xy.2

theorem originalPrincipalPair_from_actual_square (g f : 𝓢(PhysicalMomentum,ℂ)) :
    originalPrincipalPair g f=squareWeakIntegrand g f-originalDefectPair g f := by
  funext xy
  simp only [originalPrincipalPair,Pi.sub_apply,squareWeakIntegrand,originalDefectPair,
    actualFullCompositionKernelDefect]
  ring

theorem originalPrincipalPair_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (originalPrincipalPair g f) (volume.prod volume) := by
  rw [originalPrincipalPair_from_actual_square]
  exact (squareWeakIntegrand_integrable g f).sub (originalDefectPair_integrable g f)

def originalPrincipalForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ xy : PhysicalMomentum × PhysicalMomentum,originalPrincipalPair g f xy ∂volume.prod volume

theorem originalPrincipalForm_from_actual_square (g f : 𝓢(PhysicalMomentum,ℂ)) :
    originalPrincipalForm g f=squareWeakForm g f-originalDefectForm g f := by
  rw [originalPrincipalForm,originalPrincipalPair_from_actual_square]
  change (∫ xy : PhysicalMomentum × PhysicalMomentum,
    squareWeakIntegrand g f xy-originalDefectPair g f xy ∂volume.prod volume)=_
  rw [integral_sub (squareWeakIntegrand_integrable g f) (originalDefectPair_integrable g f)]
  rfl

theorem sourceFactor_composition_principal_form (g f : ScalarTest) :
    inner ℂ (sourceClosedFactor (originalFactorPoint g)) (sourceClosedFactor (originalFactorPoint f))+
      inner ℂ (localCore g) (sourceSignedComposition (localCore f))=
        originalPrincipalForm (sourceVacuumInputFrequency (sourceVacuumInputCore g))
          (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [sourceClosedFactor_actual_square,sourceSignedComposition_original,
    originalPrincipalForm_from_actual_square]
  rfl

end LowEnergy.PreparationVacuumCompositionNative
