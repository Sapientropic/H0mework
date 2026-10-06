import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailActualPreparation
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCompositionOriginalForm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullEnergyForm
open PreparationVacuumTailFourier PreparationVacuumTailSupport PreparationVacuumTailOperator
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumRemainder PreparationVacuumNativeClosure
open PreparationVacuumCompositionNative PreparationVacuumQuadraticForm
open CanonicalPreparationSquareCutoff GaussDensityCore MeasureTheory Filter
open scoped FourierTransform SchwartzMap ComplexConjugate
abbrev ArrayBound := ℕ → ℝ
variable (B : ℕ → Fin 5 → ArrayBound)
variable (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
attribute [local irreducible] tailWeylKernel

def originalTailPair (g f : 𝓢(PhysicalMomentum,ℂ)) (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1)*tailWeylKernel B xy.1 xy.2*f xy.2

theorem actualPair_toLp (g f : 𝓢(PhysicalMomentum,ℂ)) :
    PreparationVacuumTailOperator.actualPair B (g.toLp 2) (f.toLp 2)=ᵐ[volume.prod volume] originalTailPair B g f := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (g.coeFn_toLp 2 volume),
    Measure.quasiMeasurePreserving_snd.ae (f.coeFn_toLp 2 volume)] with xy hg hf
  simp only [PreparationVacuumTailOperator.actualPair,originalTailPair,hg,hf]

include positive input in
theorem originalTailPair_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (originalTailPair B g f) (volume.prod volume) :=
  (PreparationVacuumTailOperator.actualPair_integrable B positive input (g.toLp 2 volume) (f.toLp 2 volume)).congr
    (actualPair_toLp B g f)

def originalTailForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ xy : PhysicalMomentum × PhysicalMomentum,originalTailPair B g f xy ∂volume.prod volume

theorem nativeEnergyTail_original (g f : ScalarTest) :
    inner ℂ (localCore g) (nativeEnergyTail B positive input (localCore f))=
      originalTailForm B (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [nativeEnergyTail_readback,localInput_original,localInput_original]
  simpa only [PreparationVacuumTailOperator.actualPair,originalTailForm] using integral_congr_ae
    (actualPair_toLp B (sourceVacuumInputFrequency (sourceVacuumInputCore g))
      (sourceVacuumInputFrequency (sourceVacuumInputCore f)))

theorem completeNativeRemainder_original (g f : ScalarTest) :
    inner ℂ (localCore g) (completeNativeRemainder B positive input (localCore f))=
      originalTailForm B (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f))-
      originalDefectForm (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [completeNativeRemainder,sub_apply,inner_sub_right,nativeEnergyTail_original,
    sourceNativeComposition_original]

end LowEnergy.PreparationVacuumFullEnergyForm
