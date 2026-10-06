import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFullEnergyCoreReadback

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullEnergyForm
open PreparationVacuumTailFourier PreparationVacuumTailSupport PreparationVacuumTailOperator PreparationVacuumWholeTail
open PreparationVacuumWeyl PreparationVacuumWeylDomain PreparationVacuumRemainder PreparationVacuumNativeClosure
open PreparationVacuumCompositionNative PreparationVacuumQuadraticForm PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff GaussDensityCore MeasureTheory Filter
open SaturationMonoid.Quantum.Forms
open scoped FourierTransform SchwartzMap ComplexConjugate LinearPMap RealInnerProductSpace
variable (B : ℕ → Fin 5 → ArrayBound)
variable (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102)
attribute [local irreducible] tailWeylKernel originalPrincipalSquareKernel

def completeEnergySymbol (x : PreparationVacuumCanonicalMoyal.Phase) : ℝ := b1 x^2+energyTailFor B x

def completeEnergyKernel (xi eta : PhysicalMomentum) : ℂ :=
  ∫ x : PhysicalMomentum,𝐞 (-⟪x,xi-eta⟫) •
    (completeEnergySymbol B (flatPosition x,physicalMidpoint xi eta) : ℂ)

theorem completeEnergyKernel_split (xi eta : PhysicalMomentum) :
    completeEnergyKernel B xi eta=originalPrincipalSquareKernel xi eta+tailWeylKernel B xi eta := by
  have tailIntegrable : Integrable (fun x : PhysicalMomentum=>𝐞 (-⟪x,xi-eta⟫) •
      (energyTailFor B (flatPosition x,physicalMidpoint xi eta) : ℂ)) :=
    (Real.fourierIntegral_convergent_iff (xi-eta)).mpr (tailSlice_integrable B (physicalMidpoint xi eta))
  rw [completeEnergyKernel,originalPrincipalSquareKernel_literal,tailWeylKernel,tailPartialFourier]
  change (∫ x : PhysicalMomentum,𝐞 (-⟪x,xi-eta⟫) •
    (completeEnergySymbol B (flatPosition x,physicalMidpoint xi eta) : ℂ))=_
  simp only [completeEnergySymbol,Complex.ofReal_add,Complex.ofReal_pow,smul_add]
  rw [integral_add (originalPrincipalSquareKernel_integrable xi eta) tailIntegrable]
  rfl

def completeEnergyPair (g f : 𝓢(PhysicalMomentum,ℂ)) (xy : PhysicalMomentum × PhysicalMomentum) : ℂ :=
  conj (g xy.1)*completeEnergyKernel B xy.1 xy.2*f xy.2

theorem completeEnergyPair_split (g f : 𝓢(PhysicalMomentum,ℂ)) :
    completeEnergyPair B g f=originalPrincipalPair g f+originalTailPair B g f := by
  funext xy
  rw [Pi.add_apply,completeEnergyPair,completeEnergyKernel_split,originalPrincipalPair,originalTailPair]
  ring

include positive input in
theorem completeEnergyPair_integrable (g f : 𝓢(PhysicalMomentum,ℂ)) :
    Integrable (completeEnergyPair B g f) (volume.prod volume) := by
  rw [completeEnergyPair_split]
  exact (originalPrincipalPair_integrable g f).add (originalTailPair_integrable B positive input g f)

def completeEnergyForm (g f : 𝓢(PhysicalMomentum,ℂ)) : ℂ :=
  ∫ xy : PhysicalMomentum × PhysicalMomentum,completeEnergyPair B g f xy ∂volume.prod volume

include positive input in
theorem completeEnergyForm_split (g f : 𝓢(PhysicalMomentum,ℂ)) :
    completeEnergyForm B g f=originalPrincipalForm g f+originalTailForm B g f := by
  rw [completeEnergyForm,completeEnergyPair_split]
  simp only [Pi.add_apply]
  rw [integral_add (originalPrincipalPair_integrable g f) (originalTailPair_integrable B positive input g f)]
  rfl

theorem actual_closed_form_complete_energy (g f : ScalarTest) :
    BoundedRemainder.form sourceClosedFactor (completeNativeRemainder B positive input)
      (originalFactorPoint g) (originalFactorPoint f)=
      completeEnergyForm B (sourceVacuumInputFrequency (sourceVacuumInputCore g))
        (sourceVacuumInputFrequency (sourceVacuumInputCore f)) := by
  rw [BoundedRemainder.form,originalFactorPoint_source,originalFactorPoint_source,
    sourceClosedFactor_actual_square,completeNativeRemainder_original,
    completeEnergyForm_split B positive input,originalPrincipalForm_from_actual_square]
  ring

end LowEnergy.PreparationVacuumFullEnergyForm
