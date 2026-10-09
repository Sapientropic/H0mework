import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationEndpoint

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPreparationEnergy
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore GaussComposite.SourceGraph
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation PreparationChartGuard
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedJointGraph ActualDressedNoether
open GaussComposite.PhysicalEMDressedCharacter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open scoped Topology InnerProductSpace BigOperators Matrix LinearPMap
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourcePreparation sourceProfile
  sourceOperator sourceEnergy sourcePrepared sourceLeg

open PreparationVacuumNoetherOrdinaryWard Filter
local instance : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem inverse_shift {A : Type*} [Ring A] [Algebra ℂ A] (H G : A) (z : ℂ)
    (shift : G=H-z • 1) (unit : IsUnit G) : Ring.inverse G*H=1+z • Ring.inverse G := by
  have same : H=G+z • 1 := by rw [shift];abel
  rw [same,mul_add,Ring.inverse_mul_cancel G unit,mul_smul_comm,mul_one]

/-- This is the original full physical generator and its actual nonreal inverse, not the preparation form operator. -/
theorem preparation_physical_inverse (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) :
    jointResolvent p F z 0*sourceHamiltonian p F=1+z • jointResolvent p F z 0 := by
  apply inverse_shift (sourceHamiltonian p F) (jointGenerator p F z 0) z ?_ (jointGenerator_unit p F z nonreal)
  have zero : (0:ℂ) • (1:H→L[ℂ]H)=0 := by
    apply ContinuousLinearMap.ext
    intro v
    exact zero_smul ℂ v
  simp only [sourceHamiltonian,jointGenerator]
  rw [zero,sub_zero]

private theorem right_kernel_algebra {A : Type*} [Ring A] [Algebra ℂ A]
    (L N R U H : A) (z : ℂ) (time : U*H=H*U) (inverse : R*H=1+z • R) :
    L*N*R*U*H=L*N*U+z • (L*N*R*U) := by
  calc
    _=L*N*(R*H)*U := by simp only [mul_assoc];rw [←time]
    _=_ := by rw [inverse];simp only [mul_add,add_mul,mul_one,mul_smul_comm,smul_mul_assoc]

/-- Only the original right resolvent is removed by its own Green equation. -/
def preparationAmputatedKernel (event : DressedEvent) (transfer : PhysicalMomentum) (reader : Field289) (age : ℝ) : H→L[ℂ]H :=
  physicalTime (event.momentum-transfer) event.frame (-age) 0*
    jointResolvent (event.momentum-transfer) event.frame event.energy 0*
    noetherReader reader event.momentum event.frame 0*physicalTime event.momentum event.frame age 0

theorem preparation_physical_kernel_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedNoetherKernel event transfer reader age 0*sourceHamiltonian event.momentum event.frame=
      preparationAmputatedKernel event transfer reader age+
        event.energy • dressedNoetherKernel event transfer reader age 0 := by
  exact right_kernel_algebra
    (physicalTime (event.momentum-transfer) event.frame (-age) 0*
      jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (noetherReader reader event.momentum event.frame 0)
    (jointResolvent event.momentum event.frame event.energy 0)
    (physicalTime event.momentum event.frame age 0)
    (sourceHamiltonian event.momentum event.frame) event.energy
    (sourceTime_commutes event.momentum event.frame age)
    (preparation_physical_inverse event.momentum event.frame event.energy event.nonreal)

/-- The same actual preparation sees the genuine physical action endpoint as input plus its actual spectral parameter. -/
theorem preparation_physical_boundary (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedEulerObserver event
      (dressedNoetherKernel event transfer reader age 0*sourceHamiltonian event.momentum event.frame)=
    dressedEulerObserver event (preparationAmputatedKernel event transfer reader age)+
      event.energy*dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0) := by
  have generated:=congrArg (dressedEulerObserver event)
    (preparation_physical_kernel_return event transfer reader age)
  simpa only [map_add,map_smul,smul_eq_mul] using generated

/-- The source form energy and the physical action are compared at their real shared endpoint; the exact input and detuning remain. -/
theorem preparation_action_boundary_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    ‖(dressedEulerObserver event
      (dressedNoetherKernel event transfer reader age 0*sourceHamiltonian event.momentum event.frame)-
      preparationNoetherBoundary event transfer reader age 0)-
      (dressedEulerObserver event (preparationAmputatedKernel event transfer reader age)+
        (event.energy-(sourceEnergy:ℂ))*dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0))‖≤
    ‖dressedNoetherKernel event transfer reader age 0‖*(2*‖sourceLeg true 1 0‖+1)*event.epsilon := by
  rw [preparation_physical_boundary]
  have same : (dressedEulerObserver event (preparationAmputatedKernel event transfer reader age)+
      event.energy*dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)-
      preparationNoetherBoundary event transfer reader age 0)-
      (dressedEulerObserver event (preparationAmputatedKernel event transfer reader age)+
        (event.energy-(sourceEnergy:ℂ))*dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0))=
      -(preparationNoetherBoundary event transfer reader age 0-
        (sourceEnergy:ℂ)*dressedEulerObserver event (dressedNoetherKernel event transfer reader age 0)) := by ring
  rw [same,norm_neg]
  exact preparation_noether_boundary_price event transfer reader age 0


/-- Only the existing source preparation accuracy changes; every propagation parameter stays fixed. -/
def preparationEventSequence (event : DressedEvent) (n : ℕ) : DressedEvent :=
  {event with epsilon:=preparationPrecision n,precision:=preparationPrecision_positive n}

private theorem preparation_sequence_kernel (event : DressedEvent) (n : ℕ) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    dressedNoetherKernel (preparationEventSequence event n) transfer reader age 0=
      dressedNoetherKernel event transfer reader age 0 := rfl

private theorem preparation_sequence_amputated (event : DressedEvent) (n : ℕ) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    preparationAmputatedKernel (preparationEventSequence event n) transfer reader age=
      preparationAmputatedKernel event transfer reader age := rfl

/-- The measurable action-endpoint error vanishes along the original residual sequence, without asserting convergence of the selected states. -/
theorem preparation_action_boundary_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader : Field289) (age : ℝ) :
    Tendsto (fun n : ℕ=>
      (dressedEulerObserver (preparationEventSequence event n)
        (dressedNoetherKernel (preparationEventSequence event n) transfer reader age 0*
          sourceHamiltonian event.momentum event.frame)-
        preparationNoetherBoundary (preparationEventSequence event n) transfer reader age 0)-
      (dressedEulerObserver (preparationEventSequence event n) (preparationAmputatedKernel event transfer reader age)+
        (event.energy-(sourceEnergy:ℂ))*dressedEulerObserver (preparationEventSequence event n)
          (dressedNoetherKernel event transfer reader age 0))) Filter.atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have bound (n : ℕ) := preparation_action_boundary_price (preparationEventSequence event n) transfer reader age
  have precision : Tendsto preparationPrecision Filter.atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ=>1/((n:ℝ)+1)) Filter.atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun n=>norm_nonneg _) (fun n=>?_)
    (by simpa only [mul_zero] using
      (precision.const_mul (‖dressedNoetherKernel event transfer reader age 0‖*(2*‖sourceLeg true 1 0‖+1))))
  have paid:=bound n
  simp only [preparation_sequence_kernel event n transfer reader age,
    preparation_sequence_amputated event n transfer reader age] at paid ⊢
  simpa only [preparationEventSequence] using paid

end LowEnergy.GaussComposite.ActualDressedPreparationEnergy
