import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeSoftWardReturn
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeWardFiniteObservation
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance chargedSoftObservableQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

def sourceWindowReader (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) : TransferPair :=
  originalTransferPair (sourceSoftGaussAmplitude (legs 0) branch • nativeBranchVector branch)
    (sourceSoftGaussAmplitude (legs 1) branch • nativeBranchVector branch)

def sourceWindowForce (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) : TransferPair :=
  originalTransferPair (sourceSoftGaussAmplitude (legs 2) branch • nativeBranchVector branch)
    (sourceSoftGaussAmplitude (legs 3) branch • nativeBranchVector branch)

/-- The original complete source pair, before taking an age integral. -/
def sourceWindowScatteringPair (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR
    (sourceWindowReader legs branch) (sourceWindowForce legs branch) 0 time age

def sourceWindowKernel (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) : ℂ :=
  sourceChargedQuantumRead sideL edgeL sideR edgeR
    (sourceSoftNoetherOperator branch (sourceSoftGaussAmplitude (legs 0) branch)
      (sourceSoftGaussAmplitude (legs 1) branch) (sourceSoftGaussAmplitude (legs 2) branch)
      (sourceSoftGaussAmplitude (legs 3) branch) time age)

theorem sourceWindowScatteringPair_read (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) :
    sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch time age=
      (sourceWindowKernel sideL edgeL sideR edgeR legs branch time age,0) :=
  sourceSoftObservable_read branch _ _ _ _ sideL edgeL sideR edgeR time age

theorem sourceWindowKernel_derivative (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) :
    HasDerivAt (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch time)
      (sourceWindowKernel sideL edgeL sideR edgeR legs branch time age) age :=
  sourcePhysicalSoftBoundary_derivative sideL edgeL sideR edgeR legs branch time age

/-- The finite window price is fixed by original four-coordinate source legs and full coefficient norms. -/
def sourceWindowPrice (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time : ℝ) : ℝ :=
  (sourceScatteringGrowth time)^3*
    (sourceScatteringPairDomainPrice sideL edgeL sideR edgeR
      (sourceWindowReader legs branch) (sourceWindowForce legs branch) 0 0 0).1

private theorem growth_window (T r : ℝ) (future : 0 ≤ T) (bounded : |r| ≤ T) :
    sourceScatteringGrowth r ≤ sourceScatteringGrowth T := by
  simp only [sourceScatteringGrowth,sourceRate,abs_of_nonneg future]
  have scaled:=_root_.mul_le_mul_of_nonneg_right bounded (norm_nonneg (operator (interaction actual 0)))
  linarith

private theorem ordered_window (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : Fin 3→ℝ) (T t a : ℝ) (i j : Fin 4)
    (future : 0 ≤ T) (ht : |t| ≤ T) (ha : |a| ≤ T) (hd : |t-a| ≤ T) :
    sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift t a i j ≤
      (sourceScatteringGrowth T)^3*sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift 0 0 i j := by
  have left:=sourceScatteringLegPrice_nonnegative sideL edgeL i
  have right:=sourceScatteringLegPrice_nonnegative sideR edgeR j
  have gt:=growth_window T t future ht
  have ga:=growth_window T a future ha
  have gd:=growth_window T (t-a) future hd
  have positive : 0 ≤ sourceScatteringGrowth T:=by unfold sourceScatteringGrowth sourceRate; positivity
  calc
    _ ≤ sourceScatteringLegPrice sideL edgeL i*
      (sourceScatteringGrowth T*‖shiftCoefficients A shift i‖*sourceScatteringGrowth T*‖B j‖*
        sourceScatteringGrowth T*sourceScatteringLegPrice sideR edgeR j) := by
      unfold sourceOrderedCARPrice sourceOrderedInteriorPrice
      gcongr <;> unfold sourceScatteringGrowth sourceRate <;> positivity
    _=_ := by
      simp only [sourceOrderedCARPrice,sourceOrderedInteriorPrice,sourceScatteringGrowth,abs_zero,
        sub_self,zero_mul,add_zero,one_mul,mul_one]
      ring

/-- The actual complete pair supplies its price; no packet norm or Hamiltonian domain is assumed. -/
theorem sourceWindowKernel_bound (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T age : ℝ)
    (future : 0 ≤ T) (window : age∈Icc 0 T) :
    ‖sourceWindowKernel sideL edgeL sideR edgeR legs branch T age‖ ≤
      sourceWindowPrice sideL edgeL sideR edgeR legs branch T := by
  have actual:=(sourcePreparedScatteringPair_domain_bound sideL edgeL sideR edgeR
    (sourceWindowReader legs branch) (sourceWindowForce legs branch) 0 T age).1
  change ‖(sourceWindowScatteringPair sideL edgeL sideR edgeR legs branch T age).1‖ ≤ _ at actual
  rw [sourceWindowScatteringPair_read] at actual
  refine actual.trans ?_
  have ht : |T| ≤ T:=by rw [abs_of_nonneg future]
  have ha : |age| ≤ T:=by rw [abs_of_nonneg window.1]; exact window.2
  have hd : |T-age| ≤ T:=by rw [abs_of_nonneg (sub_nonneg.mpr window.2)]; linarith [window.1]
  have hd' : |age-T| ≤ T:=by simpa only [abs_sub_comm] using hd
  unfold sourceWindowPrice sourceScatteringPairDomainPrice sourceOrderedSumPrice
  simp only [mul_add,Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_le_sum fun j _=>ordered_window sideL edgeL sideR edgeR _ _ _ T age T i j future ha ht hd'
  · apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_le_sum fun j _=>ordered_window sideL edgeL sideR edgeR _ _ _ T T age i j future ht ha hd

theorem sourceWindowPrice_nonnegative (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) (future : 0 ≤ T) :
    0 ≤ sourceWindowPrice sideL edgeL sideR edgeR legs branch T :=
  (norm_nonneg _).trans (sourceWindowKernel_bound sideL edgeL sideR edgeR legs branch T 0 future ⟨le_rfl,future⟩)

theorem sourceWindowKernel_measurable (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) :
    AEStronglyMeasurable (sourceWindowKernel sideL edgeL sideR edgeR legs branch T) volume := by
  have same : sourceWindowKernel sideL edgeL sideR edgeR legs branch T=
      deriv (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T) :=
    funext fun age=>(sourceWindowKernel_derivative sideL edgeL sideR edgeR legs branch T age).deriv.symm
  rw [same]
  exact aestronglyMeasurable_deriv _ _

theorem sourceWindowKernel_integrable (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) (future : 0 ≤ T) :
    IntervalIntegrable (sourceWindowKernel sideL edgeL sideR edgeR legs branch T) volume 0 T := by
  have price : IntervalIntegrable (fun _ : ℝ=>sourceWindowPrice sideL edgeL sideR edgeR legs branch T) volume 0 T:=
    intervalIntegrable_const
  apply price.mono_fun (sourceWindowKernel_measurable sideL edgeL sideR edgeR legs branch T).restrict
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with age hage
  rw [uIoc_of_le future] at hage
  exact (sourceWindowKernel_bound sideL edgeL sideR edgeR legs branch T age future ⟨hage.1.le,hage.2⟩).trans
    (le_abs_self _)

end LowEnergy.PreparationPhysicalNativeWardFiniteObservation
