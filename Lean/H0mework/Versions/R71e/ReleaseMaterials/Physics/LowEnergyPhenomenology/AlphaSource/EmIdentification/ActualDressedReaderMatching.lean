import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderComponents
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCutReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherAction

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedReaderMatching
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent


open ActualDressedReaderComponents ActualDressedCutReturn ActualDressedNoether
open CanonicalPhysicalYResolvent
attribute [local irreducible] currentVertex currentRestriction temporalReaderCompensation noetherReader
  jointResolvent dressedEulerObserver

private theorem sandwich_splice {A : Type*} [Ring A] (J N C Lc Rc Lu Ru Dl Dr : A)
    (reader : J= -N+C) (left : Lc=Lu+Lc*Dl*Lu) (right : Rc=Ru+Rc*Dr*Ru) :
    Lc*J*Rc= -(Lu*N*Ru)+(Lc*C*Rc-Lc*Dl*Lu*N*Rc-Lu*N*Rc*Dr*Ru) := by
  have l : Lc*N*Rc=Lu*N*Rc+Lc*Dl*Lu*N*Rc := by
    have paid:=congrArg (fun X : A=>X*N*Rc) left
    simpa only [add_mul,mul_assoc] using paid
  have r : Lu*N*Rc=Lu*N*Ru+Lu*N*Rc*Dr*Ru := by
    have paid:=congrArg (fun X : A=>Lu*N*X) right
    simpa only [mul_add,mul_assoc] using paid
  calc
    Lc*J*Rc= -(Lc*N*Rc)+Lc*C*Rc := by
      simp only [reader,mul_add,add_mul,mul_neg,neg_mul]
    _= -(Lu*N*Rc+Lc*Dl*Lu*N*Rc)+Lc*C*Rc :=
      congrArg (fun X : A=> -X+Lc*C*Rc) l
    _= -(Lu*N*Ru+Lu*N*Rc*Dr*Ru+Lc*Dl*Lu*N*Rc)+Lc*C*Rc :=
      congrArg (fun X : A=> -(X+Lc*Dl*Lu*N*Rc)+Lc*C*Rc) r
    _=_ := by simp only [neg_add,sub_eq_add_neg];abel

/-- Original full field sectors and both actual cut/uncut Yukawa tails; the left term retains its complete right cut response. -/
def temporalCutCompensation (a : Fin 12) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) : H→L[ℂ]H :=
  finiteFull (p+k) F cut z*temporalReaderCompensation a p F*finiteFull p F cut w-
    finiteFull (p+k) F cut z*(cutJetError (p+k) F cut+cutRetainerLeak (p+k) F cut)*
      jointResolvent (p+k) F z 0*noetherReader (temporalField a) p F 0*finiteFull p F cut w-
    jointResolvent (p+k) F z 0*noetherReader (temporalField a) p F 0*finiteFull p F cut w*
      (cutJetError p F cut+cutRetainerLeak p F cut)*jointResolvent p F w 0

/-- The Coulomb full-field vertex and original uncut temporal Noether sandwich share one original source event, with all generated compensations retained. -/
theorem temporal_cut_noether_match (a : Fin 12) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0) :
    currentVertex (temporalField a) p k F cut z w=
      -(jointResolvent (p+k) F z 0*noetherReader (temporalField a) p F 0*jointResolvent p F w 0)+
        temporalCutCompensation a p k F cut z w := by
  unfold currentVertex temporalCutCompensation
  exact sandwich_splice (currentRestriction (temporalField a) p F 0) (noetherReader (temporalField a) p F 0)
    (temporalReaderCompensation a p F) (finiteFull (p+k) F cut z) (finiteFull p F cut w)
    (jointResolvent (p+k) F z 0) (jointResolvent p F w 0)
    (cutJetError (p+k) F cut+cutRetainerLeak (p+k) F cut) (cutJetError p F cut+cutRetainerLeak p F cut)
    (temporal_reader_generated a p F) (cut_resolvent_return (p+k) F cut z hz) (cut_resolvent_return p F cut w hw)

/-- This is exactly the root's actual unit-minus-background Euler observer, not a new preparation. -/
theorem dressed_temporal_cut_noether (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) :
    dressedEulerObserver event
        (currentVertex (temporalField a) event.momentum (-transfer) event.frame event.cut event.energy event.energy)=
      -dressedEulerObserver event
        (dressedNoetherKernel event transfer (temporalField a) 0 0)+
      dressedEulerObserver event
        (temporalCutCompensation a event.momentum (-transfer) event.frame event.cut event.energy event.energy) := by
  have paid:=congrArg (dressedEulerObserver event)
    (temporal_cut_noether_match a event.momentum (-transfer) event.frame event.cut event.energy event.energy
      event.nonreal event.nonreal)
  simpa only [dressedNoetherKernel,neg_zero,physicalTime_initial,one_mul,mul_one,sub_eq_add_neg,map_add,map_neg] using paid

private theorem vertex_coordinates (f : Field289) (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z w : ℂ) (x y : H) :
    inner ℂ x (currentVertex f p k F cut z w y)=
      ∑i : Fin 289,(f i:ℂ)*inner ℂ x (currentVertex (fieldBasis i) p k F cut z w y) := by
  simp only [currentVertex_original_pair]
  exact field_first_coordinates f p
    (sourceTestApprox F ((finiteFull (p+k) F cut z).adjoint x))
    (sourceTestApprox F (finiteFull p F cut w y))

private theorem dressed_current_euler (event : DressedEvent) (transfer : PhysicalMomentum) (f : Field289) :
    (∑i : Fin 289,(f i:ℂ)*dressedCurrent event transfer i)=
      -dressedEulerObserver event
        (currentVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy) := by
  have unit:=vertex_coordinates f event.momentum (-transfer) event.frame event.cut event.energy event.energy
    (sourceDressedUnit event.epsilon event.precision) (sourceDressedUnit event.epsilon event.precision)
  have background:=vertex_coordinates f event.momentum (-transfer) event.frame event.cut event.energy event.energy
    (prepared (sourceProfile event.epsilon event.precision)) (prepared (sourceProfile event.epsilon event.precision))
  have coordinates:=congrArg₂ (fun u v : ℂ=>u-v) unit background
  have source : (∑i : Fin 289,(f i:ℂ)*dressedCurrent event transfer i)=
      inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (currentVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (sourceDressedUnit event.epsilon event.precision))-
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (currentVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (prepared (sourceProfile event.epsilon event.precision))) := by
    simpa only [dressedCurrent,sourceDressedConnectedCurrent,sourceDressedCurrent,mul_sub,Finset.sum_sub_distrib]
      using coordinates.symm
  have observed:=dressed_euler_observer_original event
    (currentVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy)
  linear_combination source+observed

/-- The existing whole-289 dressed Coulomb current consumes the root's same actual nonlinear Noether kernel at its original temporal origin. -/
theorem dressed_temporal_coulomb_match (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) :
    (∑i : Fin 289,(temporalField a i:ℂ)*dressedCurrent event transfer i)=
      dressedEulerObserver event (dressedNoetherKernel event transfer (temporalField a) 0 0)-
        dressedEulerObserver event
          (temporalCutCompensation a event.momentum (-transfer) event.frame event.cut event.energy event.energy) := by
  have source:=dressed_current_euler event transfer (temporalField a)
  have target:=dressed_temporal_cut_noether event transfer a
  linear_combination source-target

open PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa PreparationVacuumPreparedCurrent
open PreparationVacuumLocalizedYukawa PreparationVacuumSourcePreparedState ActualDressedJointGraph

/-- Retainer support is generated by the unchanged actual creation and original prepared background. -/
theorem dressed_original_retained (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    sourceDressedUnit event.epsilon event.precision∈retainedSpace p F ∧
      prepared (sourceProfile event.epsilon event.precision)∈retainedSpace p F := by
  constructor
  · rw [source_dressed_unit_original]
    exact (retainedSpace p F).smul_mem _
      (profileLeg_retained event.epsilon event.precision p F (sourceDressedAddition event.epsilon event.precision) 1 0)
  · rw [source_profile_original_domain event]
    exact sourceCarrier_retained p F (sourcePrepared_mem (sourcePreparation event.epsilon event.precision).point.val)

private theorem original_uncut_retained (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) (x : H) (support : x∈retainedSpace p F) :
    jointResolvent p F z 0 x∈retainedSpace p F := by
  rw [jointResolvent_zero (0:Field289) p F z]
  exact sourceResolvent_retained 0 p F none z
    (by intro h;apply nonreal;rw [h];rfl) 0
    (movingDiagonal_units (0:Field289) p F z nonreal).self_of_nhds x support

/-- The right localization leak really vanishes on both original uncut responses of this same prepared event. -/
theorem dressed_original_right_leak (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) :
    cutRetainerLeak p F cut (jointResolvent p F event.energy 0 (sourceDressedUnit event.epsilon event.precision))=0 ∧
      cutRetainerLeak p F cut (jointResolvent p F event.energy 0 (prepared (sourceProfile event.epsilon event.precision)))=0 := by
  have support:=dressed_original_retained event p F
  exact ⟨cut_retainer_leak_retained p F cut _
      (original_uncut_retained p F event.energy event.nonreal (sourceDressedUnit event.epsilon event.precision) support.1),
    cut_retainer_leak_retained p F cut _
      (original_uncut_retained p F event.energy event.nonreal (prepared (sourceProfile event.epsilon event.precision)) support.2)⟩

end LowEnergy.GaussComposite.ActualDressedReaderMatching
