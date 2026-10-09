import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedRetainer

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedLeftRetained
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


open ActualDressedReaderMatching PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial FullYSourceCutoffVolterra
attribute [local irreducible] retainer cutoff uncutOperator


open ActualDressedRetainer
attribute [local irreducible] jointGenerator

private theorem inverse_commute {A : Type*} [Monoid A] (P K R : A)
    (left : R*K=1) (right : K*R=1) (commutes : P*K=K*P) : P*R=R*P := by
  calc
    P*R=(R*K)*(P*R) := by rw [left,one_mul]
    _=R*(K*P)*R := by simp only [mul_assoc]
    _=R*(P*K)*R := by rw [commutes]
    _=(R*P)*(K*R) := by simp only [mul_assoc]
    _=R*P := by rw [right,mul_one]

/-- The original full cutoff inverse preserves the same scalar retainer on the whole carrier. -/
theorem retainer_finiteFull (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) : Commute (retainer p F) (finiteFull p F cut z) := by
  have shifted : Commute (retainer p F) (compression p F+cutoff cut-z • 1) :=
    ((retainer_compression p F).add_right (retainer_full_cutoff p F cut)).sub_right
      ((Commute.one_right (retainer p F)).smul_right z)
  exact inverse_commute (retainer p F) (compression p F+cutoff cut-z • 1) (finiteFull p F cut z)
    (finiteFull_left p F cut z nonreal) (finiteFull_right p F cut z nonreal) shifted.eq

/-- Uncut support follows from the same original denominator, without a self-adjoint Yukawa assumption. -/
theorem retainer_jointResolvent (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (nonreal : z.im≠0) : Commute (retainer p F) (jointResolvent p F z 0) := by
  have shifted : Commute (retainer p F) (compression p F+uncutOperator 0 (finiteRetainer p F) 0-z • 1) :=
    ((retainer_compression p F).add_right (retainer_uncut p F)).sub_right
      ((Commute.one_right (retainer p F)).smul_right z)
  have actual : Commute (retainer p F) (jointGenerator p F z 0) :=
    (congrArg (fun K : H→L[ℂ]H=>Commute (retainer p F) K) (joint_generator_original p F z)).mpr shifted
  apply inverse_commute (retainer p F) (jointGenerator p F z 0) (jointResolvent p F z 0)
  · unfold jointResolvent
    exact Ring.inverse_mul_cancel (jointGenerator p F z 0) (jointGenerator_unit p F z nonreal)
  · unfold jointResolvent
    exact Ring.mul_inverse_cancel (jointGenerator p F z 0) (jointGenerator_unit p F z nonreal)
  · exact actual.eq

private theorem adjoint_retained (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (R : H→L[ℂ]H) (commutes : Commute (retainer p F) R) (x : H) (support : x∈retainedSpace p F) :
    R.adjoint x∈retainedSpace p F := by
  apply (retainedSpace_iff p F (R.adjoint x)).mpr
  have dual : Commute (retainer p F) R.adjoint := by
    have paid:=congrArg star commutes.eq
    have self : star (retainer p F)=retainer p F :=retainer_selfAdjoint p F
    change retainer p F*R.adjoint=R.adjoint*retainer p F
    simpa only [star_mul,self,ContinuousLinearMap.star_eq_adjoint] using paid.symm
  have paid:=congrArg (fun A : H→L[ℂ]H=>A x) dual.eq
  change retainer p F (R.adjoint x)=R.adjoint (retainer p F x) at paid
  exact paid.trans (congrArg R.adjoint ((retainedSpace_iff p F x).mp support))

/-- Both actual left Riesz representatives are generated inside the original retained subspace. -/
theorem dressed_left_retained (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) :
    (finiteFull p F cut event.energy).adjoint (sourceDressedUnit event.epsilon event.precision)∈retainedSpace p F ∧
    (jointResolvent p F event.energy 0).adjoint (sourceDressedUnit event.epsilon event.precision)∈retainedSpace p F ∧
    (finiteFull p F cut event.energy).adjoint (prepared (sourceProfile event.epsilon event.precision))∈retainedSpace p F ∧
    (jointResolvent p F event.energy 0).adjoint (prepared (sourceProfile event.epsilon event.precision))∈retainedSpace p F := by
  have support:=dressed_original_retained event p F
  exact ⟨adjoint_retained p F (finiteFull p F cut event.energy) (retainer_finiteFull p F cut event.energy event.nonreal)
      (sourceDressedUnit event.epsilon event.precision) support.1,
    adjoint_retained p F (jointResolvent p F event.energy 0) (retainer_jointResolvent p F event.energy event.nonreal)
      (sourceDressedUnit event.epsilon event.precision) support.1,
    adjoint_retained p F (finiteFull p F cut event.energy) (retainer_finiteFull p F cut event.energy event.nonreal)
      (prepared (sourceProfile event.epsilon event.precision)) support.2,
    adjoint_retained p F (jointResolvent p F event.energy 0) (retainer_jointResolvent p F event.energy event.nonreal)
      (prepared (sourceProfile event.epsilon event.precision)) support.2⟩

private theorem retained_left_leak (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (x y : H) (support : x∈retainedSpace p F) :
    inner ℂ x (cutRetainerLeak p F cut y)=0 := by
  change inner ℂ x (retainer p F (cutoff cut y)-cutoff cut y)=0
  rw [inner_sub_right,←retainer_pair p F x (cutoff cut y),(retainedSpace_iff p F x).mp support,sub_self]

private theorem response_left_leak (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (R : H→L[ℂ]H) (x y : H) (support : R.adjoint x∈retainedSpace p F) :
    inner ℂ x (R (cutRetainerLeak p F cut y))=0 := by
  rw [←R.adjoint_inner_left]
  exact retained_left_leak p F cut (R.adjoint x) y support

/-- The original left functional is preserved, with its true weighted Riesz representative; all four actual leak reads vanish by source support. -/
theorem dressed_left_leak_zero (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (y : H) :
    inner ℂ (sourceDressedUnit event.epsilon event.precision) (finiteFull p F cut event.energy (cutRetainerLeak p F cut y))=0 ∧
    inner ℂ (sourceDressedUnit event.epsilon event.precision) (jointResolvent p F event.energy 0 (cutRetainerLeak p F cut y))=0 ∧
    inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (finiteFull p F cut event.energy (cutRetainerLeak p F cut y))=0 ∧
    inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (jointResolvent p F event.energy 0 (cutRetainerLeak p F cut y))=0 := by
  have support:=dressed_left_retained event p F cut
  exact ⟨response_left_leak p F cut (finiteFull p F cut event.energy) (sourceDressedUnit event.epsilon event.precision) y support.1,
    response_left_leak p F cut (jointResolvent p F event.energy 0) (sourceDressedUnit event.epsilon event.precision) y support.2.1,
    response_left_leak p F cut (finiteFull p F cut event.energy) (prepared (sourceProfile event.epsilon event.precision)) y support.2.2.1,
    response_left_leak p F cut (jointResolvent p F event.energy 0) (prepared (sourceProfile event.epsilon event.precision)) y support.2.2.2⟩

end LowEnergy.GaussComposite.ActualDressedLeftRetained
