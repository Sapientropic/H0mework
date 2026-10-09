import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderMatching

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedRetainer
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

private theorem original_dense_pair (T : H→L[ℂ]H)
    (core : ∀a b : QuantumTest,inner ℂ (T (embed a)) (embed b)=inner ℂ (embed a) (T (embed b)))
    (x y : H) : inner ℂ (T x) y=inner ℂ x (T y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  have ea : (a:H)=embed (GaussCoreHilbert.coreEquiv.symm a) :=
    (congrArg Subtype.val (GaussCoreHilbert.coreEquiv.apply_symm_apply a)).symm
  have eb : (b:H)=embed (GaussCoreHilbert.coreEquiv.symm b) :=
    (congrArg Subtype.val (GaussCoreHilbert.coreEquiv.apply_symm_apply b)).symm
  change inner ℂ (T (a:H)) (b:H)=inner ℂ (a:H) (T (b:H))
  rw [ea,eb]
  exact core (GaussCoreHilbert.coreEquiv.symm a) (GaussCoreHilbert.coreEquiv.symm b)

/-- The original finite retainer is a real scalar multiplier in the same weighted Gauss Hilbert pairing. -/
theorem retainer_pair (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x y : H) :
    inner ℂ (retainer p F x) y=inner ℂ x (retainer p F y) := by
  apply original_dense_pair (retainer p F) _ x y
  intro a b
  rw [retainer_core p F a,retainer_core p F b]
  have same : retainTest p F=GaussNativeForm.multiply (finiteRetainer p F)
      (fun z=>(finiteRetainer p F).contDiff.contDiffAt) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    rfl
  change sourcePair (retainTest p F a) b=sourcePair a (retainTest p F b)
  rw [same]
  exact (GaussNativeForm.multiply_pair (finiteRetainer p F)
    (fun z=>(finiteRetainer p F).contDiff.contDiffAt) a b).symm

theorem retainer_selfAdjoint (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : IsSelfAdjoint (retainer p F) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact retainer_pair p F

theorem retainer_adjoint (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (retainer p F).adjoint=retainer p F := by
  exact retainer_selfAdjoint p F

/-- Compression is the original source assembly supported where the retainer equals one. -/
theorem retainer_compression (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute (retainer p F) (compression p F) := by
  have left : retainer p F*compression p F=compression p F := by
    have paid:=retainer_assembly p F
      (fun i j=>transportedForm 0 p (bareTest p F i) (bareTest p F j) 0)
    change retainer p F*transportedCompression 0 p F 0=transportedCompression 0 p F 0 at paid
    simpa only [transportedCompression_zero (0:Field289) p F] using paid
  have hp : star (retainer p F)=retainer p F :=retainer_selfAdjoint p F
  have hc : star (compression p F)=compression p F :=compression_selfAdjoint p F
  have right : compression p F*retainer p F=compression p F := by
    simpa only [star_mul,hp,hc] using congrArg star left
  exact left.trans right.symm

/-- The original full cutoff commutes with the same scalar retainer, before any support restriction. -/
theorem retainer_full_cutoff (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) :
    Commute (retainer p F) (cutoff cut) := by
  simpa only [fieldCutoff_zero (0:Field289) cut] using retainer_cutoff (0:Field289) cut p F (0:ℝ)

theorem retainer_uncut (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Commute (retainer p F) (uncutOperator 0 (finiteRetainer p F) 0) := by
  apply GaussYukawaGrade.core_ext
  intro a
  change retainer p F (uncutOperator 0 (finiteRetainer p F) 0 (embed a))=
    uncutOperator 0 (finiteRetainer p F) 0 (retainer p F (embed a))
  rw [uncutOperator_core,retainer_core,retainer_core,uncutOperator_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (finiteRetainer p F z:ℂ) • (compactFiber 0 (finiteRetainer p F) (0,z) (a z))=
    compactFiber 0 (finiteRetainer p F) (0,z) ((finiteRetainer p F z:ℂ) • a z)
  exact (map_smul _ _ _).symm

end LowEnergy.GaussComposite.ActualDressedRetainer
