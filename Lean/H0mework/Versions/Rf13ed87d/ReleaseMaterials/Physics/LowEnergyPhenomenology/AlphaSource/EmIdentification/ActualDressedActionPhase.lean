import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceResponse
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussActionTimeReturn
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMPoleWard

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedActionPhase
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

/-- The original canonical momentum inverse is applied on both actual independent branches. -/
def canonicalPhaseNormalizer (s : ActionState) : FullMatrix :=
  SourceRealScalarFock.branches (sourceCanonicalMomentumInverse s)

private theorem branches_real_smul (r : ℝ) (M : SourceMatrix) :
    SourceRealScalarFock.branches ((r:ℂ) • M)=(r:ℂ) • SourceRealScalarFock.branches M := by
  ext u v
  cases u <;> cases v <;> simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply]

private theorem branches_cancel (A B : SourceMatrix) (unit : A*B=1) :
    SourceRealScalarFock.branches A*SourceRealScalarFock.branches B=1 := by
  have conjugate : A.map (starRingEnd ℂ)*B.map (starRingEnd ℂ)=1 := by
    rw [←Matrix.map_mul,unit]
    ext i j
    simp [Matrix.map_apply,Matrix.one_apply]
  simp only [SourceRealScalarFock.branches,Matrix.fromBlocks_multiply,
    Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,neg_mul_neg,unit]
  ext u v
  cases u <;> cases v <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  all_goals simpa only [Matrix.one_apply] using congrFun (congrFun conjugate _) _

theorem canonical_phase_time_weight (s : ActionState) (valid : s∈validStates) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) • sourceTimeWeight s)=1 := by
  rw [canonicalPhaseNormalizer,sourceTimeWeight,←branches_real_smul]
  exact branches_cancel _ _ (sourceCanonicalMomentumInverse_generated s valid.1 valid.2)

/-- The physical EM time-current symbol is generated from the original action variation and original temporal momentum weight. -/
theorem original_em_noether_symbol (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    rawActionSymbol (emGaugeField 0) p s=sourceTimeWeight s*emGaugeChargeMatrix := by
  rw [rawActionSymbol_source _ p s valid,←sourceNormalizedEnergySymbol_original p s _ valid,
    em_voltage_symbol p s valid]
  rw [sourceTimeWeight_original]
  simp only [mul_neg,smul_neg,neg_smul,smul_mul_assoc]
  module

/-- The raw action coupling contains the same original phase momentum and its entire source time-weight matrix. -/
theorem original_em_noether_phase (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    rawActionSymbol (emGaugeField 0) p s=
      (Stage10.ActionNormalization.phaseMomentum:ℂ) •
        (SourceRealScalarFock.branches
          (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s)*emGaugeChargeMatrix) := by
  rw [original_em_noether_symbol p s valid,sourceTimeWeight,sourcePreparedTimeMatrix_generated,
    branches_real_smul,smul_mul_assoc]

/-- The same phase/momentum normalization sends the actual raw temporal EM action coefficient to the original full504 charge matrix. -/
theorem canonical_phase_em_noether (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (emGaugeField 0) p s)=
      emGaugeChargeMatrix := by
  rw [original_em_noether_symbol p s valid,←smul_mul_assoc,←mul_assoc,canonical_phase_time_weight s valid,one_mul]

theorem canonical_phase_hamiltonian (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergySymbol p s)=
      fourierLinear p (stateHamiltonian s) := by
  rw [originalEnergySymbol_generated p s valid.2]
  change canonicalPhaseNormalizer s*((Stage10.ActionNormalization.actionScale:ℂ) •
    (sourceTimeWeight s*fourierLinear p (stateHamiltonian s)))=_
  rw [←smul_mul_assoc,←mul_assoc,canonical_phase_time_weight s valid,one_mul]

/-- Full CAR quantization keeps its original pair correction; the created N2 state is not replaced by an N1 collapse. -/
theorem canonical_em_quantized_return (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    quantized emGaugeChargeMatrix=
      quantized (canonicalPhaseNormalizer s)*
          quantized ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (emGaugeField 0) p s)-
        pairFiber (canonicalPhaseNormalizer s)
          ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (emGaugeField 0) p s) := by
  have paid:=quantized_normal_order (canonicalPhaseNormalizer s)
    ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (emGaugeField 0) p s)
  rw [canonical_phase_em_noether p s valid] at paid
  exact eq_sub_of_add_eq paid.symm

theorem canonical_energy_quantized_return (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    quantized (fourierLinear p (stateHamiltonian s))=
      quantized (canonicalPhaseNormalizer s)*
          quantized ((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergySymbol p s)-
        pairFiber (canonicalPhaseNormalizer s)
          ((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergySymbol p s) := by
  have paid:=quantized_normal_order (canonicalPhaseNormalizer s)
    ((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergySymbol p s)
  rw [canonical_phase_hamiltonian p s valid] at paid
  exact eq_sub_of_add_eq paid.symm

theorem em_noether_matrix_same : emGaugeChargeMatrix=chargeMatrix sourcePhaseGaugeLie := by
  have primal : emCanonicalChargeMatrix=Complex.I • nativePrimal sourcePhaseGaugeLie := by
    rw [emCanonicalChargeMatrix,map_smul,←em_phase_gauge_action,sourcePhaseGaugeGenerator_native]
  rw [emGaugeChargeMatrix]
  change SourceRealScalarFock.branches emCanonicalChargeMatrix=chargeMatrix sourcePhaseGaugeLie
  rw [primal]
  unfold chargeMatrix nativeFull
  ext i j
  cases i <;> cases j <;>
    simp [SourceRealScalarFock.branches,Matrix.fromBlocks,Matrix.smul_apply,Matrix.map_apply]

/-- The actual propagated unit test consumes the same original-action Noether normalization before quantization, with the full pair correction retained. -/
theorem dressed_original_noether_phase (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z : ℂ) (x : physicalChart) :
    chargeAction sourcePhaseGaugeLie
        (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
          (sourceDressedResponse epsilon precision p F cut z)) x.val=
      quantized (canonicalPhaseNormalizer (sourceState x.val))
          (quantized ((Stage10.ActionNormalization.actionScale:ℂ) •
              rawActionSymbol (emGaugeField 0) p (sourceState x.val))
            (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
              (sourceDressedResponse epsilon precision p F cut z) x.val))-
        pairFiber (canonicalPhaseNormalizer (sourceState x.val))
          ((Stage10.ActionNormalization.actionScale:ℂ) • rawActionSymbol (emGaugeField 0) p (sourceState x.val))
          (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
            (sourceDressedResponse epsilon precision p F cut z) x.val) := by
  change quantized (chargeMatrix sourcePhaseGaugeLie) _=_
  rw [←em_noether_matrix_same]
  exact congrArg (fun A : FockFiber→L[ℂ]FockFiber=>A
    (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
      (sourceDressedResponse epsilon precision p F cut z) x.val))
    (canonical_em_quantized_return p (sourceState x.val) (sourceState_valid x))

/-- The actual dressed unit response consumes the complete action phase return, including original weight, pair, compression and uncut-retainer defects. -/
theorem dressed_action_phase_return (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (cut : ℕ) (z w : ℂ) :
    (Stage10.ActionNormalization.actionScale:ℂ)*sourceDensityEnergyRead p
        (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
          ((CanonicalPhysicalYResolvent.finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (PreparationVacuumFieldConstraintResponse.sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w))=
      inner ℂ
        (embed (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
          ((CanonicalPhysicalYResolvent.finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision))))
        ((PreparationVacuumPhysicalHalfAxis.actualC p F+PreparationVacuumPhysicalHalfAxis.actualA p F)
          (embed (PreparationVacuumFieldConstraintResponse.sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w))))+
      sourceActualUnitDefect p F
        (PreparationVacuumFieldConstraintResponse.sourceTestApprox F
          ((CanonicalPhysicalYResolvent.finiteFull (p+k) F cut z).adjoint (sourceDressedUnit epsilon precision)))
        (PreparationVacuumFieldConstraintResponse.sourceTestApprox F (sourceDressedResponse epsilon precision p F cut w)) := by
  exact sourceDensityEnergyRead_actual_time p F _ _

end LowEnergy.GaussComposite.ActualDressedActionPhase
