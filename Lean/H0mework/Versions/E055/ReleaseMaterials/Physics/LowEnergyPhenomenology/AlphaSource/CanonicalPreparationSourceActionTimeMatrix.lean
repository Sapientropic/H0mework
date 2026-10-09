import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationGaugePreparedPorts
import H0mework.Versions.AB.Physics.MotherSource.ActionNormalization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActionUnits
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction
open StageNineCurrentCoframeMatterTemporalPrincipal FullQuantum FullQuantum.CoframeResponse
open FullQuantum.StateGreen PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

def sourceTimeMomentum (e : LorentzianCoframe) : Module.End ℂ DiracExteriorMatterCarrier :=
  (-Complex.I*((|e.det|:ℝ):ℂ)) • currentCoframeMatterTemporalPrincipal e

theorem sourceTimeMomentum_original (C : StageNineHolonomicConfiguration) (x : BasePoint)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (v : DiracExteriorMatterCarrier) :
    normalizedMomentum C x dual v=dual (sourceTimeMomentum (C.coframe x) v) :=by
  simp only [normalizedMomentum,sourceTimeMomentum,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,smul_eq_mul]

theorem sourceTimeMomentum_matrix (s : ActionState) :
    Quantum.operatorMatrix (sourceTimeMomentum s.1)=inversePhase s :=by
  simp only [sourceTimeMomentum,map_smul,inversePhase,stateVolume,principalMatrix]

theorem sourceTimeMomentum_coordinates (s : ActionState)
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier) (v : DiracExteriorMatterCarrier) :
    dual (sourceTimeMomentum s.1 v)=
      ∑i,Quantum.dualCoordinates dual i*(inversePhase s*ᵥ Quantum.coordinates v) i :=by
  rw [Quantum.full_response,sourceTimeMomentum_matrix]

theorem sourcePreparedMomentum_original (x : BasePoint) :
    StageNineMatterPointwiseEquation.matterDifferentialMomentum Stage10.Runtime.source
      Stage10.CanonicalMatter.preparedConfiguration
      (matterCoordinateEquiv ((-Complex.I) • Stage10.CanonicalMatter.preparedConfiguration.matter x)) 0 x=
      Stage10.ActionNormalization.phaseMomentum :=by
  rw [Stage10.CanonicalMatter.prepared_action_time_momentum,
    Stage10.ActionNormalization.phaseMomentum_source]

theorem sourceDensityActionMatrix_momentum :
    densityActionMatrix=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      Quantum.operatorMatrix YangMills.FullPairing.flipMatter :=by
  rw [Stage10.ActionNormalization.phaseMomentum_source]
  simp only [densityActionMatrix,Complex.ofReal_mul,Complex.ofReal_ofNat]

def sourcePreparedTimeMatrix (s : ActionState) : SourceMatrix :=
  densityActionMatrix*Quantum.operatorMatrix (sourceTimeMomentum s.1)

theorem sourcePreparedTimeMatrix_generated (s : ActionState) :
    sourcePreparedTimeMatrix s=(Stage10.ActionNormalization.phaseMomentum:ℂ) •
      (Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s) :=by
  rw [sourcePreparedTimeMatrix,sourceDensityActionMatrix_momentum,sourceTimeMomentum_matrix,
    smul_mul_assoc]

theorem sourcePreparedTimeMatrix_phase_cancel (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0) :
    sourcePreparedTimeMatrix s*statePhase s=densityActionMatrix :=by
  rw [sourcePreparedTimeMatrix,sourceTimeMomentum_matrix,mul_assoc,
    inversePhase_source s nondegenerate regular,mul_one]

theorem sourceActionScale_momentum :
    (Stage10.ActionNormalization.actionScale:ℂ)*(Stage10.ActionNormalization.phaseMomentum:ℂ)=1 :=by
  rw [Stage10.ActionNormalization.actionScale,Complex.ofReal_inv,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne')]

theorem sourcePreparedTimeMatrix_normalized (s : ActionState) :
    (Stage10.ActionNormalization.actionScale:ℂ) • sourcePreparedTimeMatrix s=
      Quantum.operatorMatrix YangMills.FullPairing.flipMatter*inversePhase s :=by
  rw [sourcePreparedTimeMatrix_generated,smul_smul,sourceActionScale_momentum,one_smul]

theorem sourceCompleteLegendre_original (x : BasePoint) :
    HasDerivAt (fun r : ℝ=>StageNineDiracDualFormNativeMotherAction.sourceGeneratedDiracDualFormNativeUnifiedLocalDensity
      Stage10.Runtime.source 0 x
      (StageNineHolonomicField.toContinuumPointField
        (Stage10.StaticHamiltonian.timeStretch Stage10.Runtime.configuration x r) x))
      (Stage10.StaticHamiltonian.ordinaryTimePairing Stage10.Runtime.source Stage10.Runtime.configuration x) 0 :=
  Stage10.StaticHamiltonian.original_time_legendre x

theorem sourceCompleteLegendre_normalized (C : StageNineHolonomicConfiguration)
    (smooth : C.Smooth) (x : BasePoint) :
    Stage10.ActionNormalization.hamiltonian C x=
      Stage10.ActionNormalization.actionScale*Stage10.StaticHamiltonian.hamiltonianDensity Stage10.Runtime.source C x :=
  Stage10.ActionNormalization.source_hamiltonian C smooth x

end LowEnergy.PreparationPhysicalActionUnits
