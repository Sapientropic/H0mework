import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussBoundedMultiplier

/-! The normalized source Yukawa is bounded on the actual full Gauss100 Hilbert space. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussYukawaOperator
open GaussCoreHilbert GaussCoreDifferential GaussYukawaCoefficient GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open GaussUnitaryHistory (HistorySpace inclusion reader)
open scoped ContDiff

def bounded : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension normalized (fun _ => normalized_smooth.contDiffAt)
    (fun z => normalized_commutes z) bound bound_nonneg (fun z => normalized_bound z)

theorem bounded_core (f : QuantumTest) : bounded (embed f) = embed (GaussYukawaCoefficient.action f) :=
  GaussBoundedMultiplier.extension_core normalized (fun _ => normalized_smooth.contDiffAt)
    (fun z => normalized_commutes z) bound bound_nonneg (fun z => normalized_bound z) f

theorem bounded_norm : ‖bounded‖ ≤ bound :=
  GaussBoundedMultiplier.extension_norm normalized (fun _ => normalized_smooth.contDiffAt)
    (fun z => normalized_commutes z) bound bound_nonneg (fun z => normalized_bound z)

theorem bounded_preserves_core (x : Core) : bounded (x : H) ∈ Core := by
  obtain ⟨f,hf⟩ := embed_surjective_core x
  rw [← hf, bounded_core]
  exact embed_mem_core _

def originalAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => sourceMap (scalarField z))
    (fun _ => (sourceMap.contDiff.comp scalarField_smooth).contDiffAt)

def radiusAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => radius z • (ContinuousLinearMap.id ℂ FockFiber))
    (fun _ => radius_smooth.contDiffAt.smul contDiffAt_const)

theorem radius_action_return (f : QuantumTest) :
    radiusAction (GaussYukawaCoefficient.action f) = originalAction f := by
  apply DFunLike.ext
  intro z
  change radius z • normalized z (f z) = sourceMap (scalarField z) (f z)
  exact congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z)) (radius_return z)

def originalY : H →ₗ.[ℂ] H := realize originalAction
def radial : H →ₗ.[ℂ] H := realize radiusAction

theorem originalY_factor (f : QuantumTest) :
    originalY (coreEquiv f) = radial ⟨bounded (embed f), bounded_preserves_core (coreEquiv f)⟩ := by
  have hx : (⟨bounded (embed f), bounded_preserves_core (coreEquiv f)⟩ : Core) =
      coreEquiv (GaussYukawaCoefficient.action f) := Subtype.ext (bounded_core f)
  erw [hx]
  change embed (originalAction (coreEquiv.symm (coreEquiv f))) =
    embed (radiusAction (coreEquiv.symm (coreEquiv (GaussYukawaCoefficient.action f))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply, radius_action_return]

def common : HistorySpace →L[ℂ] HistorySpace := reader bounded

theorem common_core (f : QuantumTest) :
    common (inclusion (embed f)) = inclusion (embed (GaussYukawaCoefficient.action f)) := by
  change reader bounded (inclusion (embed f)) = _
  rw [GaussUnitaryHistory.reader_inclusion, bounded_core]

#print axioms bounded_core
#print axioms bounded_norm
#print axioms originalY_factor
#print axioms common_core
end LowEnergy.GaussYukawaOperator
