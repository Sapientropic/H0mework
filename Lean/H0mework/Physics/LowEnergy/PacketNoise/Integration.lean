import H0mework.Physics.LowEnergy.PacketNoise.Kernel
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Finite Fourier bands consume the true continuum covariance. Weighted probes retain every cross momentum term. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace HistoryPrepared Stage9DEF
noncomputable section

theorem packetNoise_integrable (energy damping : ℝ) (positive : 0 < damping) (radius : ℝ) :
    IntegrableOn (packetNoise energy damping positive) (Metric.closedBall 0 radius) volume :=
  (packetNoise_continuous energy damping positive).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 radius)

def noiseMass (energy damping : ℝ) (positive : 0 < damping) (radius : ℝ) : ℝ :=
  ∫ transfer in Metric.closedBall 0 radius, packetNoise energy damping positive transfer

theorem noiseMass_nonnegative (energy damping : ℝ) (positive : 0 < damping) (radius : ℝ) :
    0 ≤ noiseMass energy damping positive radius :=
  integral_nonneg (packetNoise_nonnegative energy damping positive)

def weightedPacket (energy damping : ℝ) (positive : 0 < damping) (profile : C(Position,ℂ))
    (transfer : Position) : FullMatterL2 :=
  profile transfer • centeredFilter energy damping positive transfer preparedPacket

theorem weightedPacket_integrable (energy damping : ℝ) (positive : 0 < damping)
    (profile : C(Position,ℂ)) (radius : ℝ) :
    IntegrableOn (weightedPacket energy damping positive profile) (Metric.closedBall 0 radius) volume :=
  (profile.continuous.smul (centeredFilter_continuous energy damping positive preparedPacket)).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 radius)

def probeResponse (energy damping : ℝ) (positive : 0 < damping) (profile : C(Position,ℂ)) (radius : ℝ) :
    FullMatterL2 :=
  ∫ transfer in Metric.closedBall 0 radius, weightedPacket energy damping positive profile transfer

theorem weightedPacket_inner (energy damping : ℝ) (positive : 0 < damping) (profile : C(Position,ℂ))
    (left right : Position) :
    star (profile left)*profile right*packetCovariance energy damping positive left right=
      inner ℂ (weightedPacket energy damping positive profile left)
        (weightedPacket energy damping positive profile right) := by
  simp only [weightedPacket,inner_smul_left,inner_smul_right,packetCovariance,mul_assoc]
  change (starRingEnd ℂ) (profile left)*(profile right*_)=
    profile right*((starRingEnd ℂ) (profile left)*_)
  ring

theorem integral_inner_left {α : Type*} [MeasurableSpace α] {measure : Measure α}
    {field : α → FullMatterL2} (integrable : Integrable field measure) (right : FullMatterL2) :
    (∫ x, inner ℂ (field x) right ∂measure)=inner ℂ (∫ x, field x ∂measure) right := by
  calc
    _ = ∫ x, (starRingEnd ℂ) (inner ℂ right (field x)) ∂measure := by simp only [inner_conj_symm]
    _ = (starRingEnd ℂ) (∫ x, inner ℂ right (field x) ∂measure) := integral_conj
    _ = _ := by rw [integral_inner integrable,inner_conj_symm]

theorem probeResponse_covariance (energy damping : ℝ) (positive : 0 < damping)
    (profile : C(Position,ℂ)) (radius : ℝ) :
    (∫ left in Metric.closedBall 0 radius, ∫ right in Metric.closedBall 0 radius,
      star (profile left)*profile right*packetCovariance energy damping positive left right)=
        (‖probeResponse energy damping positive profile radius‖ : ℂ)^2 := by
  simp_rw [weightedPacket_inner]
  simp_rw [integral_inner (weightedPacket_integrable energy damping positive profile radius)]
  rw [integral_inner_left (weightedPacket_integrable energy damping positive profile radius)]
  exact inner_self_eq_norm_sq_to_K _

theorem probeResponse_source_read (energy damping : ℝ) (positive : 0 < damping)
    (profile : C(Position,ℂ)) (radius : ℝ) :
    (∫ left in Metric.closedBall 0 radius, ∫ right in Metric.closedBall 0 radius,
      star (profile left)*profile right*
        State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
          (Compatibility.responseMatrix (sourceMother
            (covarianceObservable energy damping positive left right))))=
        (‖probeResponse energy damping positive profile radius‖ : ℂ)^2 := by
  simp_rw [covariance_source_read]
  exact probeResponse_covariance energy damping positive profile radius

def physicalTransfer (momentum : Position) : Position := (2*Real.pi)⁻¹ • momentum

theorem physicalTransfer_correct (momentum : Position) (j : Fin 3) :
    physicalMomentum (physicalTransfer momentum) j=momentum j := by
  change 2*Real.pi*((2*Real.pi)⁻¹*momentum j)=momentum j
  field_simp [Real.pi_ne_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
