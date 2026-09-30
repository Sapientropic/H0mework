import H0mework.Physics.LowEnergy.PacketNoise.Readback
import H0mework.Physics.LowEnergy.PacketNoise.GraphContinuity

/-! Overlapping continuum transfers retain their full centered covariance, before any momentum integration. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace HistoryPrepared Stage9DEF
noncomputable section

def covarianceObservable (energy damping : ℝ) (positive : 0 < damping) (left right : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (centeredFilter energy damping positive left).adjoint.comp
    (centeredFilter energy damping positive right)

def packetCovariance (energy damping : ℝ) (positive : 0 < damping) (left right : Position) : ℂ :=
  inner ℂ (centeredFilter energy damping positive left preparedPacket)
    (centeredFilter energy damping positive right preparedPacket)

theorem covariance_source_read (energy damping : ℝ) (positive : 0 < damping) (left right : Position) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (covarianceObservable energy damping positive left right)))=
        packetCovariance energy damping positive left right := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((centeredFilter energy damping positive left).adjoint
    (centeredFilter energy damping positive right preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem packetCovariance_diagonal (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    packetCovariance energy damping positive transfer transfer=(packetNoise energy damping positive transfer : ℂ) := by
  rw [packetCovariance,inner_self_eq_norm_sq_to_K]
  simp only [packetNoise,Complex.ofReal_pow]
  rfl

theorem packetCovariance_conj (energy damping : ℝ) (positive : 0 < damping) (left right : Position) :
    star (packetCovariance energy damping positive left right)=packetCovariance energy damping positive right left :=
  inner_conj_symm _ _

theorem packetCovariance_gram (energy damping : ℝ) (positive : 0 < damping)
    {ι : Type*} (indices : Finset ι) (transfers : ι → Position) (coefficients : ι → ℂ) :
    (∑ i ∈ indices, ∑ j ∈ indices,
      star (coefficients i)*coefficients j*packetCovariance energy damping positive (transfers i) (transfers j))=
      (‖∑ i ∈ indices, coefficients i • centeredFilter energy damping positive (transfers i) preparedPacket‖ : ℂ)^2 := by
  calc
    _ = inner ℂ
        (∑ i ∈ indices, coefficients i • centeredFilter energy damping positive (transfers i) preparedPacket)
        (∑ i ∈ indices, coefficients i • centeredFilter energy damping positive (transfers i) preparedPacket) := by
      simp only [sum_inner,inner_smul_left]
      simp only [inner_sum,inner_smul_right,packetCovariance,Finset.mul_sum,mul_assoc]
      rfl
    _ = _ := inner_self_eq_norm_sq_to_K _

theorem packetMean_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (packetMean energy damping positive) :=
  continuous_const.inner (currentFilter_continuous energy damping positive preparedPacket)

theorem centeredFilter_continuous (energy damping : ℝ) (positive : 0 < damping) (input : FullMatterL2) :
    Continuous (fun transfer => centeredFilter energy damping positive transfer input) := by
  change Continuous (fun transfer => currentFilter energy damping positive transfer input-
    packetMean energy damping positive transfer • sourceFilter energy damping positive input)
  exact (currentFilter_continuous energy damping positive input).sub
    ((packetMean_continuous energy damping positive).smul continuous_const)

theorem packetNoise_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (packetNoise energy damping positive) :=
  ((centeredFilter_continuous energy damping positive preparedPacket).norm).pow 2

theorem packetCovariance_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (fun pair : Position×Position => packetCovariance energy damping positive pair.1 pair.2) :=
  ((centeredFilter_continuous energy damping positive preparedPacket).comp continuous_fst).inner
    ((centeredFilter_continuous energy damping positive preparedPacket).comp continuous_snd)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
