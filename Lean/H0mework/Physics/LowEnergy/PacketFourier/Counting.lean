import H0mework.Physics.LowEnergy.PacketFourier.Centered

/-! Cosine plus sine cancels the same-sign transfers algebraically; neither same-sign covariance is assumed zero. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
open FullQuantum FullSpace PacketNoise PacketDynamics HistoryPrepared
noncomputable section

def oppositeNoise (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) : ℝ :=
  (phaseNoise energy damping positive shift time+phaseNoise energy damping positive (-shift) time)/2

theorem quadrature_noise (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    ‖packetCurrent energy damping positive shift time‖^2+‖sinePacket energy damping positive shift time‖^2=
      oppositeNoise energy damping positive shift time := by
  rw [packet_cosine,packet_sine,norm_smul,norm_smul]
  have cosineNorm : ‖(1/2 : ℂ)‖=(1/2 : ℝ) := by norm_num
  have sineNorm : ‖(2*Complex.I)⁻¹‖=(1/2 : ℝ) := by simp
  rw [cosineNorm,sineNorm]
  have identity := parallelogram_law_with_norm ℂ
    (phasePacket energy damping positive shift time) (phasePacket energy damping positive (-shift) time)
  unfold oppositeNoise phaseNoise
  nlinarith

theorem cosine_noise_le_opposite (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    ‖packetCurrent energy damping positive shift time‖^2 ≤ oppositeNoise energy damping positive shift time := by
  rw [← quadrature_noise]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem original_noise_le_opposite (energy damping : ℝ) (positive : 0 < damping) (shift : Position) :
    packetNoise energy damping positive shift ≤ oppositeNoise energy damping positive shift 0 := by
  have generated := cosine_noise_le_opposite energy damping positive shift 0
  rw [packetCurrent_initial] at generated
  exact generated

theorem oppositeNoise_nonnegative (energy damping : ℝ) (positive : 0 < damping) (shift : Position) (time : ℝ) :
    0 ≤ oppositeNoise energy damping positive shift time := by
  rw [← quadrature_noise]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem oppositeNoise_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (fun pair : Position×ℝ => oppositeNoise energy damping positive pair.1 pair.2) :=
  ((phaseNoise_continuous energy damping positive).add
    ((phaseNoise_continuous energy damping positive).comp
      (continuous_fst.neg.prodMk continuous_snd))).div_const 2

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketFourier
