import H0mework.Physics.LowEnergy.PacketNoise.Response

/-! Actual continuum means and centered Gram weights return through the unchanged source preparation and Stage10 reader. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace HistoryPrepared Stage9DEF
noncomputable section

def packetMean (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) : ℂ :=
  inner ℂ (filteredPacket energy damping positive)
    (currentFilter energy damping positive transfer preparedPacket)

theorem packetMean_current (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    packetMean energy damping positive transfer=currentMean transfer (preparedDomain energy damping positive) := by
  rw [packetMean,currentFilter_prepared]
  rfl

theorem packetMean_real (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    star (packetMean energy damping positive transfer)=packetMean energy damping positive transfer := by
  rw [packetMean_current]
  exact currentMean_real _ _

def meanObservable (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (sourceFilter energy damping positive).adjoint.comp (currentFilter energy damping positive transfer)

theorem mean_source_read (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (meanObservable energy damping positive transfer)))=
        packetMean energy damping positive transfer := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((sourceFilter energy damping positive).adjoint
    (currentFilter energy damping positive transfer preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

def centeredFilter (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  currentFilter energy damping positive transfer-
    packetMean energy damping positive transfer • sourceFilter energy damping positive

theorem centeredFilter_original (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    centeredFilter energy damping positive transfer preparedPacket=
      currentField transfer (preparedDomain energy damping positive)-
        packetMean energy damping positive transfer • filteredPacket energy damping positive := by
  change currentFilter energy damping positive transfer preparedPacket-
    packetMean energy damping positive transfer • filteredPacket energy damping positive=_
  rw [currentFilter_prepared]

theorem centeredFilter_orthogonal (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    inner ℂ (filteredPacket energy damping positive)
      (centeredFilter energy damping positive transfer preparedPacket)=0 := by
  have unit : inner ℂ (filteredPacket energy damping positive) (filteredPacket energy damping positive)=1 :=
    inner_self_eq_one_of_norm_eq_one (filteredPacket_unit energy damping positive)
  change inner ℂ (filteredPacket energy damping positive)
    (currentFilter energy damping positive transfer preparedPacket-
      packetMean energy damping positive transfer • filteredPacket energy damping positive)=0
  rw [inner_sub_right,inner_smul_right,unit,mul_one]
  exact sub_self _

def packetNoise (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) : ℝ :=
  ‖centeredFilter energy damping positive transfer preparedPacket‖^2

def noiseObservable (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  (centeredFilter energy damping positive transfer).adjoint.comp
    (centeredFilter energy damping positive transfer)

theorem noise_source_read (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Compatibility.responseMatrix (sourceMother (noiseObservable energy damping positive transfer)))=
        (packetNoise energy damping positive transfer : ℂ) := by
  rw [sourceMother_read]
  change inner ℂ preparedPacket ((centeredFilter energy damping positive transfer).adjoint
    (centeredFilter energy damping positive transfer preparedPacket))=_
  rw [ContinuousLinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  simp only [packetNoise,Complex.ofReal_pow]
  rfl

theorem packetNoise_actual (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    packetNoise energy damping positive transfer=
      ‖currentField transfer (preparedDomain energy damping positive)-
        packetMean energy damping positive transfer • filteredPacket energy damping positive‖^2 := by
  rw [packetNoise,centeredFilter_original]

theorem packetNoise_nonnegative (energy damping : ℝ) (positive : 0 < damping) (transfer : Position) :
    0 ≤ packetNoise energy damping positive transfer := sq_nonneg _

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
