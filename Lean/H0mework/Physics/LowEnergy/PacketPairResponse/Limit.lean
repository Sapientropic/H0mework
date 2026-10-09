import H0mework.Physics.LowEnergy.PacketPairResponse.Integral

/-! The finite physical-band response has its source-generated leading
coefficient as a true punctured-time limit, after the momentum integral. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
open Filter Topology PacketFourier
noncomputable section
attribute [local irreducible] bandSlopeResponse bandLeading

theorem bandResponse_limit (energy damping : ℝ) (positive : 0 < damping) :
    Tendsto (fun time : ℝ => bandResponse energy damping positive time/time^2) (𝓝[≠] 0)
      (𝓝 (bandLeading energy damping positive)) := by
  have generated := (bandSlopeResponse_continuous energy damping positive).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (0 : ℝ)≤𝓝 0 from inf_le_left)
  rw [bandSlopeResponse_initial] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with time member
  have nonzero : time≠0 := by simpa using member
  rw [bandResponse_slope]
  field_simp

theorem bandResponse_initial (energy damping : ℝ) (positive : 0 < damping) :
    bandResponse energy damping positive 0=0 := by
  rw [bandResponse_slope]
  simp only [zero_pow (by decide : (2 : ℕ)≠0),zero_mul]

theorem bandResponse_continuous (energy damping : ℝ) (positive : 0 < damping) :
    Continuous (bandResponse energy damping positive) := by
  have generated := (continuous_pow 2).mul (bandSlopeResponse_continuous energy damping positive)
  change Continuous (fun time : ℝ => time^2*bandSlopeResponse energy damping positive time) at generated
  simpa only [← bandResponse_slope] using generated

theorem bandLeading_source (energy damping : ℝ) (positive : 0 < damping) :
    bandLeading energy damping positive=fourierDensity*
      ∫ point : LightBand, (bandCoupling true point+bandCoupling false point)*
        (Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
          (Stage9DEF.Compatibility.responseMatrix (FullQuantum.HistoryPrepared.sourceMother
            (oppositeObservable energy damping positive (bandShift point) 0 0)))).re ∂bandMeasure := by
  simp_rw [opposite_source_diagonal,Complex.ofReal_re]
  rw [bandLeading]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketPairResponse
