import H0mework.Physics.Exterior.GlobalIntegratedAction
import H0mework.Physics.SpinPair.Parameters

/-! Native pairing and source-constant readouts. These do not fit a scale,
replace the source vacuum, or assert a scattering interpretation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Normalization
open SU7MotherLieAlgebra StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
noncomputable section

theorem native_boundary :
    ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).strongCouplingSquared : ℝ) = 1/2 ∧
    ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).weakCouplingSquared : ℝ) = 1/2 ∧
    ((sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ) = 1/2 := by
  change sourceCoupling = 1/2 ∧ sourceCoupling = 1/2 ∧ sourceCoupling = 1/2
  exact ⟨sourceCoupling_eq, sourceCoupling_eq, sourceCoupling_eq⟩

/-- The source U(1) bilinear is NOT the restriction of the mother trace. -/
theorem hypercharge_trace_factor (first second : HyperchargeLieScalar) :
    specialUnitaryLiePairing (p286LieBlockEmbed (0, 0, first))
        (p286LieBlockEmbed (0, 0, second)) =
      2 * hyperchargeLiePairing first second := by
  simp [specialUnitaryLiePairing, hyperchargeLiePairing, p286LieBlockEmbed,
    rawP286LieBlock, weakHyperchargeLieBlock, hyperchargeLieBlock,
    scalarLieBlock, Matrix.trace, Matrix.mul_apply]
  ring

/-- Exact source potential coefficient along ANY scalar direction. -/
theorem potential_quadratic (target direction : StageNineDynamicBreakingVacuum.ScalarCoordinateCarrier)
    (parameter : ℝ) :
    StageNineDynamicBreakingVacuum.frameRelativeScalarPotential target
      (target + (parameter : ℂ) • direction) =
      parameter ^ 2 * StageNineDynamicBreakingVacuum.scalarCoordinateSquaredNorm direction := by
  rw [StageNineDynamicBreakingVacuum.frameRelativeScalarPotential_expansion]
  simp [StageNineDynamicBreakingVacuum.frameRelativeScalarPotential]

/-- In the native kinetic convention 1/2 times the real scalar pairing,
the potential Hessian coefficient is 2, before other field blocks mix. -/
theorem potential_second_coefficient (target direction : StageNineDynamicBreakingVacuum.ScalarCoordinateCarrier) :
    StageNineDynamicBreakingVacuum.frameRelativeScalarPotential target (target + direction) +
      StageNineDynamicBreakingVacuum.frameRelativeScalarPotential target (target - direction) =
      2 * StageNineDynamicBreakingVacuum.scalarCoordinateSquaredNorm direction := by
  simp [StageNineDynamicBreakingVacuum.frameRelativeScalarPotential,
    StageNineDynamicBreakingVacuum.scalarCoordinateSquaredNorm]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Normalization
