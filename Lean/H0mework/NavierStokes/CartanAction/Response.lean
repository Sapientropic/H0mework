import H0mework.NavierStokes.CartanAction.Clifford

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanMaterialResponse

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource StageNineLorentzConnectionVariation
open StageNineCurrentCoframeMatterTemporalPrincipal
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativePauliJet
open NativeSourceCartan NativeCartanContorsionSupport NativeCartanClifford

noncomputable section

def increment (velocity : PhysicalSpace) (direction : Fin 4) : DiracExteriorMatterCarrier :=
  diracMatrixMatterAction (diracSpinConnectionLift
    (lorentzSkewConnectionOfBivectorOneForm (contorsion velocity)) direction)
      (NativeCanonicalFluidCoframe.matter velocity)

def response (velocity : PhysicalSpace) : Block :=
  ∑ direction, ∑ pair : Fin 6,
    (((compensation velocity direction)⁻¹ * contorsion velocity direction pair / 2 : ℝ) : ℂ) •
      spinAction (blockAction (bivectorBlock pair) (hermitianBlock (normalizedVelocity velocity))) direction

theorem response_inverse (velocity : PhysicalSpace) :
    currentCoframeMatterTemporalPrincipalInverse (NativeCanonicalFluidCoframe.coframe velocity)
      (gaugeVectorAt (NativeCanonicalFluidCoframe.coframe velocity) (increment velocity)) = lowerMatter (response velocity) := by
  rw [actual_derivative_inverse]
  simp only [normalizedDerivative, increment, source_matter, spinBlock_action, spin_action,
    spinBlock, blockAction_sum, blockAction_smul,
    map_sum, map_smul, Finset.smul_sum, smul_smul, response]
  simp only [← map_smul, ← map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro direction _
  apply Finset.sum_congr rfl
  intro pair _
  congr 1
  push_cast
  ring

/-- The generated Cartan support, rather than an input phase certificate, pays this response. -/
theorem response_phase_zero (velocity : PhysicalSpace) :
    phaseResidual (normalizedVelocity velocity) (response velocity) = 0 := by
  have term (direction : Fin 4) (pair : Fin 6) :
      ((compensation velocity direction)⁻¹ * contorsion velocity direction pair / 2) *
        phaseResidual (normalizedVelocity velocity)
          (spinAction (blockAction (bivectorBlock pair) (hermitianBlock (normalizedVelocity velocity))) direction) = 0 := by
    by_cases repeated : direction = lorentzBivectorFirst pair ∨ direction = lorentzBivectorSecond pair
    · have supported := contorsion_support velocity direction pair repeated
      rw [supported]
      simp
    · rw [bivector_phase_zero _ _ _ (not_or.mp repeated).1 (not_or.mp repeated).2, mul_zero]
  simp only [response, Fin.sum_univ_four, Fin.sum_univ_six, phase_add, phase_smul, term, add_zero]

end
end SaturationMonoid.NavierStokes.NativeCartanMaterialResponse
