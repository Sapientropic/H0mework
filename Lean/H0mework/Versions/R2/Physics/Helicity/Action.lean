import H0mework.Versions.R2.Physics.Helicity.Source

/-! The full magnetic/current action generates its occupied response.
The source covariant derivative, rather than a supplied scalar observable,
is the primitive input. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity

open Matrix DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open StageNineP286GaugeConnectionVariation SU7MotherLieAlgebra SU7MotherGaugeTheory
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

def action (point : BasePoint) : Module.End ℂ DiracExteriorMatterCarrier :=
  ∑ axis : Fin 3,
    diracExteriorMotherLieAction (p286LieBlockEmbed (magnetic point axis)) *
      diracExteriorMotherLieAction (p286LieBlockEmbed (covariantCurl point axis))

def amplitude : ℝ := 3 * gaugeScale ^ 5 / 2

theorem amplitude_pos : 0 < amplitude :=
  div_pos (mul_pos (by norm_num) (pow_pos gaugeScale_pos 5)) (by norm_num)

theorem amplitude_from_fullTrace (point : BasePoint) :
    (amplitude : ℂ) = value point / 2 := by
  rw [value_eq]
  simp [amplitude]

theorem action_curvature_squares (point : BasePoint) :
    action point = (2 * gaugeScale : ℂ) •
      ∑ axis : Fin 3, incomingCurvatureAction point axis * incomingCurvatureAction point axis := by
  rw [action, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  rw [magnetic_eq, covariantCurl_eq, incomingCurvatureAction_eq, curvatureAction,
    actual_magnetic_component]
  simp only [p286LieBlockEmbed_real_smul, diracExteriorMotherLieAction_real_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem action_embed (point : BasePoint) (values : Source.Index → ℂ) :
    action point (embed values) = (amplitude : ℂ) • embed values := by
  rw [action_curvature_squares]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply,
    incomingCurvatureAction_embed, Matrix.mulVec_mulVec, curvature_square,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul, Fin.sum_univ_three]
  rw [← add_smul, ← add_smul, smul_smul]
  congr 1
  simp [amplitude, curvatureScale]
  ring

theorem action_compression (point : BasePoint) :
    compression (action point) = (amplitude : ℂ) • 1 := by
  have action_eq : coordinates.comp ((action point).comp embed) =
      Matrix.toLin' ((amplitude : ℂ) • 1) := by
    apply LinearMap.ext
    intro values
    rw [Matrix.toLin'_apply]
    simp only [LinearMap.comp_apply, action_embed, map_smul, coordinates_embed,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [compression, action_eq, LinearMap.toMatrix'_toLin']

def observable (point : BasePoint) : State.Observable := responseMatrix (action point)

theorem observable_normalForm (point : BasePoint) :
    observable point = (amplitude : ℂ) • (exchange ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext ⟨spin, color⟩ ⟨other, input⟩
  simp only [observable, responseMatrix, action_compression]
  simp [Compatibility.flip, exchange, Matrix.one_apply, Prod.mk.injEq, Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all

theorem actual_quantum_response (point : BasePoint) :
    Runtime.configuration.conjugateMatter point (action point (Runtime.configuration.matter point)) =
      4 * (spinScale : ℂ) * State.vectorEvaluation (Runtime.tick.answer point) (observable point) := by
  rw [Runtime.configuration_eq, Runtime.tick_vector]
  exact actual_action_quantumResponse point (action point)

theorem observable_hermitian (point : BasePoint) : (observable point).IsHermitian := by
  rw [observable_normalForm]
  change _ᴴ = _
  simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_kronecker, exchange_hermitian.eq]

theorem observable_ground_mean (point : BasePoint) : groundEvaluation (observable point) = 0 := by
  rw [groundEvaluation_diagonal, observable_normalForm]
  simp [exchange, spinFlip]

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Helicity
