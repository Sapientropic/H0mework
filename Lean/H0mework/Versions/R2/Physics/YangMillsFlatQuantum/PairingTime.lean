import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingResponse
import H0mework.Versions.R2.Physics.GaugeSpectrum.Temporal
/-! The original physical clock transports complete mother operators and their
positive source pairing together. The actual next-field law supplies the state leg. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open Stage10.GaugeSpectrum
noncomputable section

private theorem physical_action_coordinate (displacement : BasePoint) (v : Hilbert) (spin : DiracSpinorIndex) (sector : Sector) :
    operator (diracMatrixMatterAction (clockMatrix displacement)) v (spin, sector) =
      phase (spinRate spin) displacement * v (spin, sector) := by
  have read := operator_coordinates (diracMatrixMatterAction (clockMatrix displacement))
    (naturalCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at read
  rw [read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  rw [naturalCoordinates_apply, naturalCoordinates_apply]
  simp [diracMatrixMatterAction, clockMatrix, Matrix.diagonal_apply]

theorem clock_inner (displacement : BasePoint) (v w : Hilbert) :
    inner ℂ (operator (diracMatrixMatterAction (clockMatrix displacement)) v)
      (operator (diracMatrixMatterAction (clockMatrix displacement)) w) = inner ℂ v w := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_congr rfl
  intro index _
  rcases index with ⟨spin, sector⟩
  change operator (diracMatrixMatterAction (clockMatrix displacement)) w (spin, sector) *
      star (operator (diracMatrixMatterAction (clockMatrix displacement)) v (spin, sector)) =
        w (spin, sector) * star (v (spin, sector))
  rw [physical_action_coordinate, physical_action_coordinate, star_mul]
  calc
    _ = (star (phase (spinRate spin) displacement) * phase (spinRate spin) displacement) *
        (w (spin, sector) * star (v (spin, sector))) := by ring
    _ = _ := by rw [Source.phase_star_mul, one_mul]

private theorem clock_embed (displacement : BasePoint) (values : Source.Index → ℂ) :
    diracMatrixMatterAction (clockMatrix displacement) (Compatibility.embed values) =
      Compatibility.embed ((Dynamics.unitary displacement : State.Observable).mulVec values) := by
  funext spin
  simp [diracMatrixMatterAction, clockMatrix, Matrix.diagonal_apply,
    Compatibility.embed, sourceColorDiracMatter, Dynamics.unitary_matrix,
    Matrix.mulVec_diagonal, Dynamics.phaseCoefficient, spinRate, Dynamics.rate,
    Fin.sum_univ_two, smul_add, smul_smul]

theorem prepared_time (point displacement : BasePoint) :
    operator (diracMatrixMatterAction (clockMatrix displacement)) (prepared point) =
      prepared (point + displacement) := by
  have next := Stage10.Recovery.stageOneThroughTenClosure.final.activation.nextField point displacement
  rw [Stage10.Runtime.nextTick_vector, Stage10.Runtime.tick_vector] at next
  rw [prepared, operator_coordinates, clock_embed, ← next]
  rfl

private theorem clock_inverse (displacement : BasePoint) (v : Hilbert) :
    operator (diracMatrixMatterAction (clockMatrix (-displacement)))
      (operator (diracMatrixMatterAction (clockMatrix displacement)) v) = v := by
  apply PiLp.ext
  intro index
  rcases index with ⟨spin, sector⟩
  rw [physical_action_coordinate, physical_action_coordinate]
  have opposite : phase (spinRate spin) (-displacement) = phase (-spinRate spin) displacement := by
    simp [phase]
  rw [opposite]
  calc
    _ = (phase (spinRate spin) displacement * phase (-spinRate spin) displacement) *
        v (spin, sector) := by ring
    _ = _ := by rw [phase_opposite, one_mul]

private theorem operator_comp (B C : Mother) (v : Hilbert) :
    operator (B.comp C) v = operator B (operator C v) := by
  simp [operator]

private theorem transported_vector (point displacement : BasePoint) (B : Mother) :
    operator ((diracMatrixMatterAction (clockMatrix displacement)).comp
      (B.comp (diracMatrixMatterAction (clockMatrix (-displacement))))) (prepared (point + displacement)) =
        operator (diracMatrixMatterAction (clockMatrix displacement)) (operator B (prepared point)) := by
  rw [operator_comp, operator_comp, ← prepared_time point displacement, clock_inverse]

theorem time_pairing (point : BasePoint) (time : ℝ) (B C : Mother) :
    let displacement := Dynamics.timeDisplacement time
    let V : Mother := diracMatrixMatterAction (clockMatrix displacement)
    let W : Mother := diracMatrixMatterAction (clockMatrix (-displacement))
    State.vectorEvaluation (Stage10.Runtime.tick.answer (point + displacement))
      (Compatibility.responseMatrix (pairedMother (V.comp (B.comp W)) (V.comp (C.comp W)))) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Compatibility.responseMatrix (pairedMother B C)) := by
  dsimp only
  rw [source_gram, source_gram, transported_vector, transported_vector, clock_inner]

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
