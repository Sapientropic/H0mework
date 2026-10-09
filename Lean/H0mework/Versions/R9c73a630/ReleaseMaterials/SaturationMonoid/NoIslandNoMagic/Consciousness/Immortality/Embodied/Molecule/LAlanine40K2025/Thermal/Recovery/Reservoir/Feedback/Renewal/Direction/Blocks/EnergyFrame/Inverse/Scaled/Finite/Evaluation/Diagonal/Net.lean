import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
open Collision Propagation.Interface Load.Source Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def computedBodyInput : LoadedJoint := Matrix.kronecker (chargedInput computedPair) Prepared.finiteEnvironment
def computedBody : LoadedJoint := Actions.finiteReceivedWord*computedBodyInput*star Actions.finiteReceivedWord

theorem finite_environment_norm : ‖Prepared.finiteEnvironment‖ ≤ 2 := by
  have original := Input.state_norm_le_one environmentState environmentState_positive environmentState_trace
  have triangle := norm_sub_le_norm_sub_add_norm_sub Prepared.finiteEnvironment environmentState 0
  simp only [sub_zero] at triangle
  have paid := Prepared.original_finite_environment_error
  rw [norm_sub_rev] at paid
  linarith

theorem computed_body_input_error : ‖Actions.finitePreparedInput-computedBodyInput‖ ≤ (1/10^15 : ℝ) := by
  have split : Actions.finitePreparedInput-computedBodyInput=
      Matrix.kronecker (chargedInput (Input.finitePair-computedPair)) Prepared.finiteEnvironment := by
    ext i j
    simp only [Actions.finitePreparedInput,computedBodyInput,chargedInput,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  rw [split]
  exact (kronecker_norm_le _ _).trans ((mul_le_mul ((Actions.charged_norm _).trans pair_numeric_error)
    finite_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem computed_body_error : ‖Actions.finiteReceivedBody-computedBody‖ ≤ (4/10^15 : ℝ) := by
  have wordNorm : ‖Actions.finiteReceivedWord‖ ≤ 2 :=
    (Input.approximated_unitary_norm Actions.calculatedReceivedWord Actions.finiteReceivedWord _ Actions.original_received_word_polynomial_error).trans (by norm_num)
  have paid := Input.raw_input_error Actions.finiteReceivedWord Actions.finitePreparedInput computedBodyInput
  exact paid.trans ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) wordNorm 2) computed_body_input_error
    (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem finite_net_observable_norm : ‖Post.finiteNetObservable‖ ≤ 1 := by
  have source : ‖Post.calculatedNetObservable‖ ≤ (123/1000 : ℝ) :=
    (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ PointerJoint Post.pointerFrame) (gainObservable Sectors.pointerPCObservable)).le.trans original_net_PC_norm
  have triangle := norm_sub_le_norm_sub_add_norm_sub Post.finiteNetObservable Post.calculatedNetObservable 0
  simp only [sub_zero] at triangle
  have paid := Post.original_finite_net_observable_error
  rw [norm_sub_rev] at paid
  linarith

theorem final_observable_norm : ‖Post.finiteLoadedNet‖ ≤ 16 := by
  have root : ‖Post.finiteRootNet‖ ≤ 4 :=
    (Prepared.sandwich_norm Post.finiteSourcePointer Post.finiteNetObservable).trans
      ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) Post.finite_source_pointer_norm 2) finite_net_observable_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have corner := (Prepared.pointer_readout_norm Post.finiteRootNet Post.finite_root_net_hermitian).trans root
  have full := Prepared.sandwich_norm Supply.fullSupplyPolynomial (Prepared.pointerReadout Post.finiteRootNet)
  have fullBound : ‖star Supply.fullSupplyPolynomial*(Prepared.pointerReadout Post.finiteRootNet)*Supply.fullSupplyPolynomial‖ ≤ 16 :=
    full.trans ((mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) Post.finite_full_supply_norm 2) corner (norm_nonneg _) (by norm_num)).trans (by norm_num))
  exact (Post.donor_slice_norm _ (Supply.raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ Post.finite_root_net_hermitian))).trans fullBound

def computedNetGain : ℝ := Collision.energy Post.finiteLoadedNet computedBody

private theorem energy_input_sub {ι : Type*} [Fintype ι] (O A B : Matrix ι ι ℂ) :
    Collision.energy O A-Collision.energy O B=Collision.energy O (A-B) := by
  simp only [Collision.energy,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re]

theorem diagonal_computation_net_cost : |Post.finiteNetGain-computedNetGain| ≤ (3/10^9 : ℝ) := by
  have read : Post.finiteNetGain-computedNetGain=Collision.energy Post.finiteLoadedNet (Actions.finiteReceivedBody-computedBody) :=
    energy_input_sub Post.finiteLoadedNet Actions.finiteReceivedBody computedBody
  rw [read]
  have paid := Input.energy_dimension_norm Post.finiteLoadedNet (Actions.finiteReceivedBody-computedBody)
  have cardinal : Fintype.card (PairController × Fin 2)=38416 := by norm_num [PairController,Basis]
  rw [cardinal] at paid
  norm_num only [Nat.cast_ofNat] at paid
  exact paid.trans ((mul_le_mul (mul_le_mul_of_nonneg_left final_observable_norm (show (0 : ℝ) ≤ 38416 by norm_num))
    computed_body_error (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem original_computed_diagonal_net_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-computedNetGain| ≤
      (105/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) Post.finiteNetGain computedNetGain
  linarith [Post.original_finite_net_gain_error,diagonal_computation_net_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Diagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
