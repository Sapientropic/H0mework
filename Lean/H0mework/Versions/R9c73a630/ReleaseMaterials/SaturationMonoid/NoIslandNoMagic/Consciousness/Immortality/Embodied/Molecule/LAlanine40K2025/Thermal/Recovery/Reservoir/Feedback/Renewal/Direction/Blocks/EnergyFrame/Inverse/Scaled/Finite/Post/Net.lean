import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Suffix
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Observable

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem reframe_star {ι : Type*} [Fintype ι] [DecidableEq ι] (W U : Matrix.unitaryGroup ι ℂ) :
    Actions.reframeUnitary W (star U)=star (Actions.reframeUnitary W U) := by
  simp only [Actions.reframeUnitary,star_mul,star_star,mul_assoc]

theorem conjugated_pullback {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W U : Matrix.unitaryGroup ι ℂ) (O : Matrix ι ι ℂ) :
    Quantum.conjugation W (Quantum.conjugation (star U) O)=
      Quantum.conjugation (star (Actions.reframeUnitary W U)) (Quantum.conjugation W O) := by
  rw [Actions.reframe_action,reframe_star]

theorem raw_observable_pullback_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (V O B : Matrix ι ι ℂ) :
    ‖Quantum.conjugation (star U) O-star V*B*V‖ ≤
      (1+‖V‖)*‖O‖*‖(U : Matrix ι ι ℂ)-V‖+‖V‖^2*‖O-B‖ := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Quantum.conjugation (star U) O) (star V*O*V) (star V*B*V)
  have raw := Input.raw_input_error (star V) O B
  simp only [star_star,norm_star] at raw
  exact triangle.trans (add_le_add (Supply.raw_pullback_error U V O) raw)

def calculatedNetObservable : PointerJoint := Quantum.conjugation pointerFrame (gainObservable Sectors.pointerPCObservable)
def finiteNetObservable : PointerJoint :=
  star elevenPolynomial*finitePCObservable*elevenPolynomial-star ninePolynomial*finitePCObservable*ninePolynomial

theorem original_net_coordinates : calculatedNetObservable=
    Quantum.conjugation (star calculatedEleven) calculatedPCObservable-Quantum.conjugation (star calculatedNine) calculatedPCObservable := by
  rw [calculatedNetObservable,gainObservable,map_sub,conjugated_pullback,conjugated_pullback]
  rfl

theorem original_nine_observable_error :
    ‖Quantum.conjugation (star calculatedNine) calculatedPCObservable-star ninePolynomial*finitePCObservable*ninePolynomial‖ ≤ (2/10^10 : ℝ) := by
  have normV := Input.approximated_unitary_norm calculatedNine ninePolynomial _ original_nine_polynomial_error
  have paid := raw_observable_pullback_error calculatedNine ninePolynomial calculatedPCObservable finitePCObservable
  apply paid.trans
  have first := mul_le_mul (mul_le_mul (add_le_add (le_refl (1 : ℝ)) normV) calculated_PC_observable_norm (norm_nonneg _) (by norm_num))
    original_nine_polynomial_error (norm_nonneg _) (by norm_num)
  have second := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) normV 2) finite_PC_observable_error (norm_nonneg _) (by positivity)
  exact (add_le_add first second).trans (by norm_num)

theorem original_eleven_observable_error :
    ‖Quantum.conjugation (star calculatedEleven) calculatedPCObservable-star elevenPolynomial*finitePCObservable*elevenPolynomial‖ ≤ (3/10^10 : ℝ) := by
  have normV := Input.approximated_unitary_norm calculatedEleven elevenPolynomial _ original_eleven_polynomial_error
  have paid := raw_observable_pullback_error calculatedEleven elevenPolynomial calculatedPCObservable finitePCObservable
  apply paid.trans
  have first := mul_le_mul (mul_le_mul (add_le_add (le_refl (1 : ℝ)) normV) calculated_PC_observable_norm (norm_nonneg _) (by norm_num))
    original_eleven_polynomial_error (norm_nonneg _) (by norm_num)
  have second := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) normV 2) finite_PC_observable_error (norm_nonneg _) (by positivity)
  exact (add_le_add first second).trans (by norm_num)

theorem original_finite_net_observable_error : ‖calculatedNetObservable-finiteNetObservable‖ ≤ (5/10^10 : ℝ) := by
  rw [original_net_coordinates,finiteNetObservable]
  have split := norm_sub_le
    (Quantum.conjugation (star calculatedEleven) calculatedPCObservable-star elevenPolynomial*finitePCObservable*elevenPolynomial)
    (Quantum.conjugation (star calculatedNine) calculatedPCObservable-star ninePolynomial*finitePCObservable*ninePolynomial)
  have algebra : Quantum.conjugation (star calculatedEleven) calculatedPCObservable-Quantum.conjugation (star calculatedNine) calculatedPCObservable-
      (star elevenPolynomial*finitePCObservable*elevenPolynomial-star ninePolynomial*finitePCObservable*ninePolynomial)=
    (Quantum.conjugation (star calculatedEleven) calculatedPCObservable-star elevenPolynomial*finitePCObservable*elevenPolynomial)-
    (Quantum.conjugation (star calculatedNine) calculatedPCObservable-star ninePolynomial*finitePCObservable*ninePolynomial) := by abel
  rw [algebra]
  exact split.trans (by linarith [original_eleven_observable_error,original_nine_observable_error])

theorem finite_net_hermitian : finiteNetObservable.IsHermitian :=
  (Supply.raw_pullback_hermitian elevenPolynomial finitePCObservable finite_PC_observable_hermitian).sub
    (Supply.raw_pullback_hermitian ninePolynomial finitePCObservable finite_PC_observable_hermitian)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
