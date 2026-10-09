import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.SourceRead
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Input

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem root_net_error : ‖calculatedRootNet-finiteRootNet‖ ≤ (3/10^9 : ℝ) := by
  have first := raw_sandwich_change calculatedSourcePointer finiteSourcePointer calculatedNetObservable
  have second := Input.raw_input_error (star finiteSourcePointer) calculatedNetObservable finiteNetObservable
  simp only [star_star,norm_star] at second
  have sourceNorm : ‖calculatedSourcePointer‖ ≤ 2 := calculated_source_pointer_norm.trans (by norm_num)
  have firstBound : ‖calculatedRootNet-star finiteSourcePointer*calculatedNetObservable*finiteSourcePointer‖ ≤ (12/10^17 : ℝ) := by
    apply first.trans
    exact (mul_le_mul (mul_le_mul (add_le_add sourceNorm finite_source_pointer_norm) calculated_net_norm (norm_nonneg _) (by norm_num))
      original_finite_source_pointer_error (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have secondBound : ‖star finiteSourcePointer*calculatedNetObservable*finiteSourcePointer-finiteRootNet‖ ≤ (2/10^9 : ℝ) := by
    apply second.trans
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) finite_source_pointer_norm 2) original_finite_net_observable_error
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have triangle := norm_sub_le_norm_sub_add_norm_sub calculatedRootNet
    (star finiteSourcePointer*calculatedNetObservable*finiteSourcePointer) finiteRootNet
  linarith

private theorem corner_sub {ι : Type*} (A B : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) :
    Prepared.pointerReadout A-Prepared.pointerReadout B=Prepared.pointerReadout (A-B) := rfl

theorem root_corner_error : ‖Prepared.pointerReadout calculatedRootNet-Prepared.pointerReadout finiteRootNet‖ ≤ (3/10^9 : ℝ) := by
  have same : Prepared.pointerReadout calculatedRootNet-Prepared.pointerReadout finiteRootNet=
      Prepared.pointerReadout (calculatedRootNet-finiteRootNet) := corner_sub _ _
  rw [same]
  exact (Prepared.pointer_readout_norm _ (calculated_root_net_hermitian.sub finite_root_net_hermitian)).trans root_net_error

theorem finite_full_supply_norm : ‖Supply.fullSupplyPolynomial‖ ≤ 2 :=
  (Input.approximated_unitary_norm Supply.calculatedSupply Supply.fullSupplyPolynomial _ Supply.original_supply_polynomial_error).trans (by norm_num)

theorem finite_loaded_net_error : ‖calculatedLoadedNet-finiteLoadedNet‖ ≤ (12/10^9 : ℝ) := by
  let A := star Supply.fullSupplyPolynomial*(Prepared.pointerReadout calculatedRootNet)*Supply.fullSupplyPolynomial
  let B := star Supply.fullSupplyPolynomial*(Prepared.pointerReadout finiteRootNet)*Supply.fullSupplyPolynomial
  have hermA : A.IsHermitian := Supply.raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ calculated_root_net_hermitian)
  have hermB : B.IsHermitian := Supply.raw_pullback_hermitian _ _ (Prepared.pointer_readout_hermitian _ finite_root_net_hermitian)
  have raw := Input.raw_input_error (star Supply.fullSupplyPolynomial)
    (Prepared.pointerReadout calculatedRootNet) (Prepared.pointerReadout finiteRootNet)
  simp only [star_star,norm_star] at raw
  have rawBound : ‖A-B‖ ≤ (12/10^9 : ℝ) := by
    apply raw.trans
    exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) finite_full_supply_norm 2) root_corner_error (norm_nonneg _) (by norm_num)).trans (by norm_num)
  change ‖Supply.donorSlice A-Supply.donorSlice B‖ ≤ _
  rw [← donor_slice_sub]
  exact (donor_slice_norm _ (hermA.sub hermB)).trans rawBound

private theorem energy_difference {ι : Type*} [Fintype ι] (A B rho : Matrix ι ι ℂ) :
    energy A rho-energy B rho=energy (A-B) rho := by
  simp only [energy,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re]

theorem finite_post_energy_cost : |Supply.finiteSupplyNetGain-finiteNetGain| ≤ (13/10^9 : ℝ) := by
  rw [source_supply_net_coordinates]
  have read : energy calculatedLoadedNet Actions.finiteReceivedBody-finiteNetGain=
      energy (calculatedLoadedNet-finiteLoadedNet) Actions.finiteReceivedBody :=
    energy_difference calculatedLoadedNet finiteLoadedNet Actions.finiteReceivedBody
  rw [read]
  have paid := finite_body_energy_norm (calculatedLoadedNet-finiteLoadedNet)
    (calculated_loaded_net_hermitian.sub finite_loaded_net_hermitian)
  exact paid.trans ((mul_le_mul_of_nonneg_left finite_loaded_net_error (show (0 : ℝ) ≤ 1+53/10^7 by norm_num)).trans (by norm_num))

theorem original_finite_net_gain_error :
    |(Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint))-finiteNetGain| ≤
      (104/10^7 : ℝ) := by
  have triangle := abs_sub_le
    (Resource.pcEnergyOf (bodyRead Weak.execution.joint)-Resource.pcEnergyOf (bodyRead Weak.origin.joint)) Supply.finiteSupplyNetGain finiteNetGain
  linarith [Supply.original_finite_supply_net_error,finite_post_energy_cost]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
