import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailPositive.Source

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def inTail (i : PairController × Fin 2) : Prop :=
  6 ≤ i.1.1.1.val ∧ 6 ≤ i.1.1.2.val

instance tailDecidable (i : PairController × Fin 2) : Decidable (inTail i) := by
  unfold inTail
  infer_instance

def tailProjection : LoadedJoint :=
  Matrix.diagonal (fun i => if inTail i then (1 : ℂ) else 0)

theorem tail_projection_adjoint : star tailProjection=tailProjection := by
  ext i j
  by_cases same : i=j
  · subst j
    simp [tailProjection]
  · simp [tailProjection,same,Ne.symm same]

theorem tail_projection_norm : ‖tailProjection‖ ≤ (1 : ℝ) := by
  rw [tailProjection,Matrix.l2_opNorm_diagonal]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  by_cases h : inTail i <;> simp [h]

def maskTail (A : LoadedJoint) : LoadedJoint := tailProjection*A*tailProjection

theorem positive_masked_input : (maskTail positiveReferenceInput).PosSemidef := by
  have h := positive_reference_input.mul_mul_conjTranspose_same tailProjection
  change (tailProjection*positiveReferenceInput*tailProjection).PosSemidef
  rw [← Matrix.star_eq_conjTranspose,tail_projection_adjoint] at h
  exact h

theorem source_masked_input_error :
    ‖maskTail InputProducts.bodyInput-maskTail positiveReferenceInput‖ ≤ (3/10^17 : ℝ) := by
  have same : maskTail InputProducts.bodyInput-maskTail positiveReferenceInput=
      star tailProjection*(InputProducts.bodyInput-positiveReferenceInput)*tailProjection := by
    rw [tail_projection_adjoint]
    simp only [maskTail,Matrix.mul_sub,Matrix.sub_mul]
  rw [same]
  have bound := Prepared.sandwich_norm tailProjection
    (InputProducts.bodyInput-positiveReferenceInput)
  apply bound.trans
  calc
    ‖tailProjection‖^2*‖InputProducts.bodyInput-positiveReferenceInput‖ ≤
      (1 : ℝ)^2*(3/10^17 : ℝ) := by
        gcongr
        · exact tail_projection_norm
        · exact source_reference_input_error
    _ = 3/10^17 := by norm_num

theorem mask_tail_diagonal (A : LoadedJoint) (i : PairController × Fin 2) :
    maskTail A i i=if inTail i then A i i else 0 := by
  rw [maskTail,tailProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : inTail i <;> simp [h]

theorem tail_body_sum (f : PairController × Fin 2 → ℂ) :
    (∑ i : PairController × Fin 2, if inTail i then f i else 0)=
      ∑ i : TailBody, f (tailBodyAddress i) := by
  have filter_sum (g : Basis × Basis → ℂ) :
      (∑ p : Basis × Basis,
        if 6 ≤ p.1.val ∧ 6 ≤ p.2.val then g p else 0)=
        ∑ p : TailPair, g p.val := by
    classical
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Basis × Basis =>
          6 ≤ p.1.val ∧ 6 ≤ p.2.val), g p := by simp [Finset.sum_filter]
      _ = _ := Finset.sum_subtype _ (by simp) _
  simp only [Fintype.sum_prod_type,tailBodyAddress]
  have inner (p : Basis × Basis) :
      (∑ c : Fin 2, ∑ e : Fin 2,
        if inTail ((p,c),e) then f ((p,c),e) else 0)=
      if 6 ≤ p.1.val ∧ 6 ≤ p.2.val then
        (∑ c : Fin 2, ∑ e : Fin 2, f ((p,c),e)) else 0 := by
    by_cases h : 6 ≤ p.1.val ∧ 6 ≤ p.2.val <;> simp [inTail,h]
  simp_rw [inner]
  simpa only [Fintype.sum_prod_type] using
    filter_sum (fun p => ∑ c : Fin 2, ∑ e : Fin 2, f ((p,c),e))

theorem masked_reference_trace : (maskTail positiveReferenceInput).trace=
    positiveTailInput.trace := by
  simp only [Matrix.trace,Matrix.diag,mask_tail_diagonal]
  rw [tail_body_sum]
  rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
