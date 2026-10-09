import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.TailBudget

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Powered.Dynamics Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem computed_system_positive : Field.computedSystem.PosSemidef := by
  have base : Dense.computedBase.PosSemidef := by
    rw [← Dense.original_base_exact]
    have p := Input.base_system_lawful.1.mul_mul_conjTranspose_same (star Q)
    simpa only [Input.rawBaseSystem,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using p
  simpa only [Field.computedSystem,Matrix.star_eq_conjTranspose] using
    base.mul_mul_conjTranspose_same Field.computedSystemWord

theorem computed_bath_positive : Field.computedBath.PosSemidef := by
  simpa only [Field.computedBath,Matrix.star_eq_conjTranspose] using
    Diagonal.computed_gibbs_positive.mul_mul_conjTranspose_same Field.computedPolynomial

theorem computed_pair_positive : Field.computedPair.PosSemidef := by
  have prepared : Field.computedPreparation.PosSemidef := by
    rw [Field.computedPreparation]
    exact computed_system_positive.kronecker computed_bath_positive
  simpa only [Field.computedPair,Matrix.star_eq_conjTranspose] using
    prepared.mul_mul_conjTranspose_same Input.finiteCollisionMatrix

def positiveReferenceInput : LoadedJoint :=
  Matrix.kronecker (chargedInput Field.computedPair) environmentState

theorem positive_reference_input : positiveReferenceInput.PosSemidef := by
  rw [positiveReferenceInput,chargedInput]
  exact (computed_pair_positive.kronecker excitedController_positive).kronecker environmentState_positive

theorem source_reference_input_error :
    ‖InputProducts.bodyInput-positiveReferenceInput‖ ≤ (3/10^17 : ℝ) := by
  have split : Field.computedBodyInput-positiveReferenceInput=
      Matrix.kronecker (chargedInput Field.computedPair)
        (Prepared.finiteEnvironment-environmentState) := by
    ext i j
    simp only [Field.computedBodyInput,positiveReferenceInput,Matrix.kronecker,
      Matrix.kroneckerMap_apply,Matrix.sub_apply]
    ring
  have reference : ‖Field.computedBodyInput-positiveReferenceInput‖ ≤ (28/10^18 : ℝ) := by
    rw [split]
    have p := (Actions.charged_norm Field.computedPair).trans PCExecution.field_pair_norm
    have e := Prepared.original_finite_environment_error
    rw [norm_sub_rev] at e
    exact (kronecker_norm_le _ _).trans
      ((mul_le_mul p e (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have triangle := norm_sub_le_norm_sub_add_norm_sub InputProducts.bodyInput
    Field.computedBodyInput positiveReferenceInput
  have source := InputProducts.body_input_error
  rw [norm_sub_rev] at source
  linarith

abbrev TailPair := {p : Basis × Basis // 6 ≤ p.1.val ∧ 6 ≤ p.2.val}

theorem tail_pair_sum (f : Basis × Basis → ℂ) :
    (∑ p : TailPair, f p.val)=
      ∑ a ∈ tailIndices, ∑ b ∈ tailIndices, f (a,b) := by
  classical
  calc
    _ = ∑ p ∈ Finset.univ.filter (fun p : Basis × Basis => 6 ≤ p.1.val ∧ 6 ≤ p.2.val), f p := by
      symm
      exact Finset.sum_subtype _ (by simp) _
    _ = _ := by
      simp [tailIndices,Fintype.sum_prod_type,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 6 ≤ a.val <;> simp [ha]

theorem source_tail_pair_trace_complex :
    (InputProducts.pair.submatrix (Subtype.val : TailPair → Basis × Basis)
      Subtype.val).trace=Scalar.value tailPairZ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply]
  change (∑ p : TailPair, InputProducts.pair p.val p.val)=Scalar.value tailPairZ
  rw [tail_pair_sum (fun p => InputProducts.pair p p)]
  simp only [tailPairZ,value_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact (congrFun (congrFun pairQ_value (a,b)) (a,b)).symm

theorem source_tail_pair_trace :
    (InputProducts.pair.submatrix (Subtype.val : TailPair → Basis × Basis)
      Subtype.val).trace.re=(tailPairQ : ℝ) := by
  rw [source_tail_pair_trace_complex]
  simp [tailPairQ,Scalar.value]

abbrev TailBody := (TailPair × Fin 2) × Fin 2

def tailBodyAddress (i : TailBody) : PairController × Fin 2 :=
  ((i.1.1.val,i.1.2),i.2)

def positiveTailInput : Matrix TailBody TailBody ℂ :=
  positiveReferenceInput.submatrix tailBodyAddress tailBodyAddress

theorem positive_tail_input : positiveTailInput.PosSemidef :=
  positive_reference_input.submatrix tailBodyAddress

theorem positive_tail_input_trace : positiveTailInput.trace=
    (Field.computedPair.submatrix (Subtype.val : TailPair → Basis × Basis) Subtype.val).trace := by
  have source : positiveTailInput=
      Matrix.kronecker
        (Matrix.kronecker (Field.computedPair.submatrix (Subtype.val : TailPair → Basis × Basis)
          Subtype.val) excitedController) environmentState := by
      funext i j
      rfl
  rw [source]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,
    excitedController_trace,environmentState_trace]
  ring

theorem positive_tail_trace_bound : positiveTailInput.trace.re < (21/10^8 : ℝ) := by
  have card : Fintype.card TailPair ≤ 9604 := by
    have h := Fintype.card_subtype_le
      (fun p : Basis × Basis => 6 ≤ p.1.val ∧ 6 ≤ p.2.val)
    simpa only [Fintype.card_prod, Fintype.card_fin] using h
  have entry (p : TailPair) :
      (Field.computedPair p.val p.val).re ≤
        (InputProducts.pair p.val p.val).re+(2/10^20 : ℝ) := by
    have h := (matrix_entry_norm_le (Field.computedPair-InputProducts.pair) p.val p.val).trans
      InputProducts.pair_error
    have r := (Complex.abs_re_le_norm ((Field.computedPair-InputProducts.pair) p.val p.val)).trans h
    simp only [Matrix.sub_apply,Complex.sub_re] at r
    linarith [le_abs_self ((Field.computedPair p.val p.val).re-(InputProducts.pair p.val p.val).re)]
  have summed : (∑ p : TailPair, (Field.computedPair p.val p.val).re) ≤
      ∑ p : TailPair, ((InputProducts.pair p.val p.val).re+(2/10^20 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p _
    exact entry p
  have mass : (tailPairQ : ℝ) < 2/10^7 := by
    have h := (Rat.cast_lt (K := ℝ)).2 original_tail_pair_bound
    simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using h
  rw [positive_tail_input_trace]
  rw [← source_tail_pair_trace] at mass
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply,Complex.re_sum] at mass ⊢
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at summed
  have cards : ((Fintype.card TailPair : ℕ) : ℝ) ≤ 9604 := by exact_mod_cast card
  linarith only [summed,mass,cards]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
