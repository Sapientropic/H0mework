import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_mul_int_error (AI BI : MatrixInt ι ι) (A B : Matrix ι ι ℂ)
    (small : Fintype.card ι ≤ 64) (eA eB : ℝ) (ha : ‖value AI-A‖ ≤ eA)
    (hb : ‖value BI-B‖ ≤ eB) :
    ‖value (multiply AI BI)-A*B‖ ≤
      (64/10^30 : ℝ)+eA*(‖B‖+eB)+‖A‖*eB := by
  have biBound : ‖value BI‖ ≤ ‖B‖+eB := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (value BI) B 0
    simp only [sub_zero] at triangle
    linarith only [triangle,hb]
  have split : value AI*value BI-A*B=(value AI-A)*value BI+A*(value BI-B) := by
    noncomm_ring
  have ae : 0 ≤ eA := le_trans (norm_nonneg _) ha
  have product : ‖value AI*value BI-A*B‖ ≤ eA*(‖B‖+eB)+‖A‖*eB := by
    rw [split]
    calc
      _ ≤ ‖(value AI-A)*value BI‖+‖A*(value BI-B)‖ := norm_add_le _ _
      _ ≤ ‖value AI-A‖*‖value BI‖+‖A‖*‖value BI-B‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ _ := by gcongr
  calc
    _ ≤ ‖value (multiply AI BI)-value AI*value BI‖+
      ‖value AI*value BI-A*B‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (64/10^30 : ℝ)+(eA*(‖B‖+eB)+‖A‖*eB) :=
      add_le_add (multiply_error AI BI small small) product
    _ = _ := by ring

theorem q_matrix_norm_le_200 (M : MatrixQ ι ι) (small : Fintype.card ι ≤ 64)
    (entries : ∀ i j, |(M i j).1|+|(M i j).2| ≤ (3 : ℚ)) :
    ‖qvalue M‖ ≤ (200 : ℝ) := by
  have each (i j : ι) : ‖qvalue M i j‖ ≤ (3 : ℝ) := by
    have bound : |((M i j).1 : ℝ)|+|((M i j).2 : ℝ)| ≤ (3 : ℝ) := by
      exact_mod_cast entries i j
    change ‖((((M i j).1 : ℝ) : ℂ)+Complex.I*((((M i j).2 : ℝ) : ℂ)))‖ ≤ 3
    calc
      _ ≤ ‖((((M i j).1 : ℝ) : ℂ))‖+
        ‖Complex.I*((((M i j).2 : ℝ) : ℂ))‖ := norm_add_le _ _
      _ = |((M i j).1 : ℝ)|+|((M i j).2 : ℝ)| := by simp
      _ ≤ 3 := bound
  exact (norm_from_entries (qvalue M) 3 (by norm_num) small small each).trans (by norm_num)

theorem q_root_norm_le_5000 {A B : Matrix ι ι ℚ}
    (G : SquareRoot.RootGram A B) (small : Fintype.card ι ≤ 64)
    (entries : ∀ i j, |G.realPart i j|+|G.imagPart i j| ≤ (1 : ℚ)) :
    ‖qvalue (rootGramQ G)‖ ≤ (5000 : ℝ) := by
  let F := qvalue (factorQ G)
  have bound := factor_norm_bound_of_entries G small entries
  change ‖F‖ ≤ (64 : ℝ) at bound
  have same : qvalue (rootGramQ G)=F*star F := by
    change qvalue (qmultiply (factorQ G) (qadjoint (factorQ G))) = _
    rw [qvalue_multiply,qvalue_adjoint]
    rfl
  rw [same]
  exact (norm_mul_le F (star F)).trans (by
    rw [norm_star]
    have h := mul_le_mul bound bound (norm_nonneg F) (by norm_num : (0 : ℝ) ≤ 64)
    nlinarith only [h])

theorem rotate_int_bound (UI RI : MatrixInt ι ι) (U R : Matrix ι ι ℂ)
    (small : Fintype.card ι ≤ 64)
    (uError : ‖value UI-U‖ ≤ (1/10^25 : ℝ))
    (rError : ‖value RI-R‖ ≤ (1/10^25 : ℝ))
    (uBound : ‖U‖ ≤ (200 : ℝ)) (rBound : ‖R‖ ≤ (5000 : ℝ)) :
    ‖value (rotateInt UI RI)-U*R*star U‖ ≤ (1/10^18 : ℝ) := by
  have first := source_mul_int_error UI RI U R small (1/10^25) (1/10^25)
    uError rError
  have firstBound : ‖value (multiply UI RI)-U*R‖ ≤ (1/10^21 : ℝ) := by
    apply first.trans
    calc
      (64/10^30 : ℝ)+(1/10^25)*(‖R‖+1/10^25)+‖U‖*(1/10^25) ≤
        (64/10^30 : ℝ)+(1/10^25)*(5000+1/10^25)+200*(1/10^25) := by
          gcongr
      _ ≤ 1/10^21 := by norm_num
  have adjointError : ‖value (adjoint UI)-star U‖ ≤ (1/10^25 : ℝ) := by
    rw [value_adjoint,← Matrix.star_eq_conjTranspose,← star_sub,norm_star]
    exact uError
  have exactNorm : ‖U*R‖ ≤ (1000000 : ℝ) := by
    have product := mul_le_mul uBound rBound (norm_nonneg R)
      (by norm_num : (0 : ℝ) ≤ 200)
    exact (norm_mul_le U R).trans (by nlinarith only [product])
  have adjointBound : ‖star U‖ ≤ (200 : ℝ) := by rw [norm_star]; exact uBound
  have second := source_mul_int_error (multiply UI RI) (adjoint UI)
    (U*R) (star U) small (1/10^21) (1/10^25) firstBound adjointError
  change ‖value (multiply (multiply UI RI) (adjoint UI))-U*R*star U‖ ≤ _
  apply second.trans
  calc
    (64/10^30 : ℝ)+(1/10^21)*(‖star U‖+1/10^25)+‖U*R‖*(1/10^25) ≤
      (64/10^30 : ℝ)+(1/10^21)*(200+1/10^25)+1000000*(1/10^25) := by
        gcongr
    _ ≤ 1/10^18 := by norm_num
end


end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
