import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame.FiniteNormed
noncomputable section
open InnerProductSpace
open scoped BigOperators Matrix

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [Fintype ι]

/-- The complete finite family fixes its own order; no basis is supplied. -/
def ordered (raw : ι → E) (index : Fin (Fintype.card ι)) : E :=
  raw ((Fintype.equivFin ι).symm index)

abbrev Index (raw : ι → E) :=
  {index : Fin (Fintype.card ι) // gramSchmidtNormed 𝕜 (ordered raw) index ≠ 0}

noncomputable instance indexFintype (raw : ι → E) : Fintype (Index (𝕜 := 𝕜) raw) :=
  Fintype.ofFinite _

def field (raw : ι → E) (index : Index (𝕜 := 𝕜) raw) : E :=
  gramSchmidtNormed 𝕜 (ordered raw) index.val

def rank (raw : ι → E) : Nat := Fintype.card (Index (𝕜 := 𝕜) raw)

theorem field_orthonormal (raw : ι → E) : Orthonormal 𝕜 (field (𝕜 := 𝕜) raw) :=
  gramSchmidtNormed_orthonormal' (ordered raw)

omit [NormedAddCommGroup E] in
theorem range_ordered (raw : ι → E) : Set.range (ordered raw) = Set.range raw := by
  ext value
  constructor
  · rintro ⟨index,rfl⟩
    exact Set.mem_range_self _
  · rintro ⟨index,rfl⟩
    exact ⟨Fintype.equivFin ι index,by simp only [ordered,Equiv.symm_apply_apply]⟩

theorem span_nonzero (raw : ι → E) :
    Submodule.span 𝕜 (Set.range (field (𝕜 := 𝕜) raw)) =
      Submodule.span 𝕜 (Set.range (gramSchmidtNormed 𝕜 (ordered raw))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro value ⟨index,rfl⟩
    exact Submodule.subset_span (Set.mem_range_self index.val)
  · apply Submodule.span_le.mpr
    rintro value ⟨index,rfl⟩
    by_cases nonzero : gramSchmidtNormed 𝕜 (ordered raw) index = 0
    · rw [nonzero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨index,nonzero⟩,rfl⟩

theorem span_exact (raw : ι → E) :
    Submodule.span 𝕜 (Set.range (field (𝕜 := 𝕜) raw)) =
      Submodule.span 𝕜 (Set.range raw) := by
  rw [span_nonzero,span_gramSchmidtNormed_range,span_gramSchmidt,range_ordered]

theorem field_mem_span (raw : ι → E) (index : Index (𝕜 := 𝕜) raw) :
    field (𝕜 := 𝕜) raw index ∈ Submodule.span 𝕜 (Set.range raw) := by
  rw [← span_exact raw]
  exact Submodule.subset_span (Set.mem_range_self index)

theorem rank_exact (raw : ι → E) :
    rank (𝕜 := 𝕜) raw = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range raw)) := by
  rw [← span_exact raw]
  exact (finrank_span_eq_card (field_orthonormal raw).linearIndependent).symm

theorem rank_le_source_card (raw : ι → E) : rank (𝕜 := 𝕜) raw ≤ Fintype.card ι := by
  unfold rank
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (Subtype.val : Index (𝕜 := 𝕜) raw → Fin (Fintype.card ι)) Subtype.val_injective

/-- A raw independent subfamily pays a lower bound; it does not choose the generated frame. -/
theorem independent_subfamily_rank_le (raw : ι → E) {κ : Type*} [Fintype κ]
    (select : κ → ι) (independent : LinearIndependent 𝕜 (raw ∘ select)) :
    Fintype.card κ ≤ rank (𝕜 := 𝕜) raw := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range raw)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range raw)
  rw [rank_exact,← finrank_span_eq_card independent]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro value ⟨index,rfl⟩
  exact Set.mem_range_self _

def gram (raw : ι → E) : Matrix (Index (𝕜 := 𝕜) raw) (Index (𝕜 := 𝕜) raw) 𝕜 :=
  Matrix.gram 𝕜 (field (𝕜 := 𝕜) raw)

theorem gram_one (raw : ι → E) : gram (𝕜 := 𝕜) raw = 1 :=
  Matrix.gram_eq_one_iff_orthonormal.mpr (field_orthonormal raw)

theorem gram_isUnit (raw : ι → E) : IsUnit (gram (𝕜 := 𝕜) raw) := by
  rw [gram_one]
  exact isUnit_one

/-- A complete source-span representation; the raw Gram matrix may be singular. -/
theorem exists_source_coefficients (raw : ι → E) (index : Index (𝕜 := 𝕜) raw) :
    ∃ coefficients : ι → 𝕜, ∑ source, coefficients source • raw source = field (𝕜 := 𝕜) raw index :=
  (Submodule.mem_span_range_iff_exists_fun 𝕜).mp (field_mem_span raw index)

def projectionRatio (raw : ι → E) (previous current : Fin (Fintype.card ι)) : 𝕜 :=
  inner 𝕜 (gramSchmidt 𝕜 (ordered raw) previous) (ordered raw current) /
    (‖gramSchmidt 𝕜 (ordered raw) previous‖ : 𝕜) ^ 2

/-- The same Gram-Schmidt recurrence generates the full source coefficient vector. -/
def gsCoefficients (raw : ι → E) (current : Fin (Fintype.card ι)) : Fin (Fintype.card ι) → 𝕜 :=
  wellFounded_lt.fix (C := fun _ : Fin (Fintype.card ι) => Fin (Fintype.card ι) → 𝕜)
    (fun current recurse source =>
    (if source = current then 1 else 0) -
      ∑ previous : Finset.Iio current,
        projectionRatio (𝕜 := 𝕜) raw previous.val current *
          recurse previous.val (Finset.mem_Iio.mp previous.property) source) current

theorem gs_coefficients_step (raw : ι → E) (current source : Fin (Fintype.card ι)) :
    gsCoefficients (𝕜 := 𝕜) raw current source = (if source = current then 1 else 0) -
      ∑ previous : Finset.Iio current,
        projectionRatio (𝕜 := 𝕜) raw previous.val current *
          gsCoefficients (𝕜 := 𝕜) raw previous.val source := by
  rw [gsCoefficients,WellFounded.fix_eq]
  rfl

theorem gs_coefficients_synthesis (raw : ι → E) (current : Fin (Fintype.card ι)) :
    gramSchmidt 𝕜 (ordered raw) current =
      ∑ source, gsCoefficients (𝕜 := 𝕜) raw current source • ordered raw source := by
  classical
  apply wellFounded_lt.induction current
  intro current previous
  have recurrence :
      (∑ source, gsCoefficients (𝕜 := 𝕜) raw current source • ordered raw source) =
        ∑ source, ((if source = current then 1 else 0) -
          ∑ prior : Finset.Iio current,
            projectionRatio (𝕜 := 𝕜) raw prior.val current *
              gsCoefficients (𝕜 := 𝕜) raw prior.val source) • ordered raw source :=
    Finset.sum_congr rfl (fun source _ =>
      congrArg (fun coefficient => coefficient • ordered raw source)
        (gs_coefficients_step raw current source))
  rw [recurrence]
  simp only [sub_smul,Finset.sum_sub_distrib,ite_smul,one_smul,
    zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_smul,mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have generated (index : Finset.Iio current) :
      (∑ source, gsCoefficients (𝕜 := 𝕜) raw index.val source • ordered raw source) =
        gramSchmidt 𝕜 (ordered raw) index.val :=
    (previous index.val (Finset.mem_Iio.mp index.property)).symm
  simp only [generated]
  apply (eq_sub_iff_add_eq).mpr
  have recurrence := (gramSchmidt_def'' 𝕜 (ordered raw) current).symm
  rw [← Finset.sum_attach,Finset.attach_eq_univ] at recurrence
  simpa only [projectionRatio] using recurrence

def coefficients (raw : ι → E) : Matrix ι (Index (𝕜 := 𝕜) raw) 𝕜 :=
  fun source index =>
    (‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ *
      gsCoefficients (𝕜 := 𝕜) raw index.val (Fintype.equivFin ι source)

theorem field_synthesis (raw : ι → E) (index : Index (𝕜 := 𝕜) raw) :
    field (𝕜 := 𝕜) raw index = ∑ source, coefficients (𝕜 := 𝕜) raw source index • raw source := by
  classical
  change (‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ •
    gramSchmidt 𝕜 (ordered raw) index.val = _
  calc
    _ = (‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ •
        (∑ source, gsCoefficients (𝕜 := 𝕜) raw index.val source • ordered raw source) :=
      congrArg (fun value => (‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ • value)
        (gs_coefficients_synthesis raw index.val)
    _ = ∑ source : Fin (Fintype.card ι),
        ((‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ *
          gsCoefficients (𝕜 := 𝕜) raw index.val source) • ordered raw source := by
      rw [Finset.smul_sum]
      simp only [← mul_smul]
    _ = _ := by
      simpa only [coefficients,ordered,Equiv.symm_apply_apply] using
        ((Fintype.equivFin ι).sum_comp (fun source : Fin (Fintype.card ι) =>
          ((‖gramSchmidt 𝕜 (ordered raw) index.val‖ : 𝕜)⁻¹ *
            gsCoefficients (𝕜 := 𝕜) raw index.val source) • ordered raw source)).symm

def rawCoordinates (raw : ι → E) : Matrix (Index (𝕜 := 𝕜) raw) ι 𝕜 :=
  fun index source => inner 𝕜 (field (𝕜 := 𝕜) raw index) (raw source)

theorem raw_synthesis (raw : ι → E) (source : ι) :
    raw source = ∑ index, rawCoordinates (𝕜 := 𝕜) raw index source • field (𝕜 := 𝕜) raw index := by
  classical
  have member : raw source ∈ Submodule.span 𝕜 (Set.range (field (𝕜 := 𝕜) raw)) := by
    rw [span_exact]
    exact Submodule.subset_span (Set.mem_range_self source)
  obtain ⟨coordinate,represented⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp member
  have recovered (index : Index (𝕜 := 𝕜) raw) :
      rawCoordinates (𝕜 := 𝕜) raw index source = coordinate index := by
    unfold rawCoordinates
    rw [← represented]
    exact (field_orthonormal raw).inner_right_fintype coordinate index
  simp only [recovered]
  exact represented.symm

theorem coefficient_gram (raw : ι → E) :
    (coefficients (𝕜 := 𝕜) raw).conjTranspose * Matrix.gram 𝕜 raw * coefficients (𝕜 := 𝕜) raw = 1 := by
  classical
  have synthesized :
      (coefficients (𝕜 := 𝕜) raw).conjTranspose * Matrix.gram 𝕜 raw * coefficients (𝕜 := 𝕜) raw =
        gram (𝕜 := 𝕜) raw := by
    rw [Matrix.mul_assoc]
    ext left right
    change (star (fun source => coefficients (𝕜 := 𝕜) raw source left)) ⬝ᵥ
      (Matrix.gram 𝕜 raw *ᵥ (fun source => coefficients (𝕜 := 𝕜) raw source right)) =
        inner 𝕜 (field (𝕜 := 𝕜) raw left) (field (𝕜 := 𝕜) raw right)
    rw [Matrix.star_dotProduct_gram_mulVec]
    rw [← field_synthesis raw left,← field_synthesis raw right]
  exact synthesized.trans (gram_one raw)

end
end CPS1MolecularFrame.FiniteNormed
