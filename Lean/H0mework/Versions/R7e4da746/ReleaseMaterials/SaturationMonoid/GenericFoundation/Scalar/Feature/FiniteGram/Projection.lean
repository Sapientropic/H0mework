import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.Projection
open scoped InnerProductSpace

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (source : ι → H)

def synthesis : Coordinates ι →ₗ[ℂ] H where
  toFun a := ∑ i, a i • source i
  map_add' a b := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z a := by
    simp only [PiLp.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

def gram : Matrix ι ι ℂ := Matrix.gram ℂ source
def rhs (increment : H) : Coordinates ι := WithLp.toLp 2 (fun i => inner ℂ (source i) increment)

theorem action_read (a : Coordinates ι) (i : ι) :
    action (gram source) a i = inner ℂ (source i) (synthesis source a) := by
  change (∑ j, inner ℂ (source i) (source j) * a j) = _
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq ι] in
theorem synthesis_inner (a : Coordinates ι) (increment : H) :
    inner ℂ (synthesis source a) increment = inner ℂ a (rhs source increment) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [synthesis, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_smul_left]
  change (∑ i, star (a i) * inner ℂ (source i) increment) =
    ∑ i, inner ℂ (source i) increment * star (a i)
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem kernel_synthesis : Kernel (gram source) ≤ (synthesis source).ker := by
  intro a zero
  have pair : inner ℂ (synthesis source a) (synthesis source a) = 0 := by
    rw [synthesis_inner]
    have zeroRhs : rhs source (synthesis source a) = 0 := by
      ext i
      change inner ℂ (source i) (synthesis source a) = 0
      rw [← action_read, show action (gram source) a = 0 from zero]
      rfl
    rw [zeroRhs, inner_zero_right]
  exact inner_self_eq_zero.mp pair

theorem compatible (increment : H) : Compatible (gram source) (rhs source increment) := by
  intro a zero
  rw [← synthesis_inner, show synthesis source a = 0 from kernel_synthesis source zero,
    inner_zero_left]

def coefficients (increment : H) : Coordinates ι :=
  SourceGeneratedFiniteGram.coefficients (gram source) (Matrix.isHermitian_gram ℂ source)
    (rhs source increment) (compatible source increment)

/-- The operation is built from the source Gram image inverse; projection is a later readback. -/
def predictable (increment : H) : H :=
  sourceEffect (gram source) (Matrix.isHermitian_gram ℂ source)
    (rhs source increment) (compatible source increment) (synthesis source) (kernel_synthesis source)

theorem equation (increment : H) :
    action (gram source) (coefficients source increment) = rhs source increment :=
  SourceGeneratedFiniteGram.equation _ _ _ _

theorem full_fibre (increment : H) (a : Coordinates ι) :
    action (gram source) a = rhs source increment ↔
      a - coefficients source increment ∈ Kernel (gram source) :=
  SourceGeneratedFiniteGram.full_fibre _ _ _ _ a

theorem predictable_source (increment : H) :
    predictable source increment = synthesis source (coefficients source increment) :=
  source_effect_eq _ _ _ _ _ _

abbrev sourceSpan := (synthesis source).range

theorem predictable_mem (increment : H) : predictable source increment ∈ sourceSpan source :=
  ⟨coefficients source increment, (predictable_source source increment).symm⟩

theorem residual_orthogonal (increment : H) :
    increment - predictable source increment ∈ (sourceSpan source)ᗮ := by
  rintro _ ⟨a, rfl⟩
  rw [inner_sub_right, synthesis_inner, predictable_source, synthesis_inner]
  have generated : rhs source (synthesis source (coefficients source increment)) = rhs source increment := by
    ext i
    change inner ℂ (source i) (synthesis source (coefficients source increment)) = _
    rw [← action_read, equation]
  rw [generated, sub_self]

theorem predictable_readback (increment : H) :
    predictable source increment = (sourceSpan source).starProjection increment :=
  (Submodule.eq_starProjection_of_mem_orthogonal
    (predictable_mem source increment) (residual_orthogonal source increment)).symm

def predictableCLM : H →L[ℂ] H where
  toFun := predictable source
  map_add' x y := by simp only [predictable_readback, map_add]
  map_smul' z x := by simp only [predictable_readback, map_smul, RingHom.id_apply]
  cont := (sourceSpan source).starProjection.continuous.congr
    (fun x => (predictable_readback source x).symm)

def innovationCLM : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - predictableCLM source

theorem innovation_value (increment : H) :
    innovationCLM source increment = increment - predictable source increment := rfl

theorem innovation_orthogonal (increment : H) :
    innovationCLM source increment ∈ (sourceSpan source)ᗮ :=
  residual_orthogonal source increment

end SourceGeneratedFiniteGram.Projection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
