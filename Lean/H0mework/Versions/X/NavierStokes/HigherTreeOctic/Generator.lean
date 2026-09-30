import H0mework.Versions.X.NavierStokes.HigherTreeOctic.GramDualWork

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeUnheatedTreeTime NativeUnheatedOcticThetaGram
open NativeUnheatedOcticGramDual
open NativeUnheatedTreeRateChange
namespace NativeUnheatedOcticGramDual
noncomputable section

theorem kernel_generator {nu : Viscosity} (rest : ℝ) (rest0 : 0 ≤ rest)
    (first last : IntegerWavevector) :
    (rest + rate nu first + rate nu last) * kernel nu rest first last =
      crossRate nu first last := by
  by_cases zero : rest + rate nu first + rate nu last = 0
  · rw [zero, zero_mul]
    have bound := NativeUnheatedTreeRateTransfer.cross_bound (nu := nu) first last
    have comparison : NativeUnheatedStressPairEvolution.decay nu first last =
        rate nu first + rate nu last := by unfold NativeUnheatedStressPairEvolution.decay rate; ring
    rw [comparison] at bound
    have vanishing : |crossRate nu first last| = 0 := by
      apply le_antisymm _ (abs_nonneg _)
      linarith [rate_nonnegative (nu := nu) first, rate_nonnegative (nu := nu) last]
    exact (abs_eq_zero.mp vanishing).symm
  · unfold kernel
    field_simp [zero]

theorem slots_rate {nu : Viscosity}
    (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (i j outside l m p q r s u v : Coordinate) (selected : Fin 7) (b : Coordinate)
    (entry : NativeUnheatedOcticGramDual.Address) :
    sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry) =
      rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry +
      rate nu (other slot leaf position newest i j outside l m p q r s u v selected entry) := by
  unfold sumRate slots rest NativeUnheatedOcticThetaGram.damping rate
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
  ring

theorem pulse_generator {nu : Viscosity}
    (firstRest lastRest : ℝ) (first0 : 0 ≤ firstRest) (last0 : 0 ≤ lastRest)
    (first last : IntegerWavevector) :
    ((firstRest + rate nu first + (lastRest + rate nu last) : ℝ) : ℂ) *
      inner ℂ (NativeUnheatedOcticGramDualPulse.pulse (nu := nu) firstRest first0 first)
        (NativeUnheatedOcticGramDualPulse.pulse (nu := nu) lastRest last0 last) =
      inner ℂ (NativeUnheatedOcticGramDualPulse.profile (nu := nu) firstRest first 0)
        (NativeUnheatedOcticGramDualPulse.profile (nu := nu) lastRest last 0) := by
  rw [NativeUnheatedOcticGramDualPulse.pulse_inner,
    NativeUnheatedOcticGramDualPulse.profile_inner, feature_product]
  simp only [mul_zero, Real.exp_zero, mul_one]
  rw [← Complex.ofReal_mul]
  congr 1
  convert kernel_generator (nu := nu) (firstRest+lastRest) (add_nonneg first0 last0) first last using 1; ring

private theorem finite_pair_generator {ι E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (observed : Finset ι) (u d : ι → E) (b : ι → F)
    (pair : ∀ first ∈ observed, ∀ last ∈ observed,
      inner ℂ (u first) (d last) + inner ℂ (d first) (u last) = inner ℂ (b first) (b last)) :
    inner ℂ (∑ entry ∈ observed, u entry) (∑ entry ∈ observed, d entry) +
    inner ℂ (∑ entry ∈ observed, d entry) (∑ entry ∈ observed, u entry) =
    inner ℂ (∑ entry ∈ observed, b entry) (∑ entry ∈ observed, b entry) := by
  simp only [sum_inner, inner_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first firstIn
  apply Finset.sum_congr rfl
  intro last lastIn
  exact pair last lastIn first firstIn

private theorem real_inner_of_complex_re {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
    (first last : E) : inner ℝ first last = (inner ℂ first last).re := by
  have complex := norm_add_sq (𝕜 := ℂ) first last
  have real := norm_add_sq_real first last
  simp only [RCLike.re_to_complex] at complex
  linarith

abbrev Boundary := lp (fun _ : IntegerWavevector => NativeUnheatedOcticGramDualPulse.Vector) 2
variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

def boundaryBasis (test : Test) (entry : Address) : Boundary :=
  lp.single 2 entry.2.2
    (constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry •
      NativeUnheatedOcticGramDualPulse.profile (nu := nu)
        (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry)
        (other slot leaf position newest i j outside l m p q r s u v selected entry) 0)

theorem basis_generator (test : Test) (first last : Address) :
    (((sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b first) +
      sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b last)) : ℝ) : ℂ) *
      inner ℂ (basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first)
        (basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last) =
      inner ℂ (boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first)
        (boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last) := by
  by_cases same : first.2.2 = last.2.2
  · simp only [basis, boundaryBasis, lp.inner_single_left, lp.single_apply,
      same, Pi.single_eq_same, inner_smul_left, inner_smul_right, starRingEnd_apply]
    rw [slots_rate slot leaf position newest i j outside l m p q r s u v selected b first,
      slots_rate slot leaf position newest i j outside l m p q r s u v selected b last]
    have generator := pulse_generator (nu := nu)
      (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected first)
      (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected last)
      (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected first)
      (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected last)
      (other slot leaf position newest i j outside l m p q r s u v selected first)
      (other slot leaf position newest i j outside l m p q r s u v selected last)
    have multiplied := congrArg (fun z : ℂ =>
      constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last *
      star (constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first) * z) generator
    convert multiplied using 1 <;> ring
  · simp only [basis, boundaryBasis, lp.inner_single_left, lp.single_apply,
      Pi.single_eq_of_ne same, inner_zero_right, mul_zero]

def boundaryVector (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) : Boundary :=
  ∑ entry ∈ observed,
    product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
      boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry

def dampingVector (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) : NativeUnheatedOcticGramDualPulse.Space :=
  ∑ entry ∈ observed,
    (sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry) •
      product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time) •
      basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry

def forcingVector (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) : NativeUnheatedOcticGramDualPulse.Space :=
  ∑ entry ∈ observed,
    forcing seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
      basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry

theorem vectorRate_split (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) :
    vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time =
      forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time -
      dampingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time := by
  simp only [vectorRate, forcingVector, dampingVector, sub_smul, Finset.sum_sub_distrib]

private theorem pair_dissipation (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (time : ℝ) (first last : Address) :
    inner ℂ
      (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b first) time •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first)
      ((sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b last) •
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b last) time) •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last) +
    inner ℂ
      ((sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b first) •
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b first) time) •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first)
      (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b last) time •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last) =
    inner ℂ
      (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b first) time •
        boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first)
      (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b last) time •
        boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test last) := by
  simp only [inner_smul_left, inner_smul_right, starRingEnd_apply, Complex.real_smul,
    map_mul]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  have generator := basis_generator (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test first last
  simp only [Complex.ofReal_add] at generator
  linear_combination ((starRingEnd ℂ) (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b first) time) *
    product seed (slots slot leaf position newest i j outside l m p q r s u v selected b last) time) * generator

theorem vector_dissipation_complex (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) :
    inner ℂ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (dampingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) +
    inner ℂ
      (dampingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) =
    inner ℂ
      (boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) := by
  let vecTerm : Address → NativeUnheatedOcticGramDualPulse.Space := fun entry =>
    product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
      basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry
  let dampTerm : Address → NativeUnheatedOcticGramDualPulse.Space := fun entry =>
    (sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry) •
      product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time) •
      basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry
  let bdy : Address → Boundary := fun entry =>
    product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
      boundaryBasis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry
  have pair (first : Address) (_ : first ∈ observed) (last : Address) (_ : last ∈ observed) :
      inner ℂ (vecTerm first) (dampTerm last) + inner ℂ (dampTerm first) (vecTerm last) = inner ℂ (bdy first) (bdy last) := by
    exact pair_dissipation (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed time first last
  have paid := finite_pair_generator observed vecTerm dampTerm bdy pair
  simpa only [vecTerm, dampTerm, bdy, vector_source, dampingVector, boundaryVector] using paid

theorem vector_dissipation_real (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) :
    2 * inner ℝ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (dampingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) =
    ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2 := by
  let v0 := vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
  let d0 := dampingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
  let b0 := boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
  change 2 * inner ℝ v0 d0 = ‖b0‖^2
  have paid : (inner ℂ v0 d0 + inner ℂ d0 v0).re = (inner ℂ b0 b0).re :=
    congrArg Complex.re (vector_dissipation_complex (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
  rw [Complex.add_re] at paid
  have symmetry : (inner ℂ d0 v0).re = (inner ℂ v0 d0).re := by
    simpa using (inner_re_symm (𝕜 := ℂ) v0 d0).symm
  have normed : (inner ℂ b0 b0).re = ‖b0‖^2 := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) b0).symm
  have realread : inner ℝ v0 d0 = (inner ℂ v0 d0).re := real_inner_of_complex_re v0 d0
  rw [symmetry, normed, ← realread] at paid
  linarith

end
end NativeUnheatedOcticGramDual
end SaturationMonoid.NavierStokes
