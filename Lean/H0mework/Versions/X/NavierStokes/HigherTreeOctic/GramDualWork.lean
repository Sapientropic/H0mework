import H0mework.Versions.X.NavierStokes.HigherTreeOctic.GramDualPulse
import H0mework.Versions.X.NavierStokes.HigherTreeOctic.PrimitiveKernel
import H0mework.Versions.X.NavierStokes.HigherTreeOctic.TemporalEvolution

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeUnheatedTreeTime NativeEndpointVelocityCarrier
open NativeUnheatedOcticGramDualPulse (Space pulse)
noncomputable section
variable {nu : Viscosity}
abbrev Address := IntegerWavevector × NativeUnheatedOcticEightRows.Index
abbrev Test := lp (fun _ : IntegerWavevector => ℂ) 2
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)
local notation "parents" => NativeUnheatedOcticEightRows.parent slot leaf position newest
local notation "bases" => NativeUnheatedOcticEightRows.base slot leaf position newest

def nodes (entry : Address) : Fin 7 → Slot := parents entry.1 i j outside l m p q r s u v entry.2.1
def other (entry : Address) : IntegerWavevector := (nodes slot leaf position newest i j outside l m p q r s u v entry selected).1-entry.2.2
def rest (entry : Address) : ℝ := NativeUnheatedOcticThetaGram.damping (nu := nu)
  (nodes slot leaf position newest i j outside l m p q r s u v entry) selected
theorem rest_nonnegative (entry : Address) : 0 ≤ rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry :=
  NativeUnheatedOcticThetaGram.damping_nonnegative _ _
def slots (entry : Address) : Fin 7 → Slot := Fin.cons (other slot leaf position newest i j outside l m p q r s u v selected entry,b)
  (fun number : Fin 6 => nodes slot leaf position newest i j outside l m p q r s u v entry (selected.succAbove number))

theorem slots_frequency (entry : Address) :
    (∑ number : Fin 7, (slots slot leaf position newest i j outside l m p q r s u v selected b entry number).1) = entry.1-entry.2.2 := by
  have original := NativeUnheatedSepticSevenRows.nodes_frequency slot leaf position newest entry.1 i j outside l m p q r s u v entry.2.1
  rw [Fin.sum_univ_succAbove _ selected] at original
  unfold slots
  rw [Fin.sum_univ_succ]
  dsimp only [Fin.cons_zero, Fin.cons_succ, other, nodes, NativeUnheatedOcticEightRows.parent]
  simp only [Fin.cons_zero, Fin.cons_succ]
  convert! congrArg (fun wave => wave-entry.2.2) original using 1
  abel

def constant (test : Test) (entry : Address) : ℂ := star (test entry.1)*NativeUnheatedTreeLeaf.kernel
  (NativeUnheatedTreeNormalForm.normalizer nu (nodes slot leaf position newest i j outside l m p q r s u v entry)
    (bases entry.1 i j response outside l m p q r s u v nu entry.2.1))
  (nodes slot leaf position newest i j outside l m p q r s u v entry) selected a b

def coefficient (test : Test) (seed : GeneratedWholeRestartCurrent nu) (entry : Address) (time : ℝ) : ℂ :=
  constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry*
    product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time

def vector (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) : Space :=
  ∑ entry ∈ observed, lp.single 2 entry.2.2 (coefficient slot leaf position newest i j response outside l m p q r s u v selected a b test seed entry time •
    pulse (nu := nu) (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry)
      (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected entry) (other slot leaf position newest i j outside l m p q r s u v selected entry))

def original (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) : ℂ :=
  ∑ entry ∈ observed, star (test entry.1)*NativeUnheatedOcticPrimitiveKernel.primitive slot leaf position newest entry.1
    i j response outside l m p q r s u v selected a b seed entry.2 time

def bare (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) : ℂ :=
  ∑ entry ∈ observed, star (test entry.1)*NativeUnheatedTreeLeaf.term seed
    (nodes slot leaf position newest i j outside l m p q r s u v entry)
    (NativeUnheatedTreeNormalForm.normalizer nu (nodes slot leaf position newest i j outside l m p q r s u v entry)
      (bases entry.1 i j response outside l m p q r s u v nu entry.2.1)) selected a b entry.2.2 time

theorem pairing_original (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) :
    inner ℂ (NativeUnheatedOcticGramDualPulse.source (nu := nu) (NativeUnifiedCompleteSource.source seed time).fst a)
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) =
      original slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time-
        bare slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time := by
  simp only [vector, inner_sum, original, bare, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro entry _
  rw [NativeUnheatedOcticGramDualPulse.source_single]
  rw [NativeUnheatedOcticPrimitiveKernel.primitive_transfer, NativeUnheatedOcticThetaGram.ratio_original]
  simp only [coefficient, constant, product, slots, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    NativeUnheatedTriadRows.velocity_original, NativeUnheatedTreeLeaf.term, NativeUnheatedTreeLeaf.raw,
    NativeUnheatedTreeLeaf.remaining, rest, other, nodes, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_one]
  ring

def work (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) : ℝ :=
  ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2

theorem work_formula (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) :
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time =
    (∑ first ∈ observed, ∑ last ∈ observed, if first.2.2=last.2.2 then
      star (coefficient slot leaf position newest i j response outside l m p q r s u v selected a b test seed first time)*
        coefficient slot leaf position newest i j response outside l m p q r s u v selected a b test seed last time*
          (NativeUnheatedOcticThetaGram.kernel nu
            (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected first+rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected last)
            (other slot leaf position newest i j outside l m p q r s u v selected first)
            (other slot leaf position newest i j outside l m p q r s u v selected last) : ℂ) else 0).re := by
  unfold work
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ _ _).re = _
  congr 1
  simp only [vector, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro last _
  exact NativeUnheatedOcticGramDualPulse.single_inner _ _ _ _ _ _ _ _ _ _

theorem pairing_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) :
    ‖original slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time-
      bare slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2 ≤
      NativeUnifiedCompleteSource.budget seed^2*work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time := by
  rw [← pairing_original]
  have paid := (norm_inner_le_norm (𝕜 := ℂ)
    (NativeUnheatedOcticGramDualPulse.source (nu := nu) (NativeUnifiedCompleteSource.source seed time).fst a)
    (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)).trans (mul_le_mul_of_nonneg_right
    ((NativeUnheatedOcticGramDualPulse.source_bound (nu := nu) (NativeUnifiedCompleteSource.source seed time).fst a).trans
      (NativeUnheatedSourceWeightedTail.velocity_bound seed time)) (norm_nonneg _))
  simpa only [mul_pow, work] using pow_le_pow_left₀ (norm_nonneg _) paid 2

def basis (test : Test) (entry : Address) : Space :=
  lp.single 2 entry.2.2 (constant (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry •
    pulse (nu := nu) (rest (nu := nu) slot leaf position newest i j outside l m p q r s u v selected entry)
      (rest_nonnegative slot leaf position newest i j outside l m p q r s u v selected entry)
      (other slot leaf position newest i j outside l m p q r s u v selected entry))

theorem vector_source (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) :
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time =
      ∑ entry ∈ observed, product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry := by
  simp only [vector, coefficient, basis, ← lp.single_smul, smul_smul, mul_comm]

def vectorRate (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address) (time : ℝ) : Space :=
  ∑ entry ∈ observed,
    (forcing seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time-
      sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry) •
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time) •
      basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry

theorem vectorRate_integrable (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    IntervalIntegrable (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed) volume first last := by
  have paid (entry : Address) := (NativeUnheatedTreeWindow.forcing_integrable seed
    (slots slot leaf position newest i j outside l m p q r s u v selected b entry) first last first0 last0).sub
      (((NativeUnheatedTreeTime.product_ac seed
        (slots slot leaf position newest i j outside l m p q r s u v selected b entry) first last first0 last0).continuousOn.const_smul
          (sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry))).intervalIntegrable)
  convert!
    (IntervalIntegrable.sum observed (fun entry _ =>
      ⟨(paid entry).1.smul_const (basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry),
       (paid entry).2.smul_const (basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)⟩)) using 1
  funext time
  simp only [vectorRate, Finset.sum_apply, Pi.smul_apply]

theorem vector_write (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last-
      vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first =
      ∫ time in first..last, vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time := by
  rw [vector_source, vector_source, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul, NativeUnheatedTreeTime.product_write seed _ first last first0 last0, ← intervalIntegral.integral_smul_const]
  apply Eq.symm
  apply intervalIntegral.integral_finsetSum
  intro entry _
  have paid := (NativeUnheatedTreeWindow.forcing_integrable seed
    (slots slot leaf position newest i j outside l m p q r s u v selected b entry) first last first0 last0).sub
      (((NativeUnheatedTreeTime.product_ac seed
        (slots slot leaf position newest i j outside l m p q r s u v selected b entry) first last first0 last0).continuousOn.const_smul
          (sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry))).intervalIntegrable)
  exact ⟨paid.1.smul_const _, paid.2.smul_const _⟩

theorem work_write (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last-
      work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first =
      ∫ time in first..last, inner ℝ
        (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last+
          vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first)
        (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) := by
  have polarization (left right : Space) : ‖right‖^2-‖left‖^2 = inner ℝ (right+left) (right-left) := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      real_inner_comm left right]
    ring
  rw [work, work, polarization, vector_write slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0]
  exact ((innerSL ℝ _).intervalIntegral_comp_comm
    (vectorRate_integrable slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0)).symm

theorem vector_next (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed (step.2.clockAdvance+time) =
      vector slot leaf position newest i j response outside l m p q r s u v selected a b test step.1 observed time := by
  simp only [vector_source, NativeUnheatedTreeTime.product_next seed _ step generated time nonnegative]

theorem work_next (test : Test) (seed : GeneratedWholeRestartCurrent nu) (observed : Finset Address)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed (step.2.clockAdvance+time) =
      work slot leaf position newest i j response outside l m p q r s u v selected a b test step.1 observed time := by
  rw [work, work, vector_next slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
