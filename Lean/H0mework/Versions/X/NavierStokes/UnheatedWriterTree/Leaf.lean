import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.FivePositive
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Time
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeLeaf
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient NativeUnheatedTriadChannels
open NativeUnheatedQuinticTime NativeUnheatedHalfNonlinear
noncomputable section
variable {nu : Viscosity}

variable {n : ℕ}

abbrev Nodes (n : ℕ) := Fin (n+1) → Slot

def remaining (U : NativeUnheatedTriadSum.E) (nodes : Nodes n) (leaf : Fin (n+1)) : ℂ :=
  ∏ position : Fin n, U (nodes (leaf.succAbove position)).1 (nodes (leaf.succAbove position)).2

theorem remaining_erase (U : NativeUnheatedTriadSum.E) (nodes : Nodes n) (leaf : Fin (n+1)) :
    remaining U nodes leaf = ∏ position ∈ Finset.univ.erase leaf, U (nodes position).1 (nodes position).2 := by
  let f (position : Fin (n+1)) := U (nodes position).1 (nodes position).2
  let g (position : Fin (n+1)) := if position=leaf then (1 : ℂ) else f position
  calc
    _ = ∏ position : Fin (n+1), g position := by
      rw [Fin.prod_univ_succAbove _ leaf]
      simp only [g, if_true, Fin.succAbove_ne, if_false, one_mul, remaining, f]
    _ = ∏ position ∈ Finset.univ.erase leaf, g position := (Finset.prod_erase _ (by simp only [g, if_true])).symm
    _ = _ := Finset.prod_congr rfl fun position inside => if_neg (Finset.mem_erase.mp inside).1

def slots (nodes : Nodes n) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) : Fin (n+2) → Slot :=
  Fin.cons (inside,p) (Fin.cons ((nodes leaf).1-inside,q) (fun position => nodes (leaf.succAbove position)))

theorem slots_frequency (nodes : Nodes n) (leaf : Fin (n+1)) (p q : Coordinate) (inside : IntegerWavevector) :
    (∑ position : Fin (n+2), (slots nodes leaf p q inside position).1) = ∑ position : Fin (n+1), (nodes position).1 := by
  rw [Fin.sum_univ_succAbove _ leaf]
  simp only [Fin.sum_univ_succ, slots, Fin.cons_zero, Fin.cons_succ]
  abel

def positiveInput (value : NativeWholeResolvent.wholePhysical) (regular : H1 value)
    (leaf position : Fin (n+1)) : NativeUnheatedTriadSum.E :=
  if position=leaf then NativeUnheatedQuarticSource.scalarLift (NativeUnheatedQuinticPositive.envelope value regular)
    else wholeVelocity value.1

theorem input_product (value : NativeWholeResolvent.wholePhysical) (regular : H1 value) (leaf : Fin (n+1)) :
    (∏ position : Fin (n+1), ‖positiveInput value regular leaf position‖) ≤
      coefficient*gradientMass value*‖wholeVelocity value.1‖^n := by
  rw [Fin.prod_univ_succAbove _ leaf]
  simp only [positiveInput, if_true, Fin.succAbove_ne, if_false, NativeUnheatedQuarticSource.scalarLift_norm,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (NativeUnheatedQuinticPositive.envelope_bound value regular)
    (pow_nonneg (norm_nonneg _) n)

def kernel (z : ℂ) (nodes : Nodes n) (leaf : Fin (n+1)) (p q : Coordinate) : ℂ :=
  z*pressure (nodes leaf).1 p q (nodes leaf).2

def raw (U : NativeUnheatedTriadSum.E) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1))
    (p q : Coordinate) (inside : IntegerWavevector) : ℂ :=
  kernel z nodes leaf p q*(U inside p*U ((nodes leaf).1-inside) q)*remaining U nodes leaf

def term (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1))
    (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) : ℂ :=
  raw (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) nodes z leaf p q inside

theorem term_product (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1))
    (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) :
    term seed nodes z leaf p q inside time =
      kernel z nodes leaf p q*NativeUnheatedTreeTime.product seed (slots nodes leaf p q inside) time := by
  simp only [NativeUnheatedTreeTime.product, term, raw, Fin.prod_univ_succ, slots, Fin.cons_zero, Fin.cons_succ,
    NativeUnheatedTriadRows.velocity_original]
  unfold remaining
  ring

theorem raw_summable (U : NativeUnheatedTriadSum.E) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1)) (p q : Coordinate) :
    Summable (raw U nodes z leaf p q) :=
  ((NativeHigherTimeJets.mixed_pair_summable U U (nodes leaf).1 q p).mul_left (kernel z nodes leaf p q)).mul_right _

theorem inner_sum (U : NativeUnheatedTriadSum.E) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1)) (p q : Coordinate) :
    (∑' inside, raw U nodes z leaf p q inside) =
      kernel z nodes leaf p q*(∑' inside, U inside p*U ((nodes leaf).1-inside) q)*remaining U nodes leaf := by
  simp only [raw, tsum_mul_right, tsum_mul_left]

theorem positive_product (value : NativeWholeResolvent.wholePhysical) (regular : H1 value) (nodes : Nodes n) (leaf : Fin (n+1)) :
    (∏ position : Fin (n+1), positiveInput value regular leaf position
      (nodes position).1 (nodes position).2) =
      (NativeUnheatedQuinticPositive.envelope value regular (nodes leaf).1 : ℂ)*remaining (wholeVelocity value.1) nodes leaf := by
  have selected : positiveInput value regular leaf leaf (nodes leaf).1 (nodes leaf).2 =
      (NativeUnheatedQuinticPositive.envelope value regular (nodes leaf).1 : ℂ) := by
    simp only [positiveInput]
    rfl
  rw [Fin.prod_univ_succAbove _ leaf, selected]
  congr 1
  apply Finset.prod_congr rfl
  intro position _
  simp only [positiveInput, if_neg (Fin.succAbove_ne leaf position)]

theorem fiber_bound (value : NativeWholeResolvent.wholePhysical) (regular : H1 value) (nodes : Nodes n)
    (z : ℂ) (leaf : Fin (n+1)) (p q : Coordinate) :
    (∑' inside, ‖raw (wholeVelocity value.1) nodes z leaf p q inside‖) ≤
      ‖(z*(quarter (nodes leaf).1 : ℂ))*(∏ position : Fin (n+1),
        positiveInput value regular leaf position (nodes position).1 (nodes position).2)‖ := by
  let U := wholeVelocity value.1
  have major (inside : IntegerWavevector) :
      ‖U inside p*U ((nodes leaf).1-inside) q‖ ≤
        NativeMovingCriticalProduct.amplitude U inside*NativeMovingCriticalProduct.amplitude U ((nodes leaf).1-inside) := by
    rw [norm_mul]
    exact mul_le_mul (by simpa only [NativeUnheatedQuarticEnvelope.amplitude_original] using
      NativeUnheatedPairInverseFlux.coordinate_bound U inside p)
      (by simpa only [NativeUnheatedQuarticEnvelope.amplitude_original] using
        NativeUnheatedPairInverseFlux.coordinate_bound U ((nodes leaf).1-inside) q)
      (norm_nonneg _) (norm_nonneg _)
  have pair := ((NativeHigherTimeJets.mixed_pair_summable U U (nodes leaf).1 q p).norm).tsum_le_tsum major
    (NativeUnheatedQuarticEnvelope.pair_summable value (nodes leaf).1)
  have paid := mul_le_mul (NativeUnheatedQuinticPositive.pressure_bound z (nodes leaf).1 p q (nodes leaf).2)
    pair (tsum_nonneg fun _ => norm_nonneg _) (mul_nonneg (norm_nonneg _) (quarter_nonnegative _))
  calc
    _ = (‖kernel z nodes leaf p q‖*(∑' inside, ‖U inside p*U ((nodes leaf).1-inside) q‖))*‖remaining U nodes leaf‖ := by
      simp only [raw, norm_mul, tsum_mul_right, tsum_mul_left, U]
    _ ≤ (‖z*(quarter (nodes leaf).1 : ℂ)‖*quarter (nodes leaf).1)*
        NativeUnheatedQuarticEnvelope.row value (nodes leaf).1*‖remaining U nodes leaf‖ :=
      mul_le_mul_of_nonneg_right paid (norm_nonneg _)
    _ = _ := by
      rw [positive_product]
      simp only [norm_mul, Complex.norm_real,
        NativeUnheatedQuinticPositive.envelope_apply, Real.norm_of_nonneg (quarter_nonnegative _),
        Real.norm_of_nonneg (NativeUnheatedQuarticEnvelope.row_nonnegative value _), U]
      ring

theorem source_expansion (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes n) (z : ℂ) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    z*NativeUnheatedTreeTime.forcing seed nodes time =
      ∑ leaf : Fin (n+1), ∑ p : Coordinate, ∑ q : Coordinate, ∑' inside, term seed nodes z leaf p q inside time := by
  have grouped : NativeUnheatedTreeTime.forcing seed nodes time =
      ∑ leaf : Fin (n+1), NativeUnheatedTriadRows.action seed time (nodes leaf).1 (nodes leaf).2*
        remaining (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) nodes leaf := by
    simp only [NativeUnheatedTreeTime.forcing, NativeUnheatedTreeTime.cofactor,
      remaining_erase, NativeUnheatedTriadRows.velocity_original]
  rw [grouped, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leaf _
  rw [NativeUnheatedQuarticRows.source_action seed time nonnegative regular, NativeUnheatedCubicIdentity.row_channels]
  simp only [term, inner_sum, kernel, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem term_next (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes n) (z : ℂ) (leaf : Fin (n+1))
    (p q : Coordinate) (inside : IntegerWavevector)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    term seed nodes z leaf p q inside (response.2.clockAdvance+time) = term response.1 nodes z leaf p q inside time := by
  simp only [term, NativeUnifiedCompleteSource.source_generated_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeLeaf
