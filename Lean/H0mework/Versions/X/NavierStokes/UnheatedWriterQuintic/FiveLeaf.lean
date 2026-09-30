import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.FivePositive
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.NormalForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticLeaf
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeEndpointVelocityCarrier NativeWholeH1Mixed NativeUnheatedSourceGradient NativeUnheatedTriadChannels
open NativeUnheatedQuinticTime NativeUnheatedHalfNonlinear
noncomputable section
variable {nu : Viscosity}

abbrev Nodes := Fin 4 → Slot

def remaining (U : NativeUnheatedTriadSum.E) (nodes : Nodes) (leaf : Fin 4) : ℂ :=
  ∏ position : Fin 3, U (nodes (leaf.succAbove position)).1 (nodes (leaf.succAbove position)).2

def slots (nodes : Nodes) (leaf : Fin 4) (p q : Coordinate) (inside : IntegerWavevector) : Fin 5 → Slot :=
  ![(inside,p), ((nodes leaf).1-inside,q), nodes (leaf.succAbove 0), nodes (leaf.succAbove 1), nodes (leaf.succAbove 2)]

def kernel (z : ℂ) (nodes : Nodes) (leaf : Fin 4) (p q : Coordinate) : ℂ :=
  z*pressure (nodes leaf).1 p q (nodes leaf).2

def raw (U : NativeUnheatedTriadSum.E) (nodes : Nodes) (z : ℂ) (leaf : Fin 4)
    (p q : Coordinate) (inside : IntegerWavevector) : ℂ :=
  kernel z nodes leaf p q*(U inside p*U ((nodes leaf).1-inside) q)*remaining U nodes leaf

def term (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes) (z : ℂ) (leaf : Fin 4)
    (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) : ℂ :=
  raw (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) nodes z leaf p q inside

theorem term_original (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes) (z : ℂ) (leaf : Fin 4)
    (p q : Coordinate) (inside : IntegerWavevector) (time : ℝ) :
    term seed nodes z leaf p q inside time = kernel z nodes leaf p q*product seed
      (slots nodes leaf p q inside 0) (slots nodes leaf p q inside 1) (slots nodes leaf p q inside 2)
      (slots nodes leaf p q inside 3) (slots nodes leaf p q inside 4) time := by
  simp only [term, raw, product, NativeUnheatedTriadRows.velocity_original, slots,
    Matrix.cons_val_zero, Matrix.cons_val_one, remaining, Fin.prod_univ_three]
  change _ = kernel z nodes leaf p q*(
    wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst inside p*
    wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst ((nodes leaf).1-inside) q*
    wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes (leaf.succAbove 0)).1 (nodes (leaf.succAbove 0)).2*
    wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes (leaf.succAbove 1)).1 (nodes (leaf.succAbove 1)).2*
    wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes (leaf.succAbove 2)).1 (nodes (leaf.succAbove 2)).2)
  ring

theorem raw_summable (U : NativeUnheatedTriadSum.E) (nodes : Nodes) (z : ℂ) (leaf : Fin 4) (p q : Coordinate) :
    Summable (raw U nodes z leaf p q) :=
  ((NativeHigherTimeJets.mixed_pair_summable U U (nodes leaf).1 q p).mul_left (kernel z nodes leaf p q)).mul_right _

theorem inner_sum (U : NativeUnheatedTriadSum.E) (nodes : Nodes) (z : ℂ) (leaf : Fin 4) (p q : Coordinate) :
    (∑' inside, raw U nodes z leaf p q inside) =
      kernel z nodes leaf p q*(∑' inside, U inside p*U ((nodes leaf).1-inside) q)*remaining U nodes leaf := by
  simp only [raw, tsum_mul_right, tsum_mul_left]

theorem positive_product (value : NativeWholeResolvent.wholePhysical) (regular : H1 value) (nodes : Nodes) (leaf : Fin 4) :
    (∏ position : Fin 4, NativeUnheatedQuinticPositive.input value regular leaf position
      (nodes position).1 (nodes position).2) =
      (NativeUnheatedQuinticPositive.envelope value regular (nodes leaf).1 : ℂ)*remaining (wholeVelocity value.1) nodes leaf := by
  have selected : NativeUnheatedQuinticPositive.input value regular leaf leaf (nodes leaf).1 (nodes leaf).2 =
      (NativeUnheatedQuinticPositive.envelope value regular (nodes leaf).1 : ℂ) := by
    simp only [NativeUnheatedQuinticPositive.input]
    rfl
  rw [Fin.prod_univ_succAbove _ leaf, selected]
  congr 1
  apply Finset.prod_congr rfl
  intro position _
  simp only [NativeUnheatedQuinticPositive.input, if_neg (Fin.succAbove_ne leaf position)]

theorem fiber_bound (value : NativeWholeResolvent.wholePhysical) (regular : H1 value) (nodes : Nodes)
    (z : ℂ) (leaf : Fin 4) (p q : Coordinate) :
    (∑' inside, ‖raw (wholeVelocity value.1) nodes z leaf p q inside‖) ≤
      ‖(z*(quarter (nodes leaf).1 : ℂ))*(∏ position : Fin 4,
        NativeUnheatedQuinticPositive.input value regular leaf position (nodes position).1 (nodes position).2)‖ := by
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

theorem forcing_grouped (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes) (time : ℝ) :
    NativeUnheatedQuarticTime.forcing seed (nodes 0) (nodes 1) (nodes 2) (nodes 3) time =
      ∑ leaf : Fin 4, NativeUnheatedTriadRows.action seed time (nodes leaf).1 (nodes leaf).2*
        remaining (wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) nodes leaf := by
  simp only [NativeUnheatedQuarticTime.forcing, NativeUnheatedTriadRows.velocity_original,
    Fin.sum_univ_four, remaining, Fin.prod_univ_three]
  change _ =
    NativeUnheatedTriadRows.action seed time (nodes 0).1 (nodes 0).2*(
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 1).1 (nodes 1).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 2).1 (nodes 2).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 3).1 (nodes 3).2) +
    NativeUnheatedTriadRows.action seed time (nodes 1).1 (nodes 1).2*(
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 0).1 (nodes 0).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 2).1 (nodes 2).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 3).1 (nodes 3).2) +
    NativeUnheatedTriadRows.action seed time (nodes 2).1 (nodes 2).2*(
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 0).1 (nodes 0).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 1).1 (nodes 1).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 3).1 (nodes 3).2) +
    NativeUnheatedTriadRows.action seed time (nodes 3).1 (nodes 3).2*(
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 0).1 (nodes 0).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 1).1 (nodes 1).2*
      wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst (nodes 2).1 (nodes 2).2)
  ring

theorem source_expansion (seed : GeneratedWholeRestartCurrent nu) (nodes : Nodes) (z : ℂ) (time : ℝ)
    (nonnegative : 0 ≤ time) (regular : H1 (physical seed time nonnegative)) :
    z*NativeUnheatedQuarticTime.forcing seed (nodes 0) (nodes 1) (nodes 2) (nodes 3) time =
      ∑ leaf : Fin 4, ∑ p : Coordinate, ∑ q : Coordinate, ∑' inside, term seed nodes z leaf p q inside time := by
  rw [forcing_grouped, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leaf _
  rw [NativeUnheatedQuarticRows.source_action seed time nonnegative regular, NativeUnheatedCubicIdentity.row_channels]
  simp only [term, inner_sum, kernel, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticLeaf
