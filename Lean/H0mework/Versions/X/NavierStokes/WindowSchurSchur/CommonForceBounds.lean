import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CommonForceTime
import H0mework.Versions.X.NavierStokes.WindowSchurFrozen.EffectiveBounds
import H0mework.Versions.X.NavierStokes.WindowSchurMean.JetEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCommonForceBounds
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryHeatDual (energy heat heatEnergy)
open NativeWindowHistoryHeatSize (size)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
open NativeWindowHistoryCommonForceTime (jet)
open NativeWindowHistoryEffectiveBounds (radius)
open NativeWindowHistorySchurForm (cap)
noncomputable section
variable {nu : Viscosity}

def loadRadius (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ :=
  ∑ i∈Finset.range (order+1),(order.choose i : ℝ)*cap seed horizon*radius seed horizon i*
    Real.sqrt (NativeWindowHistoryMeanJetEnergy.budget seed (order-i) horizon)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : ℝ := (loadRadius seed horizon order)^2

theorem loadRadius_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : 0 ≤ loadRadius seed horizon order :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)) (NativeWindowHistoryEffectiveBounds.radius_nonnegative seed horizon i))
      (Real.sqrt_nonneg _)

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (order : ℕ) : 0 ≤ budget seed horizon order := sq_nonneg _

theorem source_term_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M left right : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    size nu M (heat nu M (NativeWindowHistoryEffectiveTime.jet seed M left time (physicalJet seed M right time))) ≤
      cap seed horizon*radius seed horizon left*Real.sqrt (NativeWindowHistoryMeanJetEnergy.budget seed right horizon) := by
  have paid := (NativeWindowHistoryEffectiveBounds.source_jet_bound seed horizon M left time inside (physicalJet seed M right time)).trans
    (mul_le_mul_of_nonneg_left (NativeWindowHistoryMeanJetEnergy.source_energy seed right horizon M time inside) (sq_nonneg _))
  have source := Real.sqrt_le_sqrt paid
  rw [NativeWindowHistoryHeatDual.heatEnergy_self,Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (mul_nonneg (NativeWindowHistorySchurForm.cap_nonnegative seed horizon)
      (NativeWindowHistoryEffectiveBounds.radius_nonnegative seed horizon left))] at source
  exact source

theorem source_size_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    size nu M (heat nu M (jet seed M order time)) ≤ loadRadius seed horizon order := by
  rw [NativeWindowHistoryCommonForceTime.jet_product,map_sum]
  have triangle := NativeWindowHistoryHeatSize.size_sum nu M (Finset.range (order+1))
    (fun i => heat nu M (order.choose i • NativeWindowHistoryEffectiveTime.jet seed M i time (physicalJet seed M (order-i) time)))
  refine triangle.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_nsmul]
  have source := (NativeWindowHistoryHeatSize.size_nsmul nu M (order.choose i) _).trans
    (mul_le_mul_of_nonneg_left (source_term_bound seed horizon M i (order-i) time inside) (Nat.cast_nonneg _))
  exact source.trans_eq (by ring)

theorem source_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    heatEnergy nu M (jet seed M order time) ≤ budget seed horizon order := by
  have source := pow_le_pow_left₀ (NativeWindowHistoryHeatSize.size_nonnegative nu M (heat nu M (jet seed M order time)))
    (source_size_bound seed horizon M order time inside) 2
  simpa only [NativeWindowHistoryHeatSize.size_square,← NativeWindowHistoryHeatDual.heatEnergy_self,budget] using source

theorem source_pairing_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M order : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    |inner ℝ (includeCLM (modes M) (modes_closed M) v)
      (iteratedDeriv order (NativeWindowHistorySchurCompletion.commonForce seed M) time)| ≤
        size nu M v*loadRadius seed horizon order := by
  rw [← NativeWindowHistoryCommonForceTime.whole_iterated,include_inner (modes M) (modes_zero M),restrict_include]
  have paid := (NativeWindowHistoryHeatDual.dual_pairing_bound nu M v (jet seed M order time)).trans
    (mul_le_mul_of_nonneg_left (source_bound seed horizon M order time inside) (NativeWindowHistoryHeatDual.energy_nonnegative nu M v))
  have source := Real.sqrt_le_sqrt paid
  simpa only [budget,Real.sqrt_sq_eq_abs,Real.sqrt_mul (NativeWindowHistoryHeatDual.energy_nonnegative nu M v),
    Real.sqrt_sq (loadRadius_nonnegative seed horizon order),size] using source

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCommonForceBounds
