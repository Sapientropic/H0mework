import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Window
import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.GlobalWindow
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Rows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowPairActionRows
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow
noncomputable section
variable {nu : Viscosity}

def nodes (first last : IntegerWavevector) (output input : Coordinate) : Fin 2 → Slot :=
  ![(first,input), (last,output)]

def row (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : ℂ :=
  -product seed (nodes first last output input) time

def driver (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : ℂ :=
  -(forcing seed (nodes first last output input) time-
    sumRate nu (nodes first last output input) • product seed (nodes first last output input) time)

theorem row_original (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) :
    row seed first last output input time =
      -(NativeUnheatedTriadRows.velocity seed time first input*NativeUnheatedTriadRows.velocity seed time last output) := by
  simp [row,product,nodes,Fin.prod_univ_two]

theorem driver_original (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (time : ℝ) :
    driver seed first last output input time =
      -(NativeUnheatedTriadRows.action seed time first input*NativeUnheatedTriadRows.velocity seed time last output+
        NativeUnheatedTriadRows.velocity seed time first input*NativeUnheatedTriadRows.action seed time last output)-
      decay nu first last • row seed first last output input time := by
  simp [driver,forcing,cofactor,product,sumRate,nodes,row,decay,
    show (Finset.univ : Finset (Fin 2)) = {0,1} by decide,
    show ({0,1} : Finset (Fin 2)).erase 1 = {0} by decide]
  ring

theorem driver_rate_ae (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) : ∀ᵐ time : ℝ, 0 ≤ time →
    driver seed first last output input time =
      -(NativeUnheatedTriadRows.derivative seed time first input*NativeUnheatedTriadRows.velocity seed time last output+
        NativeUnheatedTriadRows.velocity seed time first input*NativeUnheatedTriadRows.derivative seed time last output) := by
  filter_upwards [productRate_split_ae seed (nodes first last output input)] with time actual nonnegative
  rw [driver, ← actual nonnegative]
  simp [productRate,cofactor,nodes,mul_comm,
    show (Finset.univ : Finset (Fin 2)) = {0,1} by decide,
    show ({0,1} : Finset (Fin 2)).erase 1 = {0} by decide]

theorem driver_pressure_ae (seed : GeneratedWholeRestartCurrent nu) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ first last output input,
    let U := NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst
    let N := fun wave => NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux U U wave)
    driver seed first last output input time =
      -(N first input*U last output+U first input*N last output)-decay nu first last • row seed first last output input time := by
  filter_upwards [NativeUnheatedSourceGradient.physical_H1_ae seed] with time regular nonnegative first last output input
  simp only [driver_original,NativeUnheatedTriadRows.velocity_original,
    NativeUnheatedQuarticRows.source_action seed time nonnegative (regular nonnegative)]

theorem driver_integrable (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (driver seed first last output input) volume a b := by
  have action := NativeUnheatedTreeWindow.forcing_integrable seed (nodes first last output input) a b a0 b0
  have pair := (product_ac seed (nodes first last output input) a b a0 b0).continuousOn.intervalIntegrable (μ := volume)
  convert! (action.sub (pair.smul (sumRate nu (nodes first last output input)))).neg using 1

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (first last : IntegerWavevector)
    (output input : Coordinate) (order : ℕ) (observation : ℝ) (valid : -1 ≤ observation) :
    (∫ time in observation+1..observation+2, kernelWeight order observation 0 time • driver seed first last output input time) =
      ∫ time in observation+1..observation+2, kernelWeight (order+1) observation 0 time • row seed first last output input time := by
  let slots := nodes first last output input
  have base := (product_ac seed slots (observation+1) (observation+2) (by linarith) (by linarith)).continuousOn.intervalIntegrable (μ := volume)
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n observation 0).continuousOn
  have q := (NativeUnheatedTreeWindow.forcing_integrable seed slots (observation+1) (observation+2)
    (by linarith) (by linarith)).continuousOn_smul (kernelWeight_continuous order observation 0).continuousOn
  have scaled : IntervalIntegrable (fun time => sumRate nu slots •
      (kernelWeight order observation 0 time • product seed slots time)) volume (observation+1) (observation+2) := by
    simpa only [Pi.smul_apply] using! (p order).smul (sumRate nu slots)
  have written := NativeUnheatedTreeWindow.weighted_write seed slots order observation 0
    (observation+1) (observation+2) (by linarith) (by linarith)
  have left : kernelWeight order observation 0 (observation+1) = 0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+1) = -1 by ring,kernelJet_right_zero]
  have right : kernelWeight order observation 0 (observation+2) = 0 := by
    simp only [kernelWeight,zero_add,show observation-(observation+2) = -2 by ring,kernelJet_left_zero]
  simp only [left,right,zero_smul,sub_self,sub_zero] at written
  simp only [driver,row,smul_neg,smul_sub,smul_comm (kernelWeight order observation 0 _) (sumRate nu _)]
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_sub q scaled,intervalIntegral.integral_smul,
    intervalIntegral.integral_neg]
  linear_combination written

end
end SaturationMonoid.NavierStokes.NativeWindowPairActionRows
