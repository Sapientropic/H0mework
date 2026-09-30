import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Output
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.FiveRows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticPrimitiveKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressCarrier NativeUnheatedSourceGradient NativeWholeH1Mixed
open NativeUnheatedQuinticFiveRows NativeUnheatedQuinticOutput
noncomputable section
variable {nu : Viscosity}

def rate (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) : ℝ :=
  NativeUnheatedQuinticTime.sumRate nu (nodes slot leaf wave i j outside l m p q index 0)
    (nodes slot leaf wave i j outside l m p q index 1) (nodes slot leaf wave i j outside l m p q index 2)
    (nodes slot leaf wave i j outside l m p q index 3) (nodes slot leaf wave i j outside l m p q index 4)

theorem rate_nonnegative (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) : 0 ≤ rate nu slot leaf wave i j outside l m p q index :=
  NativeUnheatedQuinticNormalForm.rate_nonnegative _ _ _ _ _

theorem rate_inverse_bound (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j outside l m p q : Coordinate) (index : Index) :
    (rate nu slot leaf wave i j outside l m p q index)⁻¹ ≤ (scale nu)⁻¹*weight wave := by
  have original := frequency slot leaf wave i j outside l m p q index
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, ← add_assoc] at original
  change (nodes slot leaf wave i j outside l m p q index 0).1+(nodes slot leaf wave i j outside l m p q index 1).1+
    (nodes slot leaf wave i j outside l m p q index 2).1+(nodes slot leaf wave i j outside l m p q index 3).1+
    (nodes slot leaf wave i j outside l m p q index 4).1 = wave at original
  simpa only [rate, original] using inverse_bound (nu := nu) (nodes slot leaf wave i j outside l m p q index 0)
    (nodes slot leaf wave i j outside l m p q index 1) (nodes slot leaf wave i j outside l m p q index 2)
    (nodes slot leaf wave i j outside l m p q index 3) (nodes slot leaf wave i j outside l m p q index 4)

def primitiveTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedQuinticNormalForm.primitive seed (nodes slot leaf wave i j outside l m p q index 0)
    (nodes slot leaf wave i j outside l m p q index 1) (nodes slot leaf wave i j outside l m p q index 2)
    (nodes slot leaf wave i j outside l m p q index 3) (nodes slot leaf wave i j outside l m p q index 4)
    (kernel nu slot leaf wave i j response outside l m p q index) time

def sexticTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedQuinticNormalForm.sextic seed (nodes slot leaf wave i j outside l m p q index 0)
    (nodes slot leaf wave i j outside l m p q index 1) (nodes slot leaf wave i j outside l m p q index 2)
    (nodes slot leaf wave i j outside l m p q index 3) (nodes slot leaf wave i j outside l m p q index 4)
    (kernel nu slot leaf wave i j response outside l m p q index) time

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (time : ℝ) :
    primitiveTerm seed slot leaf wave i j response outside l m p q index time =
      (rate nu slot leaf wave i j outside l m p q index)⁻¹ • term seed slot leaf wave i j response outside l m p q index time := by
  rw [term_original]
  exact NativeUnheatedQuinticOutput.primitive_original seed _ _ _ _ _ _ time

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    Summable (fun index => ‖primitiveTerm seed slot leaf wave i j response outside l m p q index time‖) := by
  apply ((NativeUnheatedQuinticFiveRows.absolute_summable seed slot leaf wave i j response outside l m p q time nonnegative regular).mul_left
    ((scale nu)⁻¹*weight wave)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro index
  rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot leaf wave i j outside l m p q index))]
  exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot leaf wave i j outside l m p q index) (norm_nonneg _)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ := (scale nu)⁻¹*NativeUnheatedQuinticSource.bound seed

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed :=
  mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (NativeUnheatedQuinticSource.bound_nonnegative seed)

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' index, ‖primitiveTerm seed slot leaf wave i j response outside l m p q index time‖) ≤ bound seed*mass seed time*weight wave := by
  have compare := (absolute_summable seed slot leaf wave i j response outside l m p q time nonnegative regular).tsum_le_tsum
    (fun index => by
      rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot leaf wave i j outside l m p q index))]
      exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot leaf wave i j outside l m p q index) (norm_nonneg _))
    ((NativeUnheatedQuinticFiveRows.absolute_summable seed slot leaf wave i j response outside l m p q time nonnegative regular).mul_left ((scale nu)⁻¹*weight wave))
  rw [tsum_mul_left] at compare
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedQuinticFiveRows.absolute_bound seed slot leaf wave i j response outside l m p q time nonnegative regular)
    (mul_nonneg (inv_nonneg.mpr (scale_positive nu).le) (weight_pos wave).le)
  exact compare.trans (paid.trans_eq (by unfold bound; ring))

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index) (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitiveTerm seed slot leaf wave i j response outside l m p q index finish -
      primitiveTerm seed slot leaf wave i j response outside l m p q index start =
      ∫ time in start..finish, sexticTerm seed slot leaf wave i j response outside l m p q index time -
        term seed slot leaf wave i j response outside l m p q index time := by
  simp_rw [term_original]
  exact NativeUnheatedQuinticNormalForm.row_write seed _ _ _ _ _ _ start finish start0 finish0

theorem primitiveTerm_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (wave : IntegerWavevector)
    (i j response outside l m p q : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitiveTerm seed slot leaf wave i j response outside l m p q index (responseStep.2.clockAdvance+time) =
      primitiveTerm responseStep.1 slot leaf wave i j response outside l m p q index time :=
  NativeUnheatedQuinticNormalForm.primitive_next seed _ _ _ _ _ _ responseStep generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticPrimitiveKernel
