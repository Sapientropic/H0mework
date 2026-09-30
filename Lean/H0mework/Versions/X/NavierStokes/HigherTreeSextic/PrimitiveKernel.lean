import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.NormalForm
import H0mework.Versions.X.NavierStokes.HigherTreeSextic.SixRows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSexticPrimitiveKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeCompleteStressCarrier NativeUnheatedSourceGradient NativeWholeH1Mixed
open NativeUnheatedSexticSixRows NativeUnheatedTreeOutput
noncomputable section
variable {nu : Viscosity}

def rate (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j outside l m p q r s : Coordinate) (index : Index) : ℝ :=
  NativeUnheatedTreeTime.sumRate nu (nodes slot leaf position wave i j outside l m p q r s index)

theorem rate_nonnegative (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j outside l m p q r s : Coordinate) (index : Index) : 0 ≤ rate nu slot leaf position wave i j outside l m p q r s index :=
  NativeUnheatedTreeOutput.rate_nonnegative _

theorem rate_inverse_bound (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j outside l m p q r s : Coordinate) (index : Index) :
    (rate nu slot leaf position wave i j outside l m p q r s index)⁻¹ ≤ (scale nu 5)⁻¹*weight wave := by
  have paid := inverse_bound (nu := nu) (nodes slot leaf position wave i j outside l m p q r s index)
  change (rate nu slot leaf position wave i j outside l m p q r s index)⁻¹ ≤
    (scale nu 5)⁻¹*weight (∑ number : Fin 6, (nodes slot leaf position wave i j outside l m p q r s index number).1) at paid
  rw [NativeUnheatedSexticSixRows.frequency] at paid
  exact paid

def primitiveTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.primitive seed (nodes slot leaf position wave i j outside l m p q r s index)
    (kernel nu slot leaf position wave i j response outside l m p q r s index) time

def septicTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.nextForcing seed (nodes slot leaf position wave i j outside l m p q r s index)
    (kernel nu slot leaf position wave i j response outside l m p q r s index) time

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (time : ℝ) :
    primitiveTerm seed slot leaf position wave i j response outside l m p q r s index time =
      (rate nu slot leaf position wave i j outside l m p q r s index)⁻¹ • term seed slot leaf position wave i j response outside l m p q r s index time := by
  rw [term_product]
  exact NativeUnheatedTreeNormalForm.primitive_original seed _ _ time

theorem absolute_summable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    Summable (fun index => ‖primitiveTerm seed slot leaf position wave i j response outside l m p q r s index time‖) := by
  apply ((NativeUnheatedSexticSixRows.absolute_summable seed slot leaf position wave i j response outside l m p q r s time nonnegative regular).mul_left
    ((scale nu 5)⁻¹*weight wave)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro index
  rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot leaf position wave i j outside l m p q r s index))]
  exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot leaf position wave i j outside l m p q r s index) (norm_nonneg _)

def bound (seed : GeneratedWholeRestartCurrent nu) : ℝ := (scale nu 5)⁻¹*NativeUnheatedSexticUniformAllSlots.budget seed

theorem bound_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ bound seed :=
  mul_nonneg (inv_nonneg.mpr (scale_positive nu 5).le) (NativeUnheatedSexticUniformAllSlots.budget_nonnegative seed)

theorem absolute_bound (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (time : ℝ) (nonnegative : 0 ≤ time)
    (regular : H1 (physical seed time nonnegative)) :
    (∑' index, ‖primitiveTerm seed slot leaf position wave i j response outside l m p q r s index time‖) ≤ bound seed*mass seed time*weight wave := by
  have compare := (absolute_summable seed slot leaf position wave i j response outside l m p q r s time nonnegative regular).tsum_le_tsum
    (fun index => by
      rw [primitive_original, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (rate_nonnegative nu slot leaf position wave i j outside l m p q r s index))]
      exact mul_le_mul_of_nonneg_right (rate_inverse_bound nu slot leaf position wave i j outside l m p q r s index) (norm_nonneg _))
    ((NativeUnheatedSexticSixRows.absolute_summable seed slot leaf position wave i j response outside l m p q r s time nonnegative regular).mul_left ((scale nu 5)⁻¹*weight wave))
  rw [tsum_mul_left] at compare
  have paid := mul_le_mul_of_nonneg_left (NativeUnheatedSexticSixRows.absolute_bound seed slot leaf position wave i j response outside l m p q r s time nonnegative regular)
    (mul_nonneg (inv_nonneg.mpr (scale_positive nu 5).le) (weight_pos wave).le)
  exact compare.trans (paid.trans_eq (by unfold bound; ring))

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index) (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitiveTerm seed slot leaf position wave i j response outside l m p q r s index finish -
      primitiveTerm seed slot leaf position wave i j response outside l m p q r s index start =
      ∫ time in start..finish, septicTerm seed slot leaf position wave i j response outside l m p q r s index time -
        term seed slot leaf position wave i j response outside l m p q r s index time := by
  simp_rw [term_product]
  exact NativeUnheatedTreeNormalForm.row_write seed _ _ start finish start0 finish0

theorem primitiveTerm_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (wave : IntegerWavevector)
    (i j response outside l m p q r s : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitiveTerm seed slot leaf position wave i j response outside l m p q r s index (responseStep.2.clockAdvance+time) =
      primitiveTerm responseStep.1 slot leaf position wave i j response outside l m p q r s index time :=
  NativeUnheatedTreeNormalForm.primitive_next seed _ _ responseStep generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedSexticPrimitiveKernel
