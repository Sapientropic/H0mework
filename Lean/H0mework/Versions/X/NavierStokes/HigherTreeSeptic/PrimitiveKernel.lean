import H0mework.Versions.X.NavierStokes.HigherTreeSeptic.SevenRows


set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedSepticPrimitiveKernel
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedSepticSevenRows
open NativeUnheatedStressPairEvolution NativeUnheatedTreeOutput
noncomputable section
variable {nu : Viscosity}

def rate (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6) (wave : IntegerWavevector)
    (i j outside l m p q r s u v : Coordinate) (index : Index) : ℝ :=
  NativeUnheatedTreeTime.sumRate nu (nodes slot leaf position newest wave i j outside l m p q r s u v index)

theorem rate_nonnegative (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j outside l m p q r s u v : Coordinate) (index : Index) :
    0 ≤ rate nu slot leaf position newest wave i j outside l m p q r s u v index :=
  NativeUnheatedTreeOutput.rate_nonnegative _

theorem rate_inverse_bound (nu : Viscosity) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j outside l m p q r s u v : Coordinate) (index : Index) :
    (rate nu slot leaf position newest wave i j outside l m p q r s u v index)⁻¹ ≤
      (scale nu 6)⁻¹*NativeCompleteStressCarrier.weight wave := by
  have paid := NativeUnheatedTreeOutput.inverse_bound (nu := nu)
    (nodes slot leaf position newest wave i j outside l m p q r s u v index)
  change (rate nu slot leaf position newest wave i j outside l m p q r s u v index)⁻¹ ≤
    (scale nu 6)⁻¹*NativeCompleteStressCarrier.weight
      (∑ number : Fin 7, (nodes slot leaf position newest wave i j outside l m p q r s u v index number).1) at paid
  rw [nodes_frequency] at paid
  exact paid

def primitiveTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.primitive seed (nodes slot leaf position newest wave i j outside l m p q r s u v index)
    (kernel nu slot leaf position newest wave i j response outside l m p q r s u v index) time

def octicTerm (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) : ℂ :=
  NativeUnheatedTreeNormalForm.nextForcing seed (nodes slot leaf position newest wave i j outside l m p q r s u v index)
    (kernel nu slot leaf position newest wave i j response outside l m p q r s u v index) time

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) :
    primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time =
      (rate nu slot leaf position newest wave i j outside l m p q r s u v index)⁻¹ •
        term seed slot leaf position newest wave i j response outside l m p q r s u v index time := by
  rw [term_product]
  exact NativeUnheatedTreeNormalForm.primitive_original seed _ _ time

theorem octic_original (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (time : ℝ) :
    octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time =
      ∑ derivativeLeaf : Fin 7, NativeUnheatedTreeInput.term seed
        (nodes slot leaf position newest wave i j outside l m p q r s u v index)
        (kernel nu slot leaf position newest wave i j response outside l m p q r s u v index) derivativeLeaf time :=
  NativeUnheatedTreeInput.next_original seed _ _ time

theorem primitive_ac (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index) start finish :=
  NativeUnheatedTreeNormalForm.primitive_ac seed _ _ start finish start0 finish0

theorem octic_integrable (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index) volume start finish :=
  NativeUnheatedTreeNormalForm.nextForcing_integrable seed _ _ start finish start0 finish0

theorem primitive_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index)
      (octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time -
        term seed slot leaf position newest wave i j response outside l m p q r s u v index time) time := by
  simp_rw [term_product]
  exact NativeUnheatedTreeNormalForm.primitive_hasDerivAt_ae seed _ _

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index finish -
      primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index start =
      ∫ time in start..finish, octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time -
        term seed slot leaf position newest wave i j response outside l m p q r s u v index time := by
  simp_rw [term_product]
  exact NativeUnheatedTreeNormalForm.row_write seed _ _ start finish start0 finish0

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index) (order : ℕ)
    (observation origin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, kernelWeight order observation origin time •
      term seed slot leaf position newest wave i j response outside l m p q r s u v index time) =
    (∫ time in start..finish, kernelWeight order observation origin time •
      octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time) -
    (∫ time in start..finish, kernelWeight (order+1) observation origin time •
      primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index time) -
    (kernelWeight order observation origin finish • primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index finish -
      kernelWeight order observation origin start • primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index start) := by
  simp_rw [term_product]
  exact NativeUnheatedTreeNormalForm.weighted_write seed _ _ order observation origin start finish start0 finish0

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitiveTerm seed slot leaf position newest wave i j response outside l m p q r s u v index (responseStep.2.clockAdvance+time) =
      primitiveTerm responseStep.1 slot leaf position newest wave i j response outside l m p q r s u v index time :=
  NativeUnheatedTreeNormalForm.primitive_next seed _ _ responseStep generated time nonnegative

theorem octic_next (seed : GeneratedWholeRestartCurrent nu) (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
    (wave : IntegerWavevector) (i j response outside l m p q r s u v : Coordinate) (index : Index)
    (responseStep : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some responseStep) (time : ℝ) (nonnegative : 0 ≤ time) :
    octicTerm seed slot leaf position newest wave i j response outside l m p q r s u v index (responseStep.2.clockAdvance+time) =
      octicTerm responseStep.1 slot leaf position newest wave i j response outside l m p q r s u v index time :=
  NativeUnheatedTreeNormalForm.nextForcing_next seed _ _ responseStep generated time nonnegative

end
end SaturationMonoid.NavierStokes.NativeUnheatedSepticPrimitiveKernel
