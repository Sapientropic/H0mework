import H0mework.Versions.X.NavierStokes.HigherTreeOctic.Generator
import H0mework.NavierStokes.Energy.StrongContinuationKineticDifferenceGronwall

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
noncomputable section

namespace NativeUnheatedOcticGramDual
variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

theorem vector_ac (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    AbsolutelyContinuousOnInterval
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
      first last := by
  classical
  have term (entry : Address) : AbsolutelyContinuousOnInterval
      (fun time => product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
        basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      first last := by
    have constantAC : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
        first last :=
      (contDiffOn_const : ContDiffOn ℝ 1
        (fun _ : ℝ => basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
        (uIcc first last)).absolutelyContinuousOnInterval
    convert (NativeUnheatedTreeTime.product_ac seed
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry)
      first last first0 last0).smul constantAC using 1
    funext time
    rfl
  have finite : ∀ observed : Finset Address, AbsolutelyContinuousOnInterval
      (fun time => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      first last := by
    intro observed
    induction observed using Finset.induction_on with
    | empty =>
        simpa using (contDiffOn_const : ContDiffOn ℝ 1
          (fun _ : ℝ => (0 : NativeUnheatedOcticGramDualPulse.Space)) (uIcc first last)).absolutelyContinuousOnInterval
    | @insert entry observed absent previous =>
        convert (term entry).add previous using 1
        funext time
        simp only [Finset.sum_insert absent, Pi.add_apply]
  have equal :
      vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed =
      (fun time => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry) := by
    funext time
    exact vector_source slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
  rw [equal]
  exact finite observed

theorem vector_hasDerivAt_ae (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) :
    ∀ᵐ time : ℝ, 0 < time →
      HasDerivAt
        (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
        (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
        time := by
  have each : ∀ᵐ time : ℝ, ∀ entry : Address, 0 < time →
      HasDerivAt
        (product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry))
        (productRate seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time)
        time :=
    ae_all_iff.mpr (fun entry => NativeUnheatedTreeTime.product_hasDerivAt_ae seed
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry))
  have split : ∀ᵐ time : ℝ, ∀ entry : Address, 0 ≤ time →
      productRate seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time =
        forcing seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time -
          sumRate nu (slots slot leaf position newest i j outside l m p q r s u v selected b entry) •
            product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time :=
    ae_all_iff.mpr (fun entry => NativeUnheatedTreeTime.productRate_split_ae seed
      (slots slot leaf position newest i j outside l m p q r s u v selected b entry))
  filter_upwards [each, split] with time actual rateEq positive
  have derived : HasDerivAt
      (fun actualTime => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) actualTime •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      (∑ entry ∈ observed,
        productRate seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry)
      time := by
    apply HasDerivAt.fun_sum
    intro entry _
    exact (actual entry positive).smul_const _
  have valueEq :
      (fun actualTime => ∑ entry ∈ observed,
        product seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) actualTime •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry) =
      vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed := by
    funext actualTime
    exact (vector_source slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed actualTime).symm
  have rateEq' :
      (∑ entry ∈ observed,
        productRate seed (slots slot leaf position newest i j outside l m p q r s u v selected b entry) time •
          basis (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test entry) =
      vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time := by
    unfold vectorRate
    apply Finset.sum_congr rfl
    intro entry _
    rw [rateEq entry positive.le]
  rw [valueEq, rateEq'] at derived
  exact derived

theorem vector_energy_write (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    (∫ time in first..last, 2 * inner ℝ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)) =
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last -
      work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first := by
  have derivative : ∀ᵐ time : ℝ, time ∈ uIcc first last →
      HasDerivAt
        (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed)
        (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
        time := by
    filter_upwards [vector_hasDerivAt_ae (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed,
      volume.ae_ne (0 : ℝ)] with time actual nonzero inside
    exact actual (lt_of_le_of_ne ((le_min first0 last0).trans inside.1) (Ne.symm nonzero))
  simpa only [work] using ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall.AbsolutelyContinuousOnInterval.norm_sq_energy_identity
    (vector_ac (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0)
    derivative

theorem signed_integrand (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (time : ℝ) :
    2 * inner ℝ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) +
      ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2 =
    2 * inner ℝ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) := by
  rw [vectorRate_split, inner_sub_right]
  have dissipated := vector_dissipation_real (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
  linarith

theorem work_signed_write (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    (∫ time in first..last,
      2 * inner ℝ
        (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
        (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) -
      ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2) =
    work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last -
      work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first := by
  calc
    _ = ∫ time in first..last, 2 * inner ℝ
      (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
      (vectorRate slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) := by
        apply intervalIntegral.integral_congr
        intro time _
        have paid := signed_integrand (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time
        linarith
    _ = _ := vector_energy_write slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0

theorem boundaryVector_next (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed (step.2.clockAdvance+time) =
      boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test step.1 observed time := by
  simp only [boundaryVector, NativeUnheatedTreeTime.product_next seed _ step generated time nonnegative]

theorem forcingVector_next (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed (step.2.clockAdvance+time) =
      forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test step.1 observed time := by
  simp only [forcingVector, NativeUnheatedTreeTime.forcing_next seed _ step generated time nonnegative]

theorem pairing_signed_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) :
    ‖original slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last -
      bare slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last‖^2 ≤
      NativeUnifiedCompleteSource.budget seed^2 *
        (work slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first +
          ∫ time in first..last,
            2 * inner ℝ
              (vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time)
              (forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time) -
            ‖boundaryVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖^2) := by
  rw [work_signed_write slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first last first0 last0]
  have paid := pairing_bound slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last
  convert paid using 1; ring

end NativeUnheatedOcticGramDual

end
end SaturationMonoid.NavierStokes
