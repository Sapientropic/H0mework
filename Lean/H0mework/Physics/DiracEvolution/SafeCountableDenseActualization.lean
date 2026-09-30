import H0mework.Physics.DiracEvolution.SafeCountableDenseTestCarrier
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis
import H0mework.Physics.DiracEvolution.SafeFiniteL2MassRead
import H0mework.Physics.DiracEvolution.SafeWeakPairingCompactness
import H0mework.Physics.DiracEvolution.GeneratedWeakLimitActualization

/-!
# Fixed P506 countable-dense weak-limit actualization

Eventual exact Galerkin representation identifies every generated common
weak-pairing limit with the finite action-owned `L²` read.  Convergence then
extends across the dense algebraic test span and canonically produces its
unique Riesz representative at each canonical time.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCountableDenseActualization

open Filter MeasureTheory Set
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineGeneratedWeakLimitActualization
open StageNineHolonomicField
open scoped BoundedContinuousFunction Interval

noncomputable section

set_option autoImplicit false

variable {timeStart timeEnd energyCap : ℝ}
variable {a b : DiracMatterSpatialCoordinates}

/-- Eventual exact representation identifies the common Galerkin pairing
limit with the finite `L²` read on every generated test. -/
theorem fixedP506L0CauchySafeFiniteMassRead_generatorConvergence
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (limit : ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (subsequence : ℕ → ℕ)
    (subsequenceStrict : StrictMono subsequence)
    (pairingConvergence : ∀ test,
      TendstoUniformly
        (fun sequenceIndex (time : Icc timeStart timeEnd) ↦
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm
              (approximation (subsequence sequenceIndex)).basis
              (fun mode ↦
                ((approximation (subsequence sequenceIndex)).basisRegular mode
                  ).continuous)
              (approximation (subsequence sequenceIndex)).basisCompact)
            (approximation (subsequence sequenceIndex)).coefficient
            (testCoefficient (subsequence sequenceIndex) test) time.1)
          (limit test) atTop)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (test : ℕ) :
    Tendsto
      (fun sequenceIndex ↦
        fixedMatterFiniteMassRead C
          (approximation (subsequence sequenceIndex)).basis
          (fun mode ↦
            ((approximation (subsequence sequenceIndex)).basisRegular mode
              ).continuous)
          (approximation (subsequence sequenceIndex)).basisCompact
          ((approximation (subsequence sequenceIndex)).coefficient time)
          time a b (operatorBound time timeMem)
          (cauchySafeMatterCanonicalInteriorDenseTest a b test))
      atTop (nhds (limit test ⟨time, timeMem⟩)) := by
  have rawConvergence := (pairingConvergence test).tendsto_at
    ⟨time, timeMem⟩
  apply rawConvergence.congr'
  have eventuallyEntered : ∀ᶠ sequenceIndex : ℕ in atTop,
      testEntry test ≤ subsequence sequenceIndex :=
    subsequenceStrict.tendsto_atTop (eventually_ge_atTop (testEntry test))
  filter_upwards [eventuallyEntered] with sequenceIndex entered
  symm
  apply fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing
    C (approximation (subsequence sequenceIndex)).basis
    (fun mode ↦
      ((approximation (subsequence sequenceIndex)).basisRegular mode
        ).continuous)
    (approximation (subsequence sequenceIndex)).basisCompact a b
    (approximation (subsequence sequenceIndex)).basisZeroOutside
    (approximation (subsequence sequenceIndex)).coefficient
    (testCoefficient (subsequence sequenceIndex) test) time
    (operatorBound time timeMem)
  intro space
  have represented := congrFun
    (testRepresentation (subsequence sequenceIndex) test entered)
    (diracMatterSpacetimeCoordinatePoint time space)
  rw [fixedP506L0CauchySafeMatterWeakSpatialCandidate_slice] at represented
  simpa [fixedMatterTrialCoordinates] using represented.symm

/-- The finite action-owned mass read family at one canonical time. -/
def fixedP506L0CauchySafeCountableDenseFiniteMassRead
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd) :
    ℕ → CauchySafeMatterSmoothCompactTest →ₗ[ℝ] ℝ :=
  fun approximationIndex ↦
    fixedMatterFiniteMassRead C
      (approximation approximationIndex).basis
      (fun mode ↦
        ((approximation approximationIndex).basisRegular mode).continuous)
      (approximation approximationIndex).basisCompact
      ((approximation approximationIndex).coefficient time)
      time a b (operatorBound time timeMem)

/-- The generated common weak limit at one canonical time actualizes to the
unique physical `L²` representative, with exact recognition on every
countable generator. -/
theorem exists_fixedP506L0CauchySafeCountableDenseRieszActualizationAt
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (testRepresentation : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
      cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test = fun point ↦
        matterCoordinateEquiv
          (fixedP506L0CauchySafeMatterWeakSpatialCandidate
            (approximation approximationIndex).basis
            (testCoefficient approximationIndex test) point))
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc timeStart timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (time : ℝ)
    (timeMem : time ∈ Icc timeStart timeEnd)
    (B : ℝ)
    (finiteReadBound : ∀ approximationIndex test,
      ‖fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
          approximation time timeMem approximationIndex test‖ ≤
        B * ‖cauchySafeMatterSmoothCompactTestToL2 a b test‖)
    (commonLimit : ℕ → (Icc timeStart timeEnd : Set ℝ) →ᵇ ℝ)
    (subsequence : ℕ → ℕ)
    (subsequenceStrict : StrictMono subsequence)
    (pairingConvergence : ∀ test,
      TendstoUniformly
        (fun sequenceIndex (candidateTime : Icc timeStart timeEnd) ↦
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm
              (approximation (subsequence sequenceIndex)).basis
              (fun mode ↦
                ((approximation (subsequence sequenceIndex)).basisRegular mode
                  ).continuous)
              (approximation (subsequence sequenceIndex)).basisCompact)
            (approximation (subsequence sequenceIndex)).coefficient
            (testCoefficient (subsequence sequenceIndex) test)
            candidateTime.1)
          (commonLimit test) atTop) :
    ∃ limit : CauchySafeMatterCanonicalInteriorTestSpan a b → ℝ,
      ∃ convergence : ∀ test,
        Tendsto
          (fun sequenceIndex ↦
            fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
              approximation time timeMem (subsequence sequenceIndex) test.1)
          atTop (nhds (limit test)),
        let spanFunctional : ℕ →
            CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ] ℝ :=
          fun approximationIndex ↦
            (fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
              approximation time timeMem approximationIndex).comp
              (Submodule.subtype (CauchySafeMatterCanonicalInteriorTestSpan a b))
        let representative := pointwiseLimitRieszActualization
          (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) spanFunctional
          subsequence limit convergence
        (∀ test,
          inner ℝ representative
              (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
            limit test) ∧
          (∀ candidate : CauchySafeMatterSpatialL2 a b,
            (∀ test,
              inner ℝ candidate
                  (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b test) =
                limit test) →
              candidate = representative) ∧
          ∀ index,
            limit ⟨cauchySafeMatterCanonicalInteriorDenseTest a b index,
              Submodule.subset_span (Set.mem_range_self index)⟩ =
                commonLimit index ⟨time, timeMem⟩ := by
  refine exists_pointwiseLimitRieszActualization_of_generatorConvergence
    (cauchySafeMatterCanonicalInteriorDenseTest a b)
    (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b)
    (fixedP506L0CauchySafeCountableDenseFiniteMassRead C operatorBound
      approximation time timeMem)
    subsequence (fun test ↦ commonLimit test ⟨time, timeMem⟩) ?_
    (cauchySafeMatterCanonicalInteriorTestSpanToL2_denseRange a b) B ?_
  · exact fixedP506L0CauchySafeFiniteMassRead_generatorConvergence
      approximation testEntry testCoefficient testRepresentation C
      operatorBound commonLimit subsequence subsequenceStrict
      pairingConvergence time timeMem
  · intro approximationIndex test
    exact finiteReadBound approximationIndex test.1

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCountableDenseActualization
