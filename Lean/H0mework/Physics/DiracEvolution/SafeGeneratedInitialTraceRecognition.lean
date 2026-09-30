import H0mework.Physics.DiracEvolution.SafeWeightedPhysicalWeakEquation

/-!
# Fixed P506 generated initial-trace recognition

Full-history convergence of the action-owned initial mass reads fixes the
initial read of every generated common-subsequence occurrence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedInitialTraceRecognition

open Filter Set
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeightedPhysicalWeakEquation
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy

noncomputable section

set_option autoImplicit false

@[irreducible] def fixedP506L0CauchySafeMatterGalerkinInitialMassRead
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (test approximationIndex : ℕ) : ℝ :=
  galerkinWeakTestPairing
    (fixedP506L0CauchySafeMatterWeakMassForm
      (approximation approximationIndex).basis
      (fun mode ↦
        ((approximation approximationIndex).basisRegular mode).continuous)
      (approximation approximationIndex).basisCompact)
    (approximation approximationIndex).coefficient
    (testCoefficient approximationIndex test) timeStart

/-- Eventual exact source reads fix the limit of the full Galerkin history. -/
theorem fixedP506L0CauchySafeMatterGalerkinInitialMassRead_tendsto_of_eventually_exact
    {timeStart timeEnd energyCap : ℝ}
    {a b : DiracMatterSpatialCoordinates}
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (initialRead : ℕ → ℝ)
    (eventuallyExact : ∀ approximationIndex test,
      testEntry test ≤ approximationIndex →
        fixedP506L0CauchySafeMatterGalerkinInitialMassRead
          approximation testCoefficient test approximationIndex =
          initialRead test)
    (test : ℕ) :
    Tendsto (fixedP506L0CauchySafeMatterGalerkinInitialMassRead
      approximation testCoefficient test) atTop (nhds (initialRead test)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (testEntry test)]
    with approximationIndex entered
  exact (eventuallyExact approximationIndex test entered).symm

theorem fixedP506L0CauchySafeMatterPhysicalMassRead_initial_eq_of_history_tendsto
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (energyCap : ℝ)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount)
    (occurrence :
      FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient)
    (initialRead : ℕ → ℝ)
    (initialConvergence : ∀ test,
      Tendsto (fixedP506L0CauchySafeMatterGalerkinInitialMassRead
        approximation testCoefficient test)
        atTop (nhds (initialRead test)))
    (test : ℕ) :
    fixedP506L0CauchySafeMatterPhysicalMassRead occurrence test
        ⟨timeStart, left_mem_Icc.mpr timeOrder⟩ =
      initialRead test := by
  let initialTime : Icc timeStart timeEnd :=
    ⟨timeStart, left_mem_Icc.mpr timeOrder⟩
  have generatedConvergence :=
    (occurrence.generatedLimit.pairingConvergence test).tendsto_at initialTime
  have historyConvergence :=
    (initialConvergence test).comp
      occurrence.generatedLimit.subsequenceStrict.tendsto_atTop
  have historyConvergence' :
      Tendsto
        (fun sequenceIndex ↦
          galerkinWeakTestPairing
            (fixedP506L0CauchySafeMatterWeakMassForm
              (approximation
                (occurrence.generatedLimit.subsequence sequenceIndex)).basis
              (fun mode ↦
                ((approximation
                  (occurrence.generatedLimit.subsequence sequenceIndex)
                    ).basisRegular mode).continuous)
              (approximation
                (occurrence.generatedLimit.subsequence sequenceIndex)
                  ).basisCompact)
            (approximation
              (occurrence.generatedLimit.subsequence sequenceIndex)
                ).coefficient
            (testCoefficient
              (occurrence.generatedLimit.subsequence sequenceIndex) test)
            timeStart)
        atTop (nhds (initialRead test)) := by
    apply historyConvergence.congr'
    exact Filter.Eventually.of_forall fun sequenceIndex ↦ by
      unfold fixedP506L0CauchySafeMatterGalerkinInitialMassRead
      rfl
  have limitEq : occurrence.generatedLimit.commonLimit test initialTime =
      initialRead test :=
    tendsto_nhds_unique generatedConvergence historyConvergence'
  rw [fixedP506L0CauchySafeMatterPhysicalMassRead_eq_commonLimit]
  exact limitEq

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedInitialTraceRecognition
