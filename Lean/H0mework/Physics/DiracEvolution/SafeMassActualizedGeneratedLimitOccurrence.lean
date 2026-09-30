import H0mework.Physics.DiracEvolution.SafeGeneratedLimitOccurrence
import H0mework.Physics.DiracEvolution.SafeL2MassActualization
import H0mework.Physics.DiracEvolution.SafeCanonicalGalerkinBasis

/-!
# Fixed P506 mass-actualized generated matter limit

The exact common-subsequence occurrence is extended by its uniquely
mass-actualized physical spatial `L²` family. This is one dependent occurrence,
not a new evolution epoch: all approximation history and weighted action laws
remain in the lower generated-limit occurrence.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence

open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGeneratedLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakPairingCompactness
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- The exact generated-limit occurrence together with its uniquely
mass-actualized physical spatial field family. -/
structure FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (energyCap : ℝ)
    (timeOrder : timeStart ≤ timeEnd)
    (approximation : ℕ →
      FixedP506L0CauchySafeWeakGalerkinApproximation
        timeStart timeEnd a b energyCap)
    (testEntry : ℕ → ℕ)
    (testCoefficient : ∀ approximationIndex (_test : ℕ),
      DiracMatterGalerkinCoefficient
        (approximation approximationIndex).modeCount) where
  generatedLimit :
    FixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
      timeStart timeEnd a b energyCap timeOrder approximation testEntry
      testCoefficient
  physicalActualization :
    FixedP506L0CauchySafeMatterPhysicalL2Actualization
      timeStart timeEnd a b generatedLimit.representative

/-- The same-source Galerkin history and eventual dense-test representation
generate the complete mass-actualized lower occurrence. -/
theorem nonempty_fixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b)
    (energyCap : ℝ)
    (energyCapNonnegative : 0 ≤ energyCap)
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
            (testCoefficient approximationIndex test) point)) :
    Nonempty
      (FixedP506L0CauchySafeMassActualizedGeneratedLimitOccurrence
        timeStart timeEnd a b energyCap timeOrder approximation testEntry
        testCoefficient) := by
  obtain ⟨generatedLimit⟩ :=
    nonempty_fixedP506L0CauchySafeCountableDenseGeneratedLimitOccurrence
      timeStart timeEnd a b timeOrder boxOrder energyCap energyCapNonnegative
      approximation testEntry testCoefficient testRepresentation
  obtain ⟨physicalActualization⟩ :=
    nonempty_fixedP506L0CauchySafeMatterPhysicalL2Actualization
      timeStart timeEnd a b boxOrder generatedLimit.representative
  exact ⟨{
    generatedLimit := generatedLimit
    physicalActualization := physicalActualization }⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterMassActualizedGeneratedLimitOccurrence
