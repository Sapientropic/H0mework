import H0mework.Versions.R2.Arithmetic.GoldbachResidual.MinimalSCC

/-!
# Prime-complement factor trace inside the dark SCC

The minimum closed decay sector is compressed to its two prime-boundary
carriers.  Every actual prime factor of the composite complement produces,
from the same source state, both the repair landing and the opposite-side
prime emission landing inside the same SCC.

No factor, landing, target equality or complement relation is supplied by a
caller.  They are read from the exact factorization channel inventory.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFirstResidualFullFactorDecayPrimeTraceProducer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFirstResidualFullFactorDecaySCCProducer
open CanonicalUnitArithmeticFullFactorDecayReachabilityProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
open CanonicalUnitArithmeticGlobalGoldbachDisposition

noncomputable section

def leftPrimeBoundaryStates
    {failure : FirstResidualOccurrence}
    (scc : RootGeneratedFirstResidualFullFactorDecaySCCAt failure) :
    Finset (EffectiveSplitAt failure.index) :=
  scc.scc.sector.states.filter fun state => Nat.Prime (splitLeft state)

def rightPrimeBoundaryStates
    {failure : FirstResidualOccurrence}
    (scc : RootGeneratedFirstResidualFullFactorDecaySCCAt failure) :
    Finset (EffectiveSplitAt failure.index) :=
  scc.scc.sector.states.filter fun state => Nat.Prime (splitRight state)

structure LeftPrimeComplementFactorTransitionAt
    {failure : FirstResidualOccurrence}
    (scc : RootGeneratedFirstResidualFullFactorDecaySCCAt failure)
    (source : EffectiveSplitAt failure.index)
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) : Type where
  private mk ::
  sourceMem : source ∈ leftPrimeBoundaryStates scc
  sourceLeftPrime : Nat.Prime (splitLeft source)
  sourceRightNotPrime : ¬ Nat.Prime (splitRight source)
  selectedPrime : Nat.Prime selected.1
  selectedDvdComplement : selected.1 ∣ splitRight source
  selectedDvdTargetSubLeftPrime :
    selected.1 ∣ repairTargetValue failure.index - splitLeft source
  repairMem :
    (FactorRepairAlternativeAt.right sourceRightNotPrime selected).target ∈
      scc.scc.sector.states
  emissionMem :
    factorEmissionTarget
        (FactorRepairAlternativeAt.right sourceRightNotPrime selected) ∈
      rightPrimeBoundaryStates scc
  repairLanding :
    splitLeft
          (FactorRepairAlternativeAt.right sourceRightNotPrime selected).target +
        splitRight
          (FactorRepairAlternativeAt.right sourceRightNotPrime selected).target =
      repairTargetValue failure.index
  emissionLanding :
    splitLeft (factorEmissionTarget
          (FactorRepairAlternativeAt.right sourceRightNotPrime selected)) +
        splitRight (factorEmissionTarget
          (FactorRepairAlternativeAt.right sourceRightNotPrime selected)) =
      repairTargetValue failure.index
  emittedRight_eq_factor :
    splitRight (factorEmissionTarget
      (FactorRepairAlternativeAt.right sourceRightNotPrime selected)) =
        selected.1
  emittedLeftNotPrime :
    ¬ Nat.Prime (splitLeft (factorEmissionTarget
      (FactorRepairAlternativeAt.right sourceRightNotPrime selected)))

structure RightPrimeComplementFactorTransitionAt
    {failure : FirstResidualOccurrence}
    (scc : RootGeneratedFirstResidualFullFactorDecaySCCAt failure)
    (source : EffectiveSplitAt failure.index)
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) : Type where
  private mk ::
  sourceMem : source ∈ rightPrimeBoundaryStates scc
  sourceLeftNotPrime : ¬ Nat.Prime (splitLeft source)
  sourceRightPrime : Nat.Prime (splitRight source)
  selectedPrime : Nat.Prime selected.1
  selectedDvdComplement : selected.1 ∣ splitLeft source
  selectedDvdTargetSubRightPrime :
    selected.1 ∣ repairTargetValue failure.index - splitRight source
  repairMem :
    (FactorRepairAlternativeAt.left sourceLeftNotPrime selected).target ∈
      scc.scc.sector.states
  emissionMem :
    factorEmissionTarget
        (FactorRepairAlternativeAt.left sourceLeftNotPrime selected) ∈
      leftPrimeBoundaryStates scc
  repairLanding :
    splitLeft
          (FactorRepairAlternativeAt.left sourceLeftNotPrime selected).target +
        splitRight
          (FactorRepairAlternativeAt.left sourceLeftNotPrime selected).target =
      repairTargetValue failure.index
  emissionLanding :
    splitLeft (factorEmissionTarget
          (FactorRepairAlternativeAt.left sourceLeftNotPrime selected)) +
        splitRight (factorEmissionTarget
          (FactorRepairAlternativeAt.left sourceLeftNotPrime selected)) =
      repairTargetValue failure.index
  emittedLeft_eq_factor :
    splitLeft (factorEmissionTarget
      (FactorRepairAlternativeAt.left sourceLeftNotPrime selected)) =
        selected.1
  emittedRightNotPrime :
    ¬ Nat.Prime (splitRight (factorEmissionTarget
      (FactorRepairAlternativeAt.left sourceLeftNotPrime selected)))

structure RootGeneratedFirstResidualFullFactorDecayPrimeTraceAt
    (failure : FirstResidualOccurrence) : Type 7 where
  private mk ::
  scc : RootGeneratedFirstResidualFullFactorDecaySCCAt failure
  scc_eq : scc = generateFirstResidualFullFactorDecaySCC failure
  leftCarrier : Finset (EffectiveSplitAt failure.index)
  leftCarrier_eq : leftCarrier = leftPrimeBoundaryStates scc
  rightCarrier : Finset (EffectiveSplitAt failure.index)
  rightCarrier_eq : rightCarrier = rightPrimeBoundaryStates scc
  leftCarrierNonempty : leftCarrier.Nonempty
  rightCarrierNonempty : rightCarrier.Nonempty
  leftToRight : ∀ source, source ∈ leftCarrier →
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) →
      LeftPrimeComplementFactorTransitionAt scc source selected
  rightToLeft : ∀ source, source ∈ rightCarrier →
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) →
      RightPrimeComplementFactorTransitionAt scc source selected
  pathBetweenCarriers : ∀ left, left ∈ leftCarrier →
    ∀ right, right ∈ rightCarrier →
      SourceGeneratedFiniteEffectiveBranchingReachability.GeneratedPathAt
        (fullFactorDecayLaw failure.index) left right
  occurrenceRoot :
    scc.decay.decay.occurrence.root.rootOccurrence =
      CanonicalUnitArithmeticRoot.initialStep.generated.occurrence

noncomputable def generateFirstResidualFullFactorDecayPrimeTrace
    (failure : FirstResidualOccurrence) :
    RootGeneratedFirstResidualFullFactorDecayPrimeTraceAt failure := by
  let scc := generateFirstResidualFullFactorDecaySCC failure
  let leftCarrier := leftPrimeBoundaryStates scc
  let rightCarrier := rightPrimeBoundaryStates scc
  let seed := Classical.choose scc.sectorNonempty
  have seedMem : seed ∈ scc.scc.sector.states :=
    Classical.choose_spec scc.sectorNonempty
  have leftCarrierNonempty : leftCarrier.Nonempty := by
    by_cases leftPrime : Nat.Prime (splitLeft seed)
    · exact ⟨seed, Finset.mem_filter.mpr ⟨seedMem, leftPrime⟩⟩
    · let alternative := generatedLeftFactorAlternative seed leftPrime
      let emitted := factorEmissionTarget alternative
      have emittedMem : emitted ∈ scc.scc.sector.states :=
        scc.everyDecayChannelClosed seed seedMem (.emission alternative)
      have emittedPrime : Nat.Prime (splitLeft emitted) := by
        unfold emitted alternative generatedLeftFactorAlternative
        exact left_factorEmission_emittedPrime leftPrime _
      exact ⟨emitted, Finset.mem_filter.mpr ⟨emittedMem, emittedPrime⟩⟩
  have rightCarrierNonempty : rightCarrier.Nonempty := by
    by_cases rightPrime : Nat.Prime (splitRight seed)
    · exact ⟨seed, Finset.mem_filter.mpr ⟨seedMem, rightPrime⟩⟩
    · let alternative := generatedRightFactorAlternative seed rightPrime
      let emitted := factorEmissionTarget alternative
      have emittedMem : emitted ∈ scc.scc.sector.states :=
        scc.everyDecayChannelClosed seed seedMem (.emission alternative)
      have emittedPrime : Nat.Prime (splitRight emitted) := by
        unfold emitted alternative generatedRightFactorAlternative
        exact right_factorEmission_emittedPrime rightPrime _
      exact ⟨emitted, Finset.mem_filter.mpr ⟨emittedMem, emittedPrime⟩⟩
  have leftToRight : ∀ source, source ∈ leftCarrier →
      (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) →
        LeftPrimeComplementFactorTransitionAt scc source selected := by
    intro source sourceMem selected
    have sourceParts := Finset.mem_filter.mp sourceMem
    have rightNotPrime : ¬ Nat.Prime (splitRight source) := by
      intro rightPrime
      exact scc.everyStateNonterminal source sourceParts.1
        ⟨⟨sourceParts.2, rightPrime⟩⟩
    let alternative : FactorRepairAlternativeAt source :=
      .right rightNotPrime selected
    have repairMem : alternative.target ∈ scc.scc.sector.states :=
      scc.everyDecayChannelClosed source sourceParts.1 (.repair alternative)
    have emissionSectorMem : factorEmissionTarget alternative ∈
        scc.scc.sector.states :=
      scc.everyDecayChannelClosed source sourceParts.1 (.emission alternative)
    have emittedRightPrime : Nat.Prime
        (splitRight (factorEmissionTarget alternative)) := by
      unfold alternative
      exact right_factorEmission_emittedPrime rightNotPrime selected
    have emittedLeftNotPrime : ¬ Nat.Prime
        (splitLeft (factorEmissionTarget alternative)) := by
      intro emittedLeftPrime
      exact scc.everyStateNonterminal (factorEmissionTarget alternative)
        emissionSectorMem ⟨⟨emittedLeftPrime, emittedRightPrime⟩⟩
    exact
      { sourceMem := sourceMem
        sourceLeftPrime := sourceParts.2
        sourceRightNotPrime := rightNotPrime
        selectedPrime := Nat.prime_of_mem_primeFactors selected.2
        selectedDvdComplement := Nat.dvd_of_mem_primeFactors selected.2
        selectedDvdTargetSubLeftPrime := by
          have sourceLanding := split_landing source
          have complementEq :
              splitRight source =
                repairTargetValue failure.index - splitLeft source := by
            omega
          rw [← complementEq]
          exact Nat.dvd_of_mem_primeFactors selected.2
        repairMem := repairMem
        emissionMem := Finset.mem_filter.mpr
          ⟨emissionSectorMem, emittedRightPrime⟩
        repairLanding := alternative.target_lands
        emissionLanding := factorEmissionTarget_lands alternative
        emittedRight_eq_factor := by
          exact right_factorEmissionTarget_right rightNotPrime selected
        emittedLeftNotPrime := emittedLeftNotPrime }
  have rightToLeft : ∀ source, source ∈ rightCarrier →
      (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) →
        RightPrimeComplementFactorTransitionAt scc source selected := by
    intro source sourceMem selected
    have sourceParts := Finset.mem_filter.mp sourceMem
    have leftNotPrime : ¬ Nat.Prime (splitLeft source) := by
      intro leftPrime
      exact scc.everyStateNonterminal source sourceParts.1
        ⟨⟨leftPrime, sourceParts.2⟩⟩
    let alternative : FactorRepairAlternativeAt source :=
      .left leftNotPrime selected
    have repairMem : alternative.target ∈ scc.scc.sector.states :=
      scc.everyDecayChannelClosed source sourceParts.1 (.repair alternative)
    have emissionSectorMem : factorEmissionTarget alternative ∈
        scc.scc.sector.states :=
      scc.everyDecayChannelClosed source sourceParts.1 (.emission alternative)
    have emittedLeftPrime : Nat.Prime
        (splitLeft (factorEmissionTarget alternative)) := by
      unfold alternative
      exact left_factorEmission_emittedPrime leftNotPrime selected
    have emittedRightNotPrime : ¬ Nat.Prime
        (splitRight (factorEmissionTarget alternative)) := by
      intro emittedRightPrime
      exact scc.everyStateNonterminal (factorEmissionTarget alternative)
        emissionSectorMem ⟨⟨emittedLeftPrime, emittedRightPrime⟩⟩
    exact
      { sourceMem := sourceMem
        sourceLeftNotPrime := leftNotPrime
        sourceRightPrime := sourceParts.2
        selectedPrime := Nat.prime_of_mem_primeFactors selected.2
        selectedDvdComplement := Nat.dvd_of_mem_primeFactors selected.2
        selectedDvdTargetSubRightPrime := by
          have sourceLanding := split_landing source
          have complementEq :
              splitLeft source =
                repairTargetValue failure.index - splitRight source := by
            omega
          rw [← complementEq]
          exact Nat.dvd_of_mem_primeFactors selected.2
        repairMem := repairMem
        emissionMem := Finset.mem_filter.mpr
          ⟨emissionSectorMem, emittedLeftPrime⟩
        repairLanding := alternative.target_lands
        emissionLanding := factorEmissionTarget_lands alternative
        emittedLeft_eq_factor := by
          exact left_factorEmissionTarget_left leftNotPrime selected
        emittedRightNotPrime := emittedRightNotPrime }
  exact
    { scc := scc
      scc_eq := rfl
      leftCarrier := leftCarrier
      leftCarrier_eq := rfl
      rightCarrier := rightCarrier
      rightCarrier_eq := rfl
      leftCarrierNonempty := leftCarrierNonempty
      rightCarrierNonempty := rightCarrierNonempty
      leftToRight := leftToRight
      rightToLeft := rightToLeft
      pathBetweenCarriers := by
        intro left leftMem right rightMem
        exact scc.pathBetween left (Finset.mem_filter.mp leftMem).1
          right (Finset.mem_filter.mp rightMem).1
      occurrenceRoot := scc.occurrenceRoot }

end
end CanonicalUnitArithmeticFirstResidualFullFactorDecayPrimeTraceProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
