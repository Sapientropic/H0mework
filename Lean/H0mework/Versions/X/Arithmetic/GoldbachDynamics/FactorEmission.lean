import H0mework.Versions.X.Arithmetic.GoldbachDynamics.RepairReachability
import H0mework.Foundation.Finite.BranchingReachability
import Mathlib.Data.Sym.Sym2

/-!
# Source-generated prime-factor emission channels

Factor repair consumes only the shift `p - 1`.  A composite endpoint also
has a second lawful decay channel: emit its actual prime factor `p` as one
stable endpoint and transfer the remaining composite charge to the sibling.

```text
(x = p*c, y) -> (p, N-p)
(x, y = p*c) -> (N-p, p)
```

The total is preserved, the emitted endpoint is prime, and the selected
composite endpoint strictly decays to its proper factor.  The combined law
inventories both repair and emission channels.  Its `classify` field retains
the existing left-first repair only as the generic law's required productivity
witness; complete reachability quantifies over every value of `StepAt` and is
therefore not restricted to that deterministic spine.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFullFactorEmissionProducer

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open CanonicalUnitArithmeticFullFactorRepairReachabilityProducer
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

def factorEmissionTarget {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    EffectiveSplitAt index := by
  cases alternative with
  | left leftNotPrime selected =>
      have factorPrime := Nat.prime_of_mem_primeFactors selected.2
      have factorProper :=
        FactorRepairAlternativeAt.left_selectedFactorProper
          leftNotPrime selected
      have sourceLanding := split_landing source
      have leftFloor := splitLeft_atLeastTwo source
      have rightFloor := splitRight_atLeastTwo source
      have leftLeTarget := splitLeft_le_target source
      refine ⟨⟨selected.1, by omega⟩, factorPrime.two_le, ?_⟩
      change 2 ≤ repairTargetValue index - selected.1
      omega
  | right rightNotPrime selected =>
      have factorPrime := Nat.prime_of_mem_primeFactors selected.2
      have factorProper :=
        FactorRepairAlternativeAt.right_selectedFactorProper
          rightNotPrime selected
      have sourceLanding := split_landing source
      have leftFloor := splitLeft_atLeastTwo source
      have rightFloor := splitRight_atLeastTwo source
      have factorLeTarget : selected.1 ≤ repairTargetValue index := by
        omega
      have targetLeftFloor :
          2 ≤ repairTargetValue index - selected.1 := by
        calc
          2 ≤ splitLeft source := leftFloor
          _ ≤ splitLeft source + (splitRight source - selected.1) :=
            Nat.le_add_right _ _
          _ = repairTargetValue index - selected.1 := by omega
      refine
        ⟨⟨repairTargetValue index - selected.1,
            Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
          targetLeftFloor, ?_⟩
      · change 2 ≤ repairTargetValue index -
          (repairTargetValue index - selected.1)
        rw [Nat.sub_sub_self factorLeTarget]
        exact factorPrime.two_le

theorem factorEmissionTarget_lands {index : Nat}
    {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    splitLeft (factorEmissionTarget alternative) +
        splitRight (factorEmissionTarget alternative) =
      repairTargetValue index :=
  split_landing (factorEmissionTarget alternative)

@[simp] theorem left_factorEmissionTarget_left {index : Nat}
    {source : EffectiveSplitAt index}
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    splitLeft (factorEmissionTarget
      (FactorRepairAlternativeAt.left leftNotPrime selected)) = selected.1 := by
  rfl

theorem left_factorEmission_emittedPrime {index : Nat}
    {source : EffectiveSplitAt index}
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    Nat.Prime (splitLeft (factorEmissionTarget
      (FactorRepairAlternativeAt.left leftNotPrime selected))) := by
  rw [left_factorEmissionTarget_left]
  exact Nat.prime_of_mem_primeFactors selected.2

theorem left_factorEmission_strict {index : Nat}
    {source : EffectiveSplitAt index}
    (leftNotPrime : ¬ Nat.Prime (splitLeft source))
    (selected : {p : Nat // p ∈ (splitLeft source).primeFactors}) :
    splitLeft (factorEmissionTarget
        (FactorRepairAlternativeAt.left leftNotPrime selected)) <
      splitLeft source := by
  rw [left_factorEmissionTarget_left]
  exact FactorRepairAlternativeAt.left_selectedFactorProper
    leftNotPrime selected

@[simp] theorem right_factorEmissionTarget_right {index : Nat}
    {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    splitRight (factorEmissionTarget
      (FactorRepairAlternativeAt.right rightNotPrime selected)) = selected.1 := by
  change repairTargetValue index -
      (repairTargetValue index - selected.1) = selected.1
  have factorProper :=
    FactorRepairAlternativeAt.right_selectedFactorProper
      rightNotPrime selected
  have sourceLanding := split_landing source
  omega

@[simp] theorem right_factorEmissionTarget_left {index : Nat}
    {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    splitLeft (factorEmissionTarget
      (FactorRepairAlternativeAt.right rightNotPrime selected)) =
        repairTargetValue index - selected.1 := by
  rfl

theorem right_factorEmission_emittedPrime {index : Nat}
    {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    Nat.Prime (splitRight (factorEmissionTarget
      (FactorRepairAlternativeAt.right rightNotPrime selected))) := by
  rw [right_factorEmissionTarget_right]
  exact Nat.prime_of_mem_primeFactors selected.2

theorem right_factorEmission_strict {index : Nat}
    {source : EffectiveSplitAt index}
    (rightNotPrime : ¬ Nat.Prime (splitRight source))
    (selected : {p : Nat // p ∈ (splitRight source).primeFactors}) :
    splitRight (factorEmissionTarget
        (FactorRepairAlternativeAt.right rightNotPrime selected)) <
      splitRight source := by
  rw [right_factorEmissionTarget_right]
  exact FactorRepairAlternativeAt.right_selectedFactorProper
    rightNotPrime selected

inductive FactorDecayChannelAt {index : Nat}
    (source : EffectiveSplitAt index) : Type
  | repair (alternative : FactorRepairAlternativeAt source)
  | emission (alternative : FactorRepairAlternativeAt source)

def FactorDecayChannelAt.target {index : Nat}
    {source : EffectiveSplitAt index} :
    FactorDecayChannelAt source → EffectiveSplitAt index
  | .repair alternative => alternative.target
  | .emission alternative => factorEmissionTarget alternative

/-- Arithmetic presentation of the indistinguishable two-particle state. -/
def unorderedSplitKey {index : Nat} (state : EffectiveSplitAt index) :
    Sym2 Nat :=
  s(splitLeft state, splitRight state)

abbrev FactorDecayChannelAt.IsPhysicalProgress {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) : Prop :=
  unorderedSplitKey channel.target ≠ unorderedSplitKey source

/-- For the classifier's chosen factor, repair and paired emission cannot
both be mere swaps.  Hence every nonterminal classified row exposes at least
one physical action without accepting a target from the caller. -/
theorem repair_or_emission_isPhysicalProgress {index : Nat}
    {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    FactorDecayChannelAt.IsPhysicalProgress (.repair alternative) ∨
      FactorDecayChannelAt.IsPhysicalProgress (.emission alternative) := by
  by_cases repairProgress :
      FactorDecayChannelAt.IsPhysicalProgress (.repair alternative)
  · exact .inl repairProgress
  · right
    intro emissionIdentity
    have repairIdentity :
        unorderedSplitKey alternative.target = unorderedSplitKey source :=
      not_ne_iff.mp repairProgress
    cases alternative with
    | left leftNotPrime selected =>
        change
          s(splitLeft
              ((FactorRepairAlternativeAt.left leftNotPrime selected).target),
              splitRight
              ((FactorRepairAlternativeAt.left leftNotPrime selected).target)) =
            s(splitLeft source, splitRight source) at repairIdentity
        change
          s(splitLeft (factorEmissionTarget
              (FactorRepairAlternativeAt.left leftNotPrime selected)),
              splitRight (factorEmissionTarget
              (FactorRepairAlternativeAt.left leftNotPrime selected))) =
            s(splitLeft source, splitRight source) at emissionIdentity
        rw [Sym2.eq_iff] at repairIdentity emissionIdentity
        rcases repairIdentity with repairDirect | repairSwap
        · exact (Nat.ne_of_lt
            (FactorRepairAlternativeAt.left_target_strict
              leftNotPrime selected)) repairDirect.1
        · rcases emissionIdentity with emissionDirect | emissionSwap
          · have factorEq : selected.1 = splitLeft source := by
              simpa only [left_factorEmissionTarget_left] using emissionDirect.1
            exact (Nat.ne_of_lt
              (FactorRepairAlternativeAt.left_selectedFactorProper
                leftNotPrime selected)) factorEq
          · have factorEq : selected.1 = splitRight source := by
              simpa only [left_factorEmissionTarget_left] using emissionSwap.1
            have repairLeft := repairSwap.1
            rw [FactorRepairAlternativeAt.left_target_left, factorEq] at repairLeft
            have factorDvd : selected.1 ∣ splitLeft source :=
              Nat.dvd_of_mem_primeFactors selected.2
            have factorProper :=
              FactorRepairAlternativeAt.left_selectedFactorProper
                leftNotPrime selected
            have factorFloor :=
              (Nat.prime_of_mem_primeFactors selected.2).two_le
            have dvdTwoFactor : selected.1 ∣ 2 * selected.1 :=
              ⟨2, by omega⟩
            have dvdOne : selected.1 ∣ 1 := by
              have difference := Nat.dvd_sub dvdTwoFactor factorDvd
              have differenceEq :
                  2 * selected.1 - splitLeft source = 1 := by omega
              rwa [differenceEq] at difference
            have factorOne := Nat.eq_one_of_dvd_one dvdOne
            exact (Nat.prime_of_mem_primeFactors selected.2).ne_one factorOne
    | right rightNotPrime selected =>
        change
          s(splitLeft
              ((FactorRepairAlternativeAt.right rightNotPrime selected).target),
              splitRight
              ((FactorRepairAlternativeAt.right rightNotPrime selected).target)) =
            s(splitLeft source, splitRight source) at repairIdentity
        change
          s(splitLeft (factorEmissionTarget
              (FactorRepairAlternativeAt.right rightNotPrime selected)),
              splitRight (factorEmissionTarget
              (FactorRepairAlternativeAt.right rightNotPrime selected))) =
            s(splitLeft source, splitRight source) at emissionIdentity
        rw [Sym2.eq_iff] at repairIdentity emissionIdentity
        rcases repairIdentity with repairDirect | repairSwap
        · exact (Nat.ne_of_lt
            (FactorRepairAlternativeAt.right_target_strict
              rightNotPrime selected)) repairDirect.1.symm
        · rcases emissionIdentity with emissionDirect | emissionSwap
          · have factorEq : selected.1 = splitRight source := by
              simpa only [right_factorEmissionTarget_right] using emissionDirect.2
            exact (Nat.ne_of_lt
              (FactorRepairAlternativeAt.right_selectedFactorProper
                rightNotPrime selected)) factorEq
          · have factorEq : selected.1 = splitLeft source := by
              simpa only [right_factorEmissionTarget_right] using emissionSwap.2
            have repairLeft := repairSwap.1
            rw [FactorRepairAlternativeAt.right_target_left, factorEq] at repairLeft
            have factorDvd : selected.1 ∣ splitRight source :=
              Nat.dvd_of_mem_primeFactors selected.2
            have factorProper :=
              FactorRepairAlternativeAt.right_selectedFactorProper
                rightNotPrime selected
            have factorFloor :=
              (Nat.prime_of_mem_primeFactors selected.2).two_le
            have dvdTwoFactor : selected.1 ∣ 2 * selected.1 :=
              ⟨2, by omega⟩
            have dvdOne : selected.1 ∣ 1 := by
              have difference := Nat.dvd_sub dvdTwoFactor factorDvd
              have differenceEq :
                  2 * selected.1 - splitRight source = 1 := by omega
              rwa [differenceEq] at difference
            have factorOne := Nat.eq_one_of_dvd_one dvdOne
            exact (Nat.prime_of_mem_primeFactors selected.2).ne_one factorOne

theorem FactorDecayChannelAt.target_lands {index : Nat}
    {source : EffectiveSplitAt index}
    (channel : FactorDecayChannelAt source) :
    splitLeft channel.target + splitRight channel.target =
      repairTargetValue index := by
  cases channel with
  | repair alternative => exact alternative.target_lands
  | emission alternative => exact factorEmissionTarget_lands alternative

noncomputable def fullFactorDecayClassify {index : Nat}
    (state : EffectiveSplitAt index) :
    PrimePairTerminalAt state ⊕ FactorDecayChannelAt state :=
  match (fullFactorRepairLaw index).classify state with
  | .inl terminal => .inl terminal
  | .inr alternative => .inr (.repair alternative)

noncomputable def fullFactorDecayLaw (index : Nat) :
    Law (EffectiveSplitAt index) where
  TerminalAt := PrimePairTerminalAt
  StepAt := FactorDecayChannelAt
  target := FactorDecayChannelAt.target
  classify := fullFactorDecayClassify

@[simp] theorem fullFactorDecayLaw_classify {index : Nat}
    (state : EffectiveSplitAt index) :
    (fullFactorDecayLaw index).classify state =
      fullFactorDecayClassify state :=
  rfl

/-- A source-classified step is always the repair face.  This theorem audits
the deterministic spine only.  It must not be used to replace the complete
branching disposition, whose `StepAt` also contains every emission channel. -/
def generatedRepairAlternativeOfClassifiedStep {index : Nat}
    (state : EffectiveSplitAt index) (channel : FactorDecayChannelAt state)
    (classifier_eq : (fullFactorDecayLaw index).classify state = .inr channel) :
    { alternative : FactorRepairAlternativeAt state //
      channel = .repair alternative } := by
  change fullFactorDecayClassify state = .inr channel at classifier_eq
  unfold fullFactorDecayClassify at classifier_eq
  split at classifier_eq
  · contradiction
  · exact ⟨_, Sum.inr.inj classifier_eq |>.symm⟩

/-! ## Canonical unordered physical source selector -/

structure PhysicalTerminalSelectionAt {index : Nat}
    (source : EffectiveSplitAt index) : Type where
  terminal : PrimePairTerminalAt source
  classifier_eq :
    (fullFactorDecayLaw index).classify source = .inl terminal

inductive PhysicalChannelSelectionReasonAt {index : Nat}
    (source : EffectiveSplitAt index)
    (alternative : FactorRepairAlternativeAt source)
    (channel : FactorDecayChannelAt source) : Type
  | preferredRepair
      (repairProgress :
        FactorDecayChannelAt.IsPhysicalProgress (.repair alternative))
      (channel_eq : channel = .repair alternative)
  | preferredEmission
      (repairIdentity :
        unorderedSplitKey alternative.target = unorderedSplitKey source)
      (emissionProgress :
        FactorDecayChannelAt.IsPhysicalProgress (.emission alternative))
      (channel_eq : channel = .emission alternative)

structure PhysicalProgressChannelAt {index : Nat}
    (source : EffectiveSplitAt index) : Type where
  channel : FactorDecayChannelAt source
  physicalProgress : channel.IsPhysicalProgress
  classifierAlternative : FactorRepairAlternativeAt source
  classifier_eq :
    (fullFactorDecayLaw index).classify source =
      .inr (.repair classifierAlternative)
  selectionReason : PhysicalChannelSelectionReasonAt source
    classifierAlternative channel

abbrev FullPhysicalFactorDecayOutcomeAt {index : Nat}
    (source : EffectiveSplitAt index) :=
  PhysicalTerminalSelectionAt source ⊕
    PhysicalProgressChannelAt source

/-- One source-owned selector shared by arithmetic provenance, Fock dynamics
and debt.  The old repair spine is preserved exactly when nonzero; a swap
falls through to its paired emission, which the paired-action theorem proves
is nonzero. -/
noncomputable def fullPhysicalFactorDecayClassify {index : Nat}
    (source : EffectiveSplitAt index) :
    FullPhysicalFactorDecayOutcomeAt source := by
  generalize classifierEq :
    (fullFactorDecayLaw index).classify source = classifier
  cases classifier with
  | inl terminal => exact .inl ⟨terminal, classifierEq⟩
  | inr classifiedChannel =>
      let classified := generatedRepairAlternativeOfClassifiedStep
        source classifiedChannel classifierEq
      let alternative := classified.1
      have classifiedEq :
          (fullFactorDecayLaw index).classify source =
            .inr (.repair alternative) :=
        classifierEq.trans (congrArg Sum.inr classified.2)
      let repairChannel : FactorDecayChannelAt source := .repair alternative
      by_cases repairProgress : repairChannel.IsPhysicalProgress
      · exact .inr
          { channel := repairChannel
            physicalProgress := repairProgress
            classifierAlternative := alternative
            classifier_eq := classifiedEq
            selectionReason := .preferredRepair repairProgress rfl }
      · let emissionChannel : FactorDecayChannelAt source :=
          .emission alternative
        have emissionProgress : emissionChannel.IsPhysicalProgress :=
          (repair_or_emission_isPhysicalProgress alternative).resolve_left
            repairProgress
        exact .inr
          { channel := emissionChannel
            physicalProgress := emissionProgress
            classifierAlternative := alternative
            classifier_eq := classifiedEq
            selectionReason := .preferredEmission
              (not_ne_iff.mp repairProgress) emissionProgress rfl }

theorem PhysicalProgressChannelAt.channel_eq_preferredRepair {index : Nat}
    {source : EffectiveSplitAt index}
    (selected : PhysicalProgressChannelAt source)
    (alternative : FactorRepairAlternativeAt source)
    (classifierEq :
      (fullFactorDecayLaw index).classify source =
        .inr (.repair alternative))
    (repairProgress :
      FactorDecayChannelAt.IsPhysicalProgress (.repair alternative)) :
    selected.channel = .repair alternative := by
  have classifiedChannelEq :
      FactorDecayChannelAt.repair selected.classifierAlternative =
        .repair alternative :=
    Sum.inr.inj (selected.classifier_eq.symm.trans classifierEq)
  have alternativeEq : selected.classifierAlternative = alternative :=
    FactorDecayChannelAt.repair.inj classifiedChannelEq
  subst alternative
  cases selected.selectionReason with
  | preferredRepair _ channelEq => exact channelEq
  | preferredEmission repairIdentity _ _ =>
      exact False.elim (repairProgress repairIdentity)

theorem PhysicalProgressChannelAt.channel_eq_preferredEmission {index : Nat}
    {source : EffectiveSplitAt index}
    (selected : PhysicalProgressChannelAt source)
    (alternative : FactorRepairAlternativeAt source)
    (classifierEq :
      (fullFactorDecayLaw index).classify source =
        .inr (.repair alternative))
    (repairIdentity :
      unorderedSplitKey alternative.target = unorderedSplitKey source)
    (emissionProgress :
      FactorDecayChannelAt.IsPhysicalProgress (.emission alternative)) :
    selected.channel = .emission alternative := by
  have classifiedChannelEq :
      FactorDecayChannelAt.repair selected.classifierAlternative =
        .repair alternative :=
    Sum.inr.inj (selected.classifier_eq.symm.trans classifierEq)
  have alternativeEq : selected.classifierAlternative = alternative :=
    FactorDecayChannelAt.repair.inj classifiedChannelEq
  subst alternative
  cases selected.selectionReason with
  | preferredRepair progress _ =>
      exact False.elim (progress repairIdentity)
  | preferredEmission _ _ channelEq => exact channelEq

end
end CanonicalUnitArithmeticFullFactorEmissionProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
