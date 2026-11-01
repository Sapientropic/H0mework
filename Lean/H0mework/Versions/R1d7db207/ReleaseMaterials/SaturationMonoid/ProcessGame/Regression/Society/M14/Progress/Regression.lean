import H0mework.Versions.R1d7db207.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Progress.WholeProgram

/-! Direct consumption and negative controls for canonical structural progress. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.Regression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14WholeProgramRegression
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedPostSettlementObserverFinitePaidExitLifecycleStitch
open M14SourceGeneratedCycleMaximalCanonicalPaidStep
open M14SourceGeneratedContributionCapacityPostSettlementFutureBirth
open M14SourceGeneratedContributionCapacityBirthBearerExit
open M14SourceGeneratedContributionCapacityCofinalProductiveNovelty

/-- The concrete original M9 visit witnesses non-vacuity. A zero observation
fuel still consumes the first actual Payment and its generated next Payment. -/
theorem zeroFuel_has_two_strict_paid_edges :
    ∃ initial : CycleAt
        M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.initialVisit 0 0,
      StrictCanonicalProgressAt initial 0 1 ∧ StrictCanonicalProgressAt initial 1 2 := by
  obtain ⟨certificate⟩ := canonicalSociety_registeredFiniteCycleStrictCanonicalProgress
    0 M9ProofCarryingRenewalInquiryRoot.jointRoot.toAuthoritativeRoot.toRoot.initialVisit 0 0 0
  exact ⟨certificate.1,
    (certificate.2.everyPayment ⟨0, by decide⟩
      (cycleMaximalSourcePaymentAt certificate.1 0)).strictProgress,
    (certificate.2.generatedNext (cycleMaximalSourcePaymentAt certificate.1 1)).strictProgress⟩

/-- An explicit later finite window consumes the same universal mouth. -/
theorem arbitraryWindow_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary fuel : Nat) :
    Nonempty { initial : CycleAt oldVisit sourceIndex boundary //
      FiniteStrictCanonicalProgressAt initial fuel } :=
  canonicalSociety_registeredFiniteCycleStrictCanonicalProgress 0 oldVisit
    sourceIndex boundary fuel

/-- Fresh, source-paid life can accrue while instantaneous exit capacity is
unchanged. This rules out silently replacing the proved order by a scalar
claim that every current has more available exit choices. -/
theorem strictProgress_with_unchangedExitCapacity
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    StrictCanonicalProgressAt initial depth (depth + 1) ∧
      (birthBearerGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth))).actionableExitCapacity =
      (birthBearerGeometryCompilerAt
        (contributionCapacityPostSettlementFutureBirthCurrentAt oldVisit sourceIndex
          (cycleLifecycleIndex initial depth + 1))).actionableExitCapacity := by
  refine ⟨(strictCanonicalProgress_iff_lt initial depth (depth + 1)).mpr
    (Nat.lt_succ_self depth), ?_⟩
  exact
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth)).exitCapacityOne_captureZero.1.trans
    (sourceGeneratedContributionCapacityPostSettlementFutureBirthAt oldVisit sourceIndex
      (cycleLifecycleIndex initial depth + 1)).exitCapacityOne_captureZero.1.symm

/-- The very same edge has equal real pulse normal forms and unequal actual
K, even though its paid authority frontier grows strictly. -/
theorem equalPulse_doesNotEraseStrictProgress
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (depth : Nat) :
    let difference := sameEdgeResponsibilityDifference initial depth
    let observer := contributionCapacityPostSettlementPaidReplayPulseObserver oldVisit sourceIndex
    observer.forget difference.leftReplay = observer.forget difference.rightReplay ∧
      observer.authorityK difference.leftReplay ≠ observer.authorityK difference.rightReplay ∧
      StrictCanonicalProgressAt initial depth (depth + 1) := by
  have different := (sameEdgeResponsibilityDifference initial depth).sameRealNormalFormDifferentActualK
  exact ⟨different.1, different.2,
    (strictCanonicalProgress_iff_lt initial depth (depth + 1)).mpr (Nat.lt_succ_self depth)⟩

/-- A no-loss transition without any new authority is non-strict. -/
theorem preservation_without_novelty_is_not_strict (oldVisit : OldVisit)
    (sourceIndex start horizon : Nat) :
    ¬ authoritySupport oldVisit sourceIndex start horizon ⊂
      authoritySupport oldVisit sourceIndex start horizon :=
  lt_irrefl _

/-- A genuinely new witness does not excuse deleting an old one. -/
theorem novelty_without_preservation_is_not_strict :
    (1 : Nat) ∈ ({1} : Set Nat) ∧ 1 ∉ ({0} : Set Nat) ∧
      ¬ ({0} : Set Nat) ⊂ {1} := by
  refine ⟨by simp, by simp, ?_⟩
  intro h
  have := h.1 (show (0 : Nat) ∈ ({0} : Set Nat) by simp)
  simp at this

/-- Cofinality alone permits quiet ticks. The per-Payment result must use the
actual target birth, not promote a cofinal statement to every micro tick. -/
theorem cofinal_growth_does_not_imply_every_tick :
    ∃ f : Nat → Nat,
      (∀ n, ∃ m, n < m ∧ f n < f m) ∧ ¬ (∀ n, f n < f (n + 1)) := by
  refine ⟨fun n => n / 2, ?_, ?_⟩
  · intro n
    refine ⟨2 * (n + 1), by omega, ?_⟩
    change n / 2 < (2 * (n + 1)) / 2
    omega
  · intro h
    have h0 : (0 : Nat) / 2 < 1 / 2 := h 0
    omega

end
end SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.Regression

#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.Regression.zeroFuel_has_two_strict_paid_edges
#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.Regression.strictProgress_with_unchangedExitCapacity
#print axioms SaturationMonoid.ProcessGame.Society.CanonicalSocietyProgress.Regression.cofinal_growth_does_not_imply_every_tick
