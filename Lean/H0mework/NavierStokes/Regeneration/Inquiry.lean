import H0mework.NavierStokes.Regeneration.Standard

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFiniteInquiry

open Set
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock

noncomputable section

abbrev Solution := StandardGlobalWholeMildSerrinSolutionAt concreteCounterexampleViscosity
  concreteCounterexampleInitial.initialState

/-- Finite observation of the original face compiler. The right output is
the retained reachable frontier; the left output ends this inquiry. -/
def inquire : (depth : Nat) → Solution ⊕
    (Σ face : ButterflyCreditClockFaceAt (source.stateAfter depth),
      ButterflyCreditClockFaceReachableAt depth face)
  | 0 => .inr ⟨.capped butterflyZeroBankInitialInstruction, .initial⟩
  | depth + 1 =>
      match inquire depth with
      | .inl solution => .inl solution
      | .inr ⟨face, reachable⟩ =>
          match butterflyCreditClockFaceTotalTransition depth face
              (sourceGeneratedStandingActionRunClockDisposition
                stackedInitialActionMaterialInstruction depth) with
          | .inl paid => .inr ⟨(butterflyRetainFaceSettlement depth paid.2).1,
              .next reachable paid.2⟩
          | .inr shortfall => .inl
              (SourceFieldRenewal.standardGlobalOfReachableResidual reachable shortfall)

/-- Every returned solution retains an exact earlier compiler failure on
this same finite inquiry, rather than a separate global/bounded classifier. -/
theorem returnedOld_origin (depth : Nat) (solution : Solution)
    (returned : inquire depth = .inl solution) :
    ∃ prior < depth,
      ∃ face : ButterflyCreditClockFaceAt (source.stateAfter prior),
      ∃ reachable : ButterflyCreditClockFaceReachableAt prior face,
      ∃ shortfall : ButterflyCreditClockFaceResidualAt prior face
          (sourceGeneratedStandingActionRunClockDisposition
            stackedInitialActionMaterialInstruction prior),
        inquire prior = .inr ⟨face, reachable⟩ ∧
        butterflyCreditClockFaceTotalTransition prior face
            (sourceGeneratedStandingActionRunClockDisposition
              stackedInitialActionMaterialInstruction prior) = .inr shortfall ∧
        solution = SourceFieldRenewal.standardGlobalOfReachableResidual reachable shortfall := by
  induction depth with
  | zero => simp only [inquire, reduceCtorEq] at returned
  | succ depth inductionHypothesis =>
      cases previous : inquire depth with
      | inl earlier =>
          have same : earlier = solution := by simpa only [inquire, previous, Sum.inl.injEq] using returned
          subst solution
          obtain ⟨prior, before, face, reachable, shortfall, origin⟩ :=
            inductionHypothesis previous
          exact ⟨prior, Nat.lt_succ_of_lt before, face, reachable, shortfall, origin⟩
      | inr frontier =>
          rcases frontier with ⟨face, reachable⟩
          cases edge : butterflyCreditClockFaceTotalTransition depth face
              (sourceGeneratedStandingActionRunClockDisposition
                stackedInitialActionMaterialInstruction depth) with
          | inl paid => simp only [inquire, previous, edge, reduceCtorEq] at returned
          | inr shortfall =>
              refine ⟨depth, Nat.lt_succ_self _, face, reachable, shortfall, previous, edge, ?_⟩
              simpa only [inquire, previous, edge, Sum.inl.injEq] using returned.symm

theorem beyond_bank_returns_old (depth : Nat)
    (beyond : butterflyInitialTotalClockBank <
      elapsedTime concreteCounterexampleInitial (depth + 1)) :
    ∃ solution : Solution, inquire depth = .inl solution := by
  cases inquire depth with
  | inl solution => exact ⟨solution, rfl⟩
  | inr frontier =>
      rcases frontier with ⟨face, reachable⟩
      have account := butterflyReachable_elapsedTime_succ_add_potential_eq_initial reachable
      have nonneg := face.clockState.potential_nonneg
      linarith

/-- Global existence is equivalent to an old answer from this original
finite inquiry. Completeness uses a finite crossing of its exact source bank. -/
theorem standardGlobal_nonempty_iff_returns_old :
    Nonempty Solution ↔ ∃ depth : Nat, ∃ solution : Solution, inquire depth = .inl solution := by
  constructor
  · intro existsSolution
    have unbounded := WholeGlobalReceipt.standardGlobal_nonempty_iff_unbounded.mp existsSolution
    obtain ⟨time, ⟨depth, rfl⟩, beyond⟩ :=
      not_bddAbove_iff.mp unbounded butterflyInitialTotalClockBank
    have later := (elapsedTime_strictMono concreteCounterexampleInitial).monotone (Nat.le_succ depth)
    exact ⟨depth, beyond_bank_returns_old depth (beyond.trans_le later)⟩
  · rintro ⟨_depth, solution, _returned⟩
    exact ⟨solution⟩

end
end SaturationMonoid.NavierStokes.SourceFiniteInquiry
