/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M7.Go.GoReadoutFactorizationRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Probability.Consumer.ObserverConditionedPrediction

/-!
# M12 Go normal-form probability no-go

At every horizon a fixed probability-valued computation on the classical
normal form is a lawful visible readout.  The existing ko/fresh replay kernel
pair still forbids that probability from decoding path authority or actual
occurrence identity.  No Go-specific probability producer is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M12GoNormalFormProbabilityRegression

noncomputable section

open Go.CrossOccurrencePathResidual
open Go.CrossOccurrenceClassicalResidual
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open Observer Probability Consumer
open M6GoNaturalAuthorityReconstructionRegression
open M7GoReadoutFactorizationRegression

/-- Fixed downstream probability computation on the visible normal form. -/
def visibleUniformProbability (horizon : Nat) :
    NormalizedImage horizon → Option ℚ≥0 :=
  fun _visible => some (1 / 2)

def goProbabilityReadout (horizon : Nat) :
    OccurrenceReadout ActualPath (Option ℚ≥0) :=
  OccurrenceReadout.ofVisible
    (goAuthorityObserver horizon) (visibleUniformProbability horizon)

def goProbabilityFactorization (horizon : Nat) :
    ReadoutFactorization (goAuthorityObserver horizon)
      (goProbabilityReadout horizon) :=
  ReadoutFactorization.ofVisible
    (goAuthorityObserver horizon) (visibleUniformProbability horizon)

@[simp] theorem goProbabilityReadout_exact
    (horizon : Nat) (path : ActualPath) :
    (goProbabilityReadout horizon).read path = some (1 / 2) :=
  rfl

/-- Ko and fresh replays have the same probability readout because they have
the same arbitrary-horizon normal form. -/
theorem go_paths_same_probability (horizon : Nat) :
    (goProbabilityReadout horizon).read koPath =
      (goProbabilityReadout horizon).read freshPath := by
  rfl

/-- Visible probability cannot become an authority decoder across the exact
ko/fresh replay kernel pair. -/
theorem go_probability_not_authority_complete (horizon : Nat) :
    ¬ Nonempty (AuthorityCompleteReadoutAt
      (goAuthorityObserver horizon) (goProbabilityReadout horizon)) := by
  rintro ⟨complete⟩
  exact (goAuthorityKernelPair horizon).noAuthorityFactorization
    ⟨(goProbabilityFactorization horizon).toAuthorityFactorization complete⟩

def goProbabilityClassification (horizon : Nat) (path : ActualPath) :
    Option ObserverConditionedPredictionClass :=
  ObserverConditionedPredictionClass.ofReadout
    ((goProbabilityReadout horizon).read path)

@[simp] theorem goProbabilityClassification_equalHalf
    (horizon : Nat) (path : ActualPath) :
    goProbabilityClassification horizon path =
      some ObserverConditionedPredictionClass.equalHalf := by
  unfold goProbabilityClassification
  apply (ObserverConditionedPredictionClass.ofReadout_eq_some_equalHalf_iff _).2
  refine ⟨1 / 2, rfl, ?_⟩
  rfl

structure GoNormalFormProbabilityCertificate (horizon : Nat) where
  crossOccurrenceNormalForm :
    M7GoReadoutFactorizationRegression.GoReadoutFactorizationCertificate horizon
  sameProbability :
    (goProbabilityReadout horizon).read koPath =
      (goProbabilityReadout horizon).read freshPath
  differentActualOccurrences :
    actualOccurrence koPath ≠ actualOccurrence freshPath
  differentAuthority : pathAuthorityK koPath ≠ pathAuthorityK freshPath
  visibleFactorization :
    ReadoutFactorization (goAuthorityObserver horizon)
      (goProbabilityReadout horizon)
  noAuthorityCompleteProbability : ¬ Nonempty
    (AuthorityCompleteReadoutAt
      (goAuthorityObserver horizon) (goProbabilityReadout horizon))

def goNormalFormProbabilityDirectConsumer (horizon : Nat) :
    GoNormalFormProbabilityCertificate horizon where
  crossOccurrenceNormalForm := goReadoutFactorizationDirectConsumer horizon
  sameProbability := go_paths_same_probability horizon
  differentActualOccurrences := actualOccurrences_ne
  differentAuthority := pathAuthorityK_ne
  visibleFactorization := goProbabilityFactorization horizon
  noAuthorityCompleteProbability :=
    go_probability_not_authority_complete horizon

end
end M12GoNormalFormProbabilityRegression
end Society
end ProcessGame
end SaturationMonoid
