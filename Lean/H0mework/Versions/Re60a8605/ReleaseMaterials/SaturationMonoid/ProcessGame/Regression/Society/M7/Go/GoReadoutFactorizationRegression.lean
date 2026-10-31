import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ReadoutFactorization
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.GoNaturalAuthorityReconstructionRegression

/-!
# M7 Go readout-factorization bridge

At every horizon the existing full normal-form projection remains a positive
visible identity computation.  The existing M6 Go attachment boundary rejects
both an authority-complete decoder and an actual-path-complete ko surrogate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M7GoReadoutFactorizationRegression

open Go.CrossOccurrencePathResidual
open Go.CrossOccurrenceClassicalResidual
open _root_.SaturationMonoid.ProcessGame.Go.Classical
open M6GoNaturalAuthorityReconstructionRegression
open Observer

def visibleNormalFormIdentity (horizon : Nat) :
    NormalizedImage horizon → NormalizedImage horizon :=
  id

def goNormalFormReadout (horizon : Nat) :
    OccurrenceReadout ActualPath (NormalizedImage horizon) :=
  OccurrenceReadout.ofVisible
    (goAuthorityObserver horizon) (visibleNormalFormIdentity horizon)

def goNormalFormFactorization (horizon : Nat) :
    ReadoutFactorization (goAuthorityObserver horizon)
      (goNormalFormReadout horizon) :=
  ReadoutFactorization.ofVisible
    (goAuthorityObserver horizon) (visibleNormalFormIdentity horizon)

theorem go_visible_normalForm_factorization_positive (horizon : Nat) :
    Nonempty
      (ReadoutFactorization (goAuthorityObserver horizon)
        (goNormalFormReadout horizon)) :=
  ReadoutFactorization.visibleComputation_nonempty
    (goAuthorityObserver horizon) (visibleNormalFormIdentity horizon)

theorem go_normalForm_readout_exact (horizon : Nat) (path : ActualPath) :
    (goNormalFormReadout horizon).read path =
      normalizedForget horizon path :=
  rfl

theorem go_normalForm_no_complete_authority_readout (horizon : Nat) :
    ¬ Nonempty
      (AuthorityCompleteReadoutAt (goAuthorityObserver horizon)
        (goNormalFormReadout horizon)) :=
  (goSourceGeneratedObserverAttachingDirection horizon)
    |>.boundary_noAuthorityCompleteReadout
      (goNormalFormFactorization horizon)

/-- Existing ko surrogate, exposed as a visible occurrence-valued readout. -/
def goKoSurrogatePathReadout (horizon : Nat) :
    OccurrenceReadout ActualPath ActualPath :=
  OccurrenceReadout.ofVisible
    (goAuthorityObserver horizon) (koSurrogateSection horizon)

def goKoSurrogatePathFactorization (horizon : Nat) :
    ReadoutFactorization (goAuthorityObserver horizon)
      (goKoSurrogatePathReadout horizon) :=
  ReadoutFactorization.ofVisible
    (goAuthorityObserver horizon) (koSurrogateSection horizon)

theorem go_ko_surrogate_no_complete_actual_path (horizon : Nat) :
    ¬ Nonempty
      (ActualOccurrenceCompleteReadoutAt
        (goKoSurrogatePathReadout horizon)) := by
  rintro ⟨complete⟩
  exact (goSourceGeneratedObserverAttachingDirection horizon)
    |>.boundary_rejectsActualCompleteReadout
      (goKoSurrogatePathFactorization horizon)
      (goSurrogateRightSection horizon) complete

structure GoReadoutFactorizationCertificate (horizon : Nat) : Prop where
  differentReplaySpines :
    koTerminalReplay.stateTrace ≠ freshTerminalReplay.stateTrace
  differentActualOccurrences :
    actualOccurrence koPath ≠ actualOccurrence freshPath
  honestNormalFormTransport : Nonempty
    (CrossReplayNormalFormEquivalence
      koTerminalReplay freshTerminalReplay horizon)
  equalVisibleNormalForm :
    normalizedForget horizon koPath = normalizedForget horizon freshPath
  differentReplayAuthority :
    pathAuthorityK koPath ≠ pathAuthorityK freshPath
  koAuthorityExact :
    pathAuthorityK koPath = actualizationK koTerminalReplay
  freshAuthorityExact :
    pathAuthorityK freshPath = actualizationK freshTerminalReplay
  positiveVisibleIdentityFactorization : Nonempty
    (ReadoutFactorization (goAuthorityObserver horizon)
      (goNormalFormReadout horizon))
  exactVisibleIdentityReadout : ∀ path,
    (goNormalFormReadout horizon).read path =
      normalizedForget horizon path
  exactAttachmentBoundary :
    (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.left =
        koPath ∧
      (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.right =
        freshPath ∧
      normalizedForget horizon
          (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.left =
        normalizedForget horizon
          (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.right ∧
      pathAuthorityK
          (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.left ≠
        pathAuthorityK
          (goSourceGeneratedObserverAttachingDirection horizon).boundaryKernelPair.right
  noCompleteAuthorityReadout : ¬ Nonempty
    (AuthorityCompleteReadoutAt (goAuthorityObserver horizon)
      (goNormalFormReadout horizon))
  noCompleteActualPathReadout : ¬ Nonempty
    (ActualOccurrenceCompleteReadoutAt
      (goKoSurrogatePathReadout horizon))

theorem goReadoutFactorizationDirectConsumer (horizon : Nat) :
    GoReadoutFactorizationCertificate horizon where
  differentReplaySpines := terminal_stateTraces_ne
  differentActualOccurrences := actualOccurrences_ne
  honestNormalFormTransport := ⟨normalFormEquivalence horizon⟩
  equalVisibleNormalForm := normalizedForget_paths_equal horizon
  differentReplayAuthority := pathAuthorityK_ne
  koAuthorityExact := pathAuthorityK_ko_replay
  freshAuthorityExact := pathAuthorityK_fresh_replay
  positiveVisibleIdentityFactorization :=
    go_visible_normalForm_factorization_positive horizon
  exactVisibleIdentityReadout := go_normalForm_readout_exact horizon
  exactAttachmentBoundary :=
    goObserverAttachingDirection_exact_boundary horizon
  noCompleteAuthorityReadout :=
    go_normalForm_no_complete_authority_readout horizon
  noCompleteActualPathReadout :=
    go_ko_surrogate_no_complete_actual_path horizon

end M7GoReadoutFactorizationRegression
end Society
end ProcessGame
end SaturationMonoid
