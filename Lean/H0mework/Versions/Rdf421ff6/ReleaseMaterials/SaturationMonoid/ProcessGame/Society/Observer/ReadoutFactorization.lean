import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.ObserverObstructionDirection

/-!
# Observer-factored readouts and reconstruction forcing

This module separates three claims which are often conflated by an
identification, aggregation, matching, or narrative rule:

* a readout can be computed from the visible image;
* that readout can recover source-native authority;
* an occurrence-valued readout can recover the actual occurrence naturally.

Visible computation is always available.  Authority completeness generates
an `AuthorityFactorization`; actual-occurrence completeness, together with an
ordinary surrogate section, generates a faithful reconstruction; naturality
of that same readout generates a natural section.  Consequently an M6 source-
generated attachment can reject the stronger claims at its own boundary while
leaving ordinary visible computation untouched.

All carriers and universes are arbitrary.  No finite agent set, alternative
set, sample, archive, decidable equality, or classical impossibility theorem
is assumed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Observer

universe uOccurrence uVisible uResidual uOutput

variable {Occurrence : Type uOccurrence}
variable {Visible : Type uVisible}
variable {Residual : Type uResidual}
variable {Output : Type uOutput}
variable {O : AuthorityObserver Occurrence Visible Residual}

/-- An occurrence-indexed policy or readout.  It carries no assertion that
its result is visible, authoritative, complete, or natural. -/
structure OccurrenceReadout
    (Occurrence : Type uOccurrence)
    (Output : Type uOutput) where
  read : Occurrence → Output

/-- Policies and readouts have the same generic factorization problem. -/
abbrev OccurrencePolicy
    (Occurrence : Type uOccurrence)
    (Decision : Type uOutput) :=
  OccurrenceReadout Occurrence Decision

/-- Evidence that one exact occurrence readout uses only the observer's
visible image.  The visible implementation is explicit, and the commuting
law is required for every occurrence rather than a selected calibration
family. -/
structure ReadoutFactorization
    (O : AuthorityObserver Occurrence Visible Residual)
    (readout : OccurrenceReadout Occurrence Output) where
  visibleReadout : Visible → Output
  factorizes : ∀ occurrence,
    readout.read occurrence = visibleReadout (O.forget occurrence)

/-- Policy terminology for the same exact observer factorization. -/
abbrev PolicyFactorization
    (O : AuthorityObserver Occurrence Visible Residual)
    (policy : OccurrencePolicy Occurrence Output) :=
  ReadoutFactorization O policy

namespace OccurrenceReadout

/-- Every computation already defined on visible images induces a lawful
occurrence readout.  This is the positive half of the interface. -/
def ofVisible
    (O : AuthorityObserver Occurrence Visible Residual)
    (visibleReadout : Visible → Output) :
    OccurrenceReadout Occurrence Output where
  read := fun occurrence => visibleReadout (O.forget occurrence)

end OccurrenceReadout

namespace ReadoutFactorization

/-- The readout induced by a visible computation factors definitionally.
No authority-completeness claim is manufactured by this construction. -/
def ofVisible
    (O : AuthorityObserver Occurrence Visible Residual)
    (visibleReadout : Visible → Output) :
    ReadoutFactorization O (OccurrenceReadout.ofVisible O visibleReadout) where
  visibleReadout := visibleReadout
  factorizes := fun _ => rfl

/-- Arbitrary visible computation therefore remains inhabited even in the
presence of a nontrivial authority fibre. -/
theorem visibleComputation_nonempty
    (O : AuthorityObserver Occurrence Visible Residual)
    (visibleReadout : Visible → Output) :
    Nonempty
      (ReadoutFactorization O
        (OccurrenceReadout.ofVisible O visibleReadout)) :=
  ⟨ofVisible O visibleReadout⟩

end ReadoutFactorization

/-- A readout claims authority completeness when one decoder recovers the
actual source-native `K` on every occurrence.  This claim is deliberately
separate from visible factorization: neither one contains the other. -/
structure AuthorityCompleteReadoutAt
    (O : AuthorityObserver Occurrence Visible Residual)
    (readout : OccurrenceReadout Occurrence Output) where
  decodeAuthority : Output → Residual
  readsActualAuthority : ∀ occurrence,
    decodeAuthority (readout.read occurrence) = O.authorityK occurrence

namespace ReadoutFactorization

variable {readout : OccurrenceReadout Occurrence Output}

/-- A visible factorization plus authority-complete decoding generates the
M6 authority factorization.  The caller supplies only the concrete readout,
its visible implementation, and its advertised decoding law; the forbidden
factorization is the theorem output. -/
def toAuthorityFactorization
    (factorization : ReadoutFactorization O readout)
    (complete : AuthorityCompleteReadoutAt O readout) :
    AuthorityFactorization O where
  readAuthority := fun visible =>
    complete.decodeAuthority (factorization.visibleReadout visible)
  preservesActualAuthority := fun occurrence => by
    calc
      complete.decodeAuthority
          (factorization.visibleReadout (O.forget occurrence)) =
          complete.decodeAuthority (readout.read occurrence) :=
        congrArg complete.decodeAuthority
          (factorization.factorizes occurrence).symm
      _ = O.authorityK occurrence :=
        complete.readsActualAuthority occurrence

end ReadoutFactorization

/-- An occurrence-valued readout claims actual completeness by identifying
every occurrence with its own result.  It does not contain a visible section,
left inverse, authority factorization, or naturality field. -/
structure ActualOccurrenceCompleteReadoutAt
    (readout : OccurrenceReadout Occurrence Occurrence) where
  readsActualOccurrence : ∀ occurrence,
    readout.read occurrence = occurrence

/-- Naturality of the visible implementation of an occurrence-valued
readout.  This is stated as equivariance under every admissible observer
automorphism, before any section is constructed. -/
structure NaturalOccurrenceReadoutAt
    (O : AuthorityObserver Occurrence Visible Residual)
    {readout : OccurrenceReadout Occurrence Occurrence}
    (factorization : ReadoutFactorization O readout) where
  commutesWithAutomorphisms :
    ∀ automorphism : AdmissibleObserverAutomorphism O,
      ∀ visible,
        factorization.visibleReadout
            (automorphism.visibleEquiv visible) =
          automorphism.occurrenceEquiv
            (factorization.visibleReadout visible)

/-- The exact two-sided reconstruction forced by an actual-complete,
observer-factored occurrence readout over a surjective visible image.  It is
an output carrier for the forcing theorem below, not an input premise. -/
structure ForcedActualReconstruction
    (O : AuthorityObserver Occurrence Visible Residual) where
  reconstruct : Visible → Occurrence
  recoversVisible : Function.RightInverse reconstruct O.forget
  recoversActual : Function.LeftInverse reconstruct O.forget

namespace ReadoutFactorization

variable {readout : OccurrenceReadout Occurrence Occurrence}

/-- Actual identification cannot remain a harmless visible computation.
Given only an ordinary surrogate proving reachability of every visible point,
factorization plus exact occurrence identification forces a two-sided actual
reconstruction. -/
def forceActualReconstruction
    (factorization : ReadoutFactorization O readout)
    (surrogate : SurrogateRightSection O)
    (complete : ActualOccurrenceCompleteReadoutAt readout) :
    ForcedActualReconstruction O where
  reconstruct := factorization.visibleReadout
  recoversVisible := fun visible => by
    let occurrence := surrogate.lift visible
    have occurrence_visible : O.forget occurrence = visible :=
      surrogate.lift_forget visible
    have reconstructed_occurrence :
        factorization.visibleReadout visible = occurrence := by
      calc
        factorization.visibleReadout visible =
            factorization.visibleReadout (O.forget occurrence) :=
          congrArg factorization.visibleReadout occurrence_visible.symm
        _ = readout.read occurrence :=
          (factorization.factorizes occurrence).symm
        _ = occurrence := complete.readsActualOccurrence occurrence
    calc
      O.forget (factorization.visibleReadout visible) =
          O.forget occurrence := congrArg O.forget reconstructed_occurrence
      _ = visible := occurrence_visible
  recoversActual := fun occurrence => by
    calc
      factorization.visibleReadout (O.forget occurrence) =
          readout.read occurrence :=
        (factorization.factorizes occurrence).symm
      _ = occurrence := complete.readsActualOccurrence occurrence

end ReadoutFactorization

namespace ForcedActualReconstruction

/-- Actual reconstruction automatically supplies a faithful authority
reconstruction by reading `K` from the reconstructed occurrence.  Authority
preservation is derived from `recoversActual`; it is not another premise. -/
def toFaithfulAuthorityReconstruction
    (forced : ForcedActualReconstruction O) :
    FaithfulAuthorityReconstruction O where
  lift := forced.reconstruct
  lift_forget := forced.recoversVisible
  readAuthority := fun visible => O.authorityK (forced.reconstruct visible)
  preservesActualAuthority := fun occurrence =>
    congrArg O.authorityK (forced.recoversActual occurrence)
  recoversOccurrence := forced.recoversActual

end ForcedActualReconstruction

/-- Natural actual reconstruction is the output forced when the same
occurrence-valued readout is also equivariant.  The structure records the
already-derived two-sided reconstruction and its derived naturality. -/
structure ForcedNaturalActualReconstruction
    (O : AuthorityObserver Occurrence Visible Residual)
    extends ForcedActualReconstruction O where
  naturality : ∀ automorphism : AdmissibleObserverAutomorphism O,
    ∀ visible,
      reconstruct (automorphism.visibleEquiv visible) =
        automorphism.occurrenceEquiv (reconstruct visible)

namespace NaturalOccurrenceReadoutAt

variable {readout : OccurrenceReadout Occurrence Occurrence}
variable {factorization : ReadoutFactorization O readout}

/-- Readout equivariance upgrades the forced actual reconstruction to a
genuinely natural one. -/
def forceNaturalActualReconstruction
    (naturalReadout : NaturalOccurrenceReadoutAt O factorization)
    (surrogate : SurrogateRightSection O)
    (complete : ActualOccurrenceCompleteReadoutAt readout) :
    ForcedNaturalActualReconstruction O where
  toForcedActualReconstruction :=
    factorization.forceActualReconstruction surrogate complete
  naturality := naturalReadout.commutesWithAutomorphisms

end NaturalOccurrenceReadoutAt

namespace ForcedNaturalActualReconstruction

/-- Forget actual recovery and retain the genuinely natural surrogate
section forced by the equivariant readout.  Authority equivariance follows
from readout naturality and the observer automorphism law. -/
def toNaturalSurrogateSection
    (forced : ForcedNaturalActualReconstruction O) :
    NaturalSurrogateSection O where
  lift := forced.reconstruct
  lift_forget := forced.recoversVisible
  naturality := forced.naturality
  preservesAuthority := fun automorphism visible => by
    calc
      O.authorityK
          (forced.reconstruct (automorphism.visibleEquiv visible)) =
          O.authorityK
            (automorphism.occurrenceEquiv
              (forced.reconstruct visible)) :=
        congrArg O.authorityK (forced.naturality automorphism visible)
      _ = automorphism.authorityEquiv
          (O.authorityK (forced.reconstruct visible)) :=
        automorphism.authority_commutes (forced.reconstruct visible)

/-- The forced natural reconstruction generates the full M6 natural
authority reconstruction.  Both authority laws follow from actual recovery
and admissible-automorphism commutation. -/
def toNaturalAuthorityReconstruction
    (forced : ForcedNaturalActualReconstruction O) :
    NaturalAuthorityReconstruction O where
  lift := forced.reconstruct
  lift_forget := forced.recoversVisible
  naturality := forced.naturality
  preservesAuthority := fun automorphism visible => by
    calc
      O.authorityK
          (forced.reconstruct (automorphism.visibleEquiv visible)) =
          O.authorityK
            (automorphism.occurrenceEquiv
              (forced.reconstruct visible)) :=
        congrArg O.authorityK (forced.naturality automorphism visible)
      _ = automorphism.authorityEquiv
          (O.authorityK (forced.reconstruct visible)) :=
        automorphism.authority_commutes (forced.reconstruct visible)
  readAuthority := fun visible => O.authorityK (forced.reconstruct visible)
  preservesActualAuthority := fun occurrence =>
    congrArg O.authorityK (forced.recoversActual occurrence)
  recoversOccurrence := forced.recoversActual

end ForcedNaturalActualReconstruction

namespace SourceGeneratedObserverAttachingDirectionAt

variable {vertical : AuthorityChangingVerticalAutomorphism O}
variable {rooted : RootedObserverObstructionAt vertical}

/-- The M6 generated boundary directly rejects any authority-complete
visible factorization, whatever the readout carrier may be. -/
theorem boundary_rejectsAuthorityCompleteReadout
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted)
    {readout : OccurrenceReadout Occurrence Output}
    (factorization : ReadoutFactorization O readout)
    (complete : AuthorityCompleteReadoutAt O readout) :
    False :=
  attachment.boundary_noAuthorityFactorization
    ⟨factorization.toAuthorityFactorization complete⟩

/-- Verdict for a fixed visible implementation: it cannot also be authority
complete at this boundary. -/
theorem boundary_noAuthorityCompleteReadout
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted)
    {readout : OccurrenceReadout Occurrence Output}
    (factorization : ReadoutFactorization O readout) :
    ¬ Nonempty (AuthorityCompleteReadoutAt O readout) := by
  rintro ⟨complete⟩
  exact attachment.boundary_rejectsAuthorityCompleteReadout
    factorization complete

/-- The same boundary rejects the actual-reconstruction object generated by
an actual-complete occurrence readout. -/
theorem boundary_rejectsForcedActualReconstruction
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted)
    (forced : ForcedActualReconstruction O) :
    False :=
  attachment.boundaryKernelPair.noFaithfulAuthorityReconstruction
    ⟨forced.toFaithfulAuthorityReconstruction⟩

/-- Direct axiom-to-section verdict.  A surrogate section may exist, but no
observer-factored readout over it can identify every actual occurrence. -/
theorem boundary_rejectsActualCompleteReadout
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted)
    {readout : OccurrenceReadout Occurrence Occurrence}
    (factorization : ReadoutFactorization O readout)
    (surrogate : SurrogateRightSection O)
    (complete : ActualOccurrenceCompleteReadoutAt readout) :
    False :=
  attachment.boundary_rejectsForcedActualReconstruction
    (factorization.forceActualReconstruction surrogate complete)

/-- The generated attachment is indexed by the exact vertical obstruction;
therefore its boundary also rejects the natural section forced by an
equivariant actual-complete readout. -/
theorem boundary_rejectsNaturalActualCompleteReadout
    (attachment : SourceGeneratedObserverAttachingDirectionAt rooted)
    {readout : OccurrenceReadout Occurrence Occurrence}
    {factorization : ReadoutFactorization O readout}
    (naturalReadout : NaturalOccurrenceReadoutAt O factorization)
    (surrogate : SurrogateRightSection O)
    (complete : ActualOccurrenceCompleteReadoutAt readout) :
    False :=
  attachment.boundary_noNaturalAuthorityReconstruction
    ⟨(naturalReadout.forceNaturalActualReconstruction surrogate complete)
      |>.toNaturalAuthorityReconstruction⟩

end SourceGeneratedObserverAttachingDirectionAt

/-- Identity observation is the unrestricted positive control. -/
def identityAuthorityObserver
    (authorityK : Occurrence → Residual) :
    AuthorityObserver Occurrence Occurrence Residual where
  forget := id
  authorityK := authorityK

/-- Every occurrence readout factors through the identity observer. -/
def identityReadoutFactorization
    (authorityK : Occurrence → Residual)
    (readout : OccurrenceReadout Occurrence Output) :
    ReadoutFactorization (identityAuthorityObserver authorityK) readout where
  visibleReadout := readout.read
  factorizes := fun _ => rfl

/-- Exact `K` itself is an authority-complete identity-observer readout. -/
def identityAuthorityReadout
    (authorityK : Occurrence → Residual) :
    OccurrenceReadout Occurrence Residual where
  read := authorityK

def identityAuthorityCompleteReadout
    (authorityK : Occurrence → Residual) :
    AuthorityCompleteReadoutAt
      (identityAuthorityObserver authorityK)
      (identityAuthorityReadout authorityK) where
  decodeAuthority := id
  readsActualAuthority := fun _ => rfl

/-- The positive identity control realizes the readout-to-factorization
producer rather than merely asserting that its output type is inhabited. -/
def identityAuthorityFactorization
    (authorityK : Occurrence → Residual) :
    AuthorityFactorization (identityAuthorityObserver authorityK) :=
  (identityReadoutFactorization authorityK
    (identityAuthorityReadout authorityK)).toAuthorityFactorization
      (identityAuthorityCompleteReadout authorityK)

/-- The identity observer admits a forced two-sided reconstruction. -/
def identityForcedActualReconstruction
    (authorityK : Occurrence → Residual) :
    ForcedActualReconstruction (identityAuthorityObserver authorityK) where
  reconstruct := id
  recoversVisible := fun _ => rfl
  recoversActual := fun _ => rfl

/-- The identity observer admits the full natural reconstruction for
arbitrary occurrence and residual carriers. -/
def identityForcedNaturalActualReconstruction
    (authorityK : Occurrence → Residual) :
    ForcedNaturalActualReconstruction
      (identityAuthorityObserver authorityK) where
  toForcedActualReconstruction :=
    identityForcedActualReconstruction authorityK
  naturality := by
    intro automorphism occurrence
    exact (automorphism.forget_commutes occurrence).symm

theorem identityObserver_hasNaturalAuthorityReconstruction
    (authorityK : Occurrence → Residual) :
    Nonempty
      (NaturalAuthorityReconstruction
        (identityAuthorityObserver authorityK)) :=
  ⟨(identityForcedNaturalActualReconstruction authorityK)
    |>.toNaturalAuthorityReconstruction⟩

end Observer
end Society
end ProcessGame
end SaturationMonoid
