import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.AuthorityObserver
import H0mework.Foundation.Responsibility.Observer

/-!
# Common authority observer restrictions

A common observer family collects several restrictions of the same actual
occurrence.  Its joint visible image is the dependent tuple of all member
readouts, while every member retains the one source-native authority map.

This interface does not transport between different actual occurrences.  A
comparison between distinct source occurrences still requires an independent
source-owned transporter.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Beauty
namespace SharedKernel

open ProcessGame.Society.Observer
open ResponsibilityLifecycle

universe uOccurrence uResidual uFamily

/-- A nonempty family of visible restrictions of one actual occurrence,
sharing exactly one source-native authority readout. -/
structure CommonAuthorityObserverFamily
    (Occurrence : Type uOccurrence)
    (Residual : Type uResidual) where
  Member : Type uFamily
  Visible : Member → Type uFamily
  forget : (member : Member) → Occurrence → Visible member
  authorityK : Occurrence → Residual
  positive : Nonempty Member

namespace CommonAuthorityObserverFamily

variable {Occurrence : Type uOccurrence}
variable {Residual : Type uResidual}
variable (F : CommonAuthorityObserverFamily Occurrence Residual)

/-- The public image jointly retained by every restriction of the same
occurrence. -/
abbrev JointVisible := (member : F.Member) → F.Visible member

/-- Joint observation of one occurrence.  No cross-occurrence transport is
performed here. -/
def jointForget (occurrence : Occurrence) : F.JointVisible :=
  fun member => F.forget member occurrence

/-- One member restriction viewed as an ordinary authority observer. -/
def observerAt (member : F.Member) :
    AuthorityObserver Occurrence (F.Visible member) Residual where
  forget := F.forget member
  authorityK := F.authorityK

/-- The common authority observer whose visible side contains all member
restrictions and whose residual remains the original source authority. -/
def jointAuthorityObserver :
    AuthorityObserver Occurrence F.JointVisible Residual where
  forget := F.jointForget
  authorityK := F.authorityK

/-- Equality in the joint kernel is exactly equality under every member
restriction. -/
theorem jointForget_eq_iff {left right : Occurrence} :
    F.jointForget left = F.jointForget right ↔
      ∀ member, F.forget member left = F.forget member right := by
  constructor
  · intro jointEq member
    exact congrFun jointEq member
  · intro memberEq
    funext member
    exact memberEq member

/-! ## Member projections and consumer safety -/

/-- Evaluation at one family member. -/
def memberProjection (member : F.Member) :
    F.JointVisible → F.Visible member :=
  fun joint => joint member

@[simp] theorem memberProjection_jointForget
    (member : F.Member) (occurrence : Occurrence) :
    F.memberProjection member (F.jointForget occurrence) =
      F.forget member occurrence :=
  rfl

/-- Every member restriction factors through the joint observation. -/
theorem memberProjection_comp_jointForget (member : F.Member) :
    F.memberProjection member ∘ F.jointForget = F.forget member := by
  funext occurrence
  rfl

/-- Consequently the joint observation is certified safe for every member
readout consumer. -/
theorem memberForget_consumerSafe (member : F.Member) :
    ConsumerSafe F.jointForget (F.forget member) :=
  ConsumerSafe.of_factorization (F.memberProjection member)
    (fun _ => rfl)

/-! ## Exact joint kernel pairs and hidden authority -/

/-- Build an exact joint authority-kernel pair from endpoint facts.  The
joint visible equality is generated from memberwise equalities rather than
accepted as an additional tuple-level premise. -/
def jointAuthorityKernelPair
    (left right : Occurrence)
    (occurrence_ne : left ≠ right)
    (memberVisible_eq :
      ∀ member, F.forget member left = F.forget member right)
    (authority_ne : F.authorityK left ≠ F.authorityK right) :
    AuthorityKernelPair F.jointAuthorityObserver where
  left := left
  right := right
  occurrence_ne := occurrence_ne
  visible_eq := F.jointForget_eq_iff.mpr memberVisible_eq
  authority_ne := authority_ne

/-- Every member restriction identifies the endpoints of a joint kernel
pair. -/
theorem jointKernelPair_memberVisible_eq
    (pair : AuthorityKernelPair F.jointAuthorityObserver)
    (member : F.Member) :
    F.forget member pair.left = F.forget member pair.right :=
  F.jointForget_eq_iff.mp pair.visible_eq member

/-- A joint authority-kernel pair is immediately an exact hidden-NULL
witness for the source authority consumer. -/
def jointKernelPairHiddenNullWitness
    (pair : AuthorityKernelPair F.jointAuthorityObserver) :
    HiddenNullWitness F.jointForget F.authorityK where
  left := pair.left
  right := pair.right
  sameObservation := pair.visible_eq
  differentDisposition := pair.authority_ne

/-- The canonical consumer-kernel classification generated by a joint
authority-kernel pair. -/
def jointKernelPairConsumerStatus
    (pair : AuthorityKernelPair F.jointAuthorityObserver) :
    ConsumerKernelStatus F.jointForget F.authorityK :=
  .hidden (F.jointKernelPairHiddenNullWitness pair)

theorem jointKernelPair_not_consumerSafe
    (pair : AuthorityKernelPair F.jointAuthorityObserver) :
    ¬ ConsumerSafe F.jointForget F.authorityK :=
  (F.jointKernelPairHiddenNullWitness pair).not_consumerSafe

theorem jointKernelPairConsumerStatus_not_certifiedSafe
    (pair : AuthorityKernelPair F.jointAuthorityObserver) :
    ¬ (F.jointKernelPairConsumerStatus pair).IsCertifiedSafe :=
  ConsumerKernelStatus.hidden_not_certifiedSafe
    (F.jointKernelPairHiddenNullWitness pair)

end CommonAuthorityObserverFamily
end SharedKernel
end Beauty
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel.CommonAuthorityObserverFamily.jointForget_eq_iff
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel.CommonAuthorityObserverFamily.memberForget_consumerSafe
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel.CommonAuthorityObserverFamily.jointKernelPairHiddenNullWitness
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.SharedKernel.CommonAuthorityObserverFamily.jointKernelPairConsumerStatus_not_certifiedSafe
