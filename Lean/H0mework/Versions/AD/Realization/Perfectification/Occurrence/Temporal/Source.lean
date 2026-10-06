import H0mework.Versions.R2.Foundation.Runtime.Activation
/-! Finite visits and source cofinal landings already have low carriers.
Their exact original recursive history is retained here without the
temporal wrapper universe; decoding recovers every source constructor. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLedgerRootClosure N V)
inductive PostAt (root : SourceNativeLedgerRootClosure N V) : V.Current → Type u
  | cofinal (visit : SourceNativeCofinalVisitAt root) : PostAt root visit.current
  | step {current next : V.Current} (prior : PostAt root current)
      (next_eq : (root.toRoot.evolutionAt current).nextCurrent? = some next) : PostAt root next
namespace PostAt
def encode {current : V.Current} : SourceNativePostCofinalReachableAt root current → PostAt root current
  | .cofinal visit => .cofinal visit
  | .step prior next_eq => .step (encode prior) next_eq
def decode {current : V.Current} : PostAt root current → SourceNativePostCofinalReachableAt root current
  | .cofinal visit => .cofinal visit
  | .step prior next_eq => .step (decode prior) next_eq
theorem decode_encode {current : V.Current} (past : SourceNativePostCofinalReachableAt root current) :
    decode root (encode root past) = past := by
  induction past with
  | cofinal visit => rfl
  | step prior next_eq ih => exact congrArg (fun previous => SourceNativePostCofinalReachableAt.step previous next_eq) ih
theorem encode_decode {current : V.Current} (past : PostAt root current) :
    encode root (decode root past) = past := by
  induction past with
  | cofinal visit => rfl
  | step prior next_eq ih => exact congrArg (fun previous => PostAt.step previous next_eq) ih
end PostAt
inductive HistoryAt (root : SourceNativeLedgerRootClosure N V) : V.Current → Type u
  | finite {current : V.Current} (history : root.toRoot.ReachableAt current) : HistoryAt root current
  | postCofinal {current : V.Current} (history : PostAt root current) : HistoryAt root current
namespace HistoryAt
def encode {current : V.Current} : SourceNativeTemporalReachableAt root current → HistoryAt root current
  | .finite past => .finite past
  | .postCofinal past => .postCofinal (PostAt.encode root past)
def decode {current : V.Current} : HistoryAt root current → SourceNativeTemporalReachableAt root current
  | .finite past => .finite past
  | .postCofinal past => .postCofinal (PostAt.decode root past)
theorem decode_encode {current : V.Current} (past : SourceNativeTemporalReachableAt root current) :
    decode root (encode root past) = past := by
  cases past with
  | finite past => rfl
  | postCofinal past => exact congrArg SourceNativeTemporalReachableAt.postCofinal (PostAt.decode_encode root past)
theorem encode_decode {current : V.Current} (past : HistoryAt root current) :
    encode root (decode root past) = past := by
  cases past with
  | finite past => rfl
  | postCofinal past => exact congrArg HistoryAt.postCofinal (PostAt.encode_decode root past)
end HistoryAt
structure Code (root : SourceNativeLedgerRootClosure N V) : Type u where
  current : V.Current
  history : HistoryAt root current
def encode (visit : SourceNativeTemporalVisitAt root) : Code root :=
  ⟨visit.current, HistoryAt.encode root visit.history⟩
def decode (code : Code root) : SourceNativeTemporalVisitAt root :=
  ⟨code.current, HistoryAt.decode root code.history⟩
theorem decode_encode (visit : SourceNativeTemporalVisitAt root) : decode root (encode root visit) = visit := by
  cases visit with
  | mk current history => exact congrArg (SourceNativeTemporalVisitAt.mk current) (HistoryAt.decode_encode root history)
theorem encode_decode (code : Code root) : encode root (decode root code) = code := by
  cases code with
  | mk current history => exact congrArg (Code.mk current) (HistoryAt.encode_decode root history)
theorem encode_injective : Function.Injective (encode root) := by
  intro first second same
  exact (decode_encode root first).symm.trans ((congrArg (decode root) same).trans (decode_encode root second))

def next {target : V.Current} (code : Code root)
    (next_eq : (root.toRoot.evolutionAt code.current).nextCurrent? = some target) : Code root :=
  encode root ((decode root code).next next_eq)

theorem decode_next {target : V.Current} (code : Code root)
    (next_eq : (root.toRoot.evolutionAt code.current).nextCurrent? = some target) :
    decode root (next root code next_eq) = (decode root code).next next_eq :=
  decode_encode root _

theorem encode_next {target : V.Current} (visit : SourceNativeTemporalVisitAt root)
    (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some target) :
    next root (encode root visit) next_eq = encode root (visit.next next_eq) := by
  cases visit with
  | mk current history =>
      exact congrArg (fun past : SourceNativeTemporalReachableAt root current =>
        Code.mk target (HistoryAt.encode root (past.next next_eq)))
        (HistoryAt.decode_encode root history)
end SourceTemporalMaterial
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
