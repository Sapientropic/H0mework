import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryClosure

/-! Read the two original registered native writes as the same six-row
compiler images used by the continuation. The boundary equality carries
every old live entry into the next actual compiler image. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentReentryLedger

open ContentReentryIO ContentReentryRoot

variable {source : ContentReentryIO.Source}

structure PriorAt (source : ContentReentryIO.Source) where
  private mk ::
  first : GeneratedAt source source.born
  second : GeneratedAt source first.next
  boundary : second.next = source.initial

/-- The paths and the old metadata are fixed by the original source's
registration. A caller supplies neither an old ledger nor a target. -/
def loadPrior (source : ContentReentryIO.Source) : IO (PriorAt source) := do
  guard source.material
  let first ← ContentReentryRoot.readRegistered source source.born
  let second ← ContentReentryRoot.readRegistered source first.next
  if boundary : capture second.next = capture source.initial then
    return ⟨first, second, capture_injective boundary⟩
  else throw (IO.userError "the original whole-ledger destination is not this implementation's complete initial current")

def boundaryEntry (prior : PriorAt source) (responsibility : Responsibility) :
    OpenResponsibilityAt (network source) source.initial :=
  prior.boundary ▸
    (prior.second.patch.toLedgerWriteEvolution.destination
      (prior.first.patch.toLedgerWriteEvolution.destination
        (ContentReentryRoot.entry source source.born responsibility)).1).1

private theorem entry_transport {before after : Current source.material}
    (same : before = after) (responsibility : Responsibility) :
    (same ▸ ContentReentryRoot.entry source before responsibility) =
      ContentReentryRoot.entry source after responsibility := by
  cases same
  rfl

theorem boundary_entry_exact (prior : PriorAt source) (responsibility : Responsibility) :
    boundaryEntry prior responsibility = ContentReentryRoot.entry source source.initial responsibility := by
  unfold boundaryEntry
  rw [actual_six_rows]
  rw [actual_six_rows]
  exact entry_transport prior.boundary responsibility

def continuedEntry (prior : PriorAt source) (generated : GeneratedAt source source.initial)
    (responsibility : Responsibility) : OpenResponsibilityAt (network source) generated.next :=
  (generated.patch.toLedgerWriteEvolution.destination (boundaryEntry prior responsibility)).1

theorem all_old_destinations_continue (prior : PriorAt source)
    (generated : GeneratedAt source source.initial) (responsibility : Responsibility) :
    continuedEntry prior generated responsibility = ContentReentryRoot.entry source generated.next responsibility := by
  unfold continuedEntry
  rw [boundary_entry_exact]
  exact actual_six_rows source generated responsibility

def firstOrigin (prior : PriorAt source) (responsibility : Responsibility) :
    OpenResponsibilityAt (network source) source.born :=
  (prior.first.patch.toLedgerWriteEvolution.origin
    (prior.second.patch.toLedgerWriteEvolution.origin
      (ContentReentryRoot.entry source prior.second.next responsibility)).1).1

theorem all_old_origins_retained (prior : PriorAt source) (responsibility : Responsibility) :
    firstOrigin prior responsibility = ContentReentryRoot.entry source source.born responsibility := rfl

theorem new_origin_is_old_boundary (prior : PriorAt source)
    (generated : GeneratedAt source source.initial) (responsibility : Responsibility) :
    (generated.patch.toLedgerWriteEvolution.origin
      (ContentReentryRoot.entry source generated.next responsibility)).1 = boundaryEntry prior responsibility := by
  rw [boundary_entry_exact]
  rfl

theorem original_anchor_lineage_and_incidence (prior : PriorAt source)
    (generated : GeneratedAt source source.initial) :
    (network source).anchorAt prior.second.next = (network source).anchorAt generated.next ∧
    (network source).lineageAt prior.second.next = (network source).lineageAt generated.next ∧
    (network source).incidenceAt prior.second.next = ContentReentryIO.boundaryVisit ∧
    (network source).incidenceAt generated.next = ContentReentryIO.boundaryVisit + 1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change prior.second.next.visit = ContentReentryIO.boundaryVisit
    rw [prior.boundary]
    exact source.initial_visit
  · change generated.next.visit = ContentReentryIO.boundaryVisit + 1
    change generated.reply.after.visit = ContentReentryIO.boundaryVisit + 1
    rw [generated.reply.next_visit, source.initial_visit]

end ContentReentryLedger
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
