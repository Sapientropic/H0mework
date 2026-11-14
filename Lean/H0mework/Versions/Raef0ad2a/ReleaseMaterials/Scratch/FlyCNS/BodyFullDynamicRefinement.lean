import H0mework.Versions.Raef0ad2a.ReleaseMaterials.Scratch.FlyCNS.BodyFullPackedIO
import H0mework.Foundation.Relations.ConsumerQuotient

/-! Actual future escapes are observations of two completed branches of one
fixed source.  The added coordinates are read from their original residuals,
never from a desired future.  The executable carrier keeps the complete
packet, so refinement cannot discard an autonomous state coordinate. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace BodyFullDynamicRefinement

open BodyFullIO BodyFullPackedIO RepresentationIO
open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

inductive Coordinate (material : BodyFullIO.Material) where
  | word (address : Fin material.count)
  | backend (address : Fin 4)
  | header
  | visit
  deriving DecidableEq

inductive Datum where
  | word (bytes : ByteArray) (dataStart width count : Nat)
  | bytes (value : ByteArray)
  | visit (value : Nat)
  deriving DecidableEq

def coordinateRead {material : BodyFullIO.Material}
    (coordinate : Coordinate material) (image : Image material) : Datum :=
  match coordinate with
  | .word address =>
      let word := image.words.get address
      .word word.bytes word.dataStart word.width word.count
  | .backend address => .bytes (image.backend.get address)
  | .header => .bytes image.header
  | .visit => .visit image.visit

/-- The raw state basis precedes comparison.  Backends and literal headers
remain in the residual; they are not silently regenerated from this basis. -/
def sourceBasis (material : BodyFullIO.Material) : List (Coordinate material) :=
  (List.finRange material.count).map Coordinate.word ++ [.visit]

def completeCoordinates (material : BodyFullIO.Material) : List (Coordinate material) :=
  (List.finRange material.count).map Coordinate.word ++
    (List.finRange 4).map Coordinate.backend ++ [.header, .visit]

def gateOmittingPlan (material : BodyFullIO.Material) : List (Coordinate material) :=
  ((List.finRange material.count).filter fun address =>
    address != material.addresses.get ⟨35, by decide⟩).map Coordinate.word

def view {material : BodyFullIO.Material} (plan : List (Coordinate material))
    (image : Image material) : List Datum := plan.map fun coordinate => coordinateRead coordinate image

def viewConsumers {material : BodyFullIO.Material} (plan : List (Coordinate material)) :
    IndependentConsumerSystem (Image material) where
  Consumer := PUnit
  Output := fun _ => List Datum
  read := fun _ => view plan
  positive := ⟨PUnit.unit⟩

theorem view_kernel_exact {material : BodyFullIO.Material} (plan : List (Coordinate material)) :
    FaceKernelExactAt (viewConsumers plan) (view plan) := by
  intro left right
  constructor
  · intro equal consumer
    exact equal
  · intro equal
    exact equal PUnit.unit

def sourceCoordinateReadout {material : BodyFullIO.Material} (coordinate : Coordinate material) :
    IndependentReadout (Image material) := ⟨Datum, coordinateRead coordinate⟩

theorem adjoined_source_coordinate_exact {material : BodyFullIO.Material}
    (plan : List (Coordinate material)) (coordinate : Coordinate material) :
    FaceKernelExactAt ((viewConsumers plan).adjoin (sourceCoordinateReadout coordinate))
      (refinedFace (view plan) (sourceCoordinateReadout coordinate)) :=
  (view_kernel_exact plan).adjoin_refinedFace

theorem source_coordinate_adjoin_does_not_merge {material : BodyFullIO.Material}
    (plan : List (Coordinate material)) (coordinate : Coordinate material)
    (left right : Image material)
    (different : coordinateRead coordinate left ≠ coordinateRead coordinate right) :
    refinedFace (view plan) (sourceCoordinateReadout coordinate) left ≠
      refinedFace (view plan) (sourceCoordinateReadout coordinate) right := by
  intro same
  exact different (congrArg Prod.snd same)

theorem view_append_old {material : BodyFullIO.Material}
    (old added : List (Coordinate material)) (image : Image material) :
    (view (old ++ added) image).take old.length = view old image := by
  simp [view]

theorem refined_preserves_old_kernel {material : BodyFullIO.Material}
    (old added : List (Coordinate material)) (left right : Image material)
    (same : view (old ++ added) left = view (old ++ added) right) :
    view old left = view old right := by
  have previous := congrArg (List.take old.length) same
  simpa only [view_append_old] using previous

structure OriginAt {material : BodyFullIO.Material} (plan : List (Coordinate material))
    (left right : Image material) where
  coordinate : Coordinate material
  source_member : coordinate ∈ sourceBasis material
  absent : coordinate ∉ plan
  different : coordinateRead coordinate left ≠ coordinateRead coordinate right

/-- A finite search reads literal source state.  Neither future output nor a
decoder/factorization witness is supplied to this producer. -/
def findOrigin {material : BodyFullIO.Material} (plan : List (Coordinate material))
    (left right : Image material) :
    (candidates : List (Coordinate material)) →
    (∀ coordinate ∈ candidates, coordinate ∈ sourceBasis material) →
    Option (OriginAt plan left right)
  | [], _ => none
  | coordinate :: rest, members =>
      if absent : coordinate ∉ plan then
        if different : coordinateRead coordinate left ≠ coordinateRead coordinate right then
          some ⟨coordinate, members coordinate (by simp), absent, different⟩
        else findOrigin plan left right rest (fun value member => members value (by simp [member]))
      else findOrigin plan left right rest (fun value member => members value (by simp [member]))

def separationCoordinates {material : BodyFullIO.Material}
    (plan : List (Coordinate material)) (left right : Image material) : List (Coordinate material) :=
  (sourceBasis material).filter fun coordinate =>
    decide (coordinate ∉ plan ∧ coordinateRead coordinate left ≠ coordinateRead coordinate right)

theorem origin_mem_separation {material : BodyFullIO.Material}
    {plan : List (Coordinate material)} {left right : Image material}
    (origin : OriginAt plan left right) : origin.coordinate ∈ separationCoordinates plan left right := by
  simp only [separationCoordinates, List.mem_filter, decide_eq_true_eq]
  exact ⟨origin.source_member, origin.absent, origin.different⟩

variable (root : BodyFullIO.IORoot)

/-- This dependent carrier is produced only after actual completed source
updates.  It is not a table stored in the primitive source or its initial state. -/
abbrev Branch := (current : BodyFullIO.Current root.fixedSource.material) ×
  BodyFullIO.GeneratedAt root.fixedSource current

def beforeView (plan : List (Coordinate root.fixedSource.material)) (branch : Branch root) : List Datum :=
  view plan (capture branch.1)

def futureView (plan : List (Coordinate root.fixedSource.material)) : IndependentReadout (Branch root) :=
  ⟨List Datum, fun branch => view plan (capture branch.2.next)⟩

structure EscapeAt (plan : List (Coordinate root.fixedSource.material))
    (left right : Branch root) where
  private mk ::
  old_same : beforeView root plan left = beforeView root plan right
  future_different : (futureView root plan).read left ≠ (futureView root plan).read right
  origin : OriginAt plan (capture left.1) (capture right.1)

/-- Both futures are already born through the same fixed root.  Runtime
comparisons generate the escape certificate and its original-state direction. -/
def detectEscape (plan : List (Coordinate root.fixedSource.material))
    (left right : Branch root) : Option (EscapeAt root plan left right) :=
  if oldSame : beforeView root plan left = beforeView root plan right then
    if futureDifferent : view plan (capture left.2.next) ≠ view plan (capture right.2.next) then
      match findOrigin plan (capture left.1) (capture right.1)
          (sourceBasis root.fixedSource.material) (fun _ member => member) with
      | none => none
      | some origin => some ⟨oldSame, futureDifferent, origin⟩
    else none
  else none

theorem actual_future_escape {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right) :
    FaceKernelEscapeAt (beforeView root plan) (futureView root plan) :=
  ⟨left, right, escape.old_same, escape.future_different⟩

theorem actual_future_cannot_factor {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right) :
    ¬ Function.FactorsThrough (futureView root plan).read (beforeView root plan) :=
  (actual_future_escape root escape).not_factorsThrough

def EscapeAt.nextPlan {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (_escape : EscapeAt root plan left right) :
    List (Coordinate root.fixedSource.material) :=
  plan ++ separationCoordinates plan (capture left.1) (capture right.1)

theorem escape_nextPlan_separates {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right) :
    view escape.nextPlan (capture left.1) ≠ view escape.nextPlan (capture right.1) := by
  intro same
  have mapped := List.map_inj_left.mp same
  exact escape.origin.different (mapped escape.origin.coordinate (by
    apply List.mem_append.mpr
    exact .inr (origin_mem_separation escape.origin)))

theorem escape_preserves_old_view {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right)
    (image : Image root.fixedSource.material) :
    (view escape.nextPlan image).take plan.length = view plan image :=
  view_append_old plan _ image

/-- Materialized executable representation: coordinate inventory plus exact
remaining packet.  No original Current, function or future table is stored. -/
structure Representation where
  plan : List (Coordinate root.fixedSource.material)
  residual : Packet root.fixedSource.material

def Representation.image (representation : Representation root) : Image root.fixedSource.material :=
  unpack representation.residual

def Representation.observation (representation : Representation root) : List Datum :=
  view representation.plan representation.image

def represent (plan : List (Coordinate root.fixedSource.material))
    (current : BodyFullIO.Current root.fixedSource.material) : Representation root :=
  ⟨plan, packetCurrent current⟩

theorem representation_complete (plan : List (Coordinate root.fixedSource.material))
    (current : BodyFullIO.Current root.fixedSource.material) :
    (represent root plan current).image = capture current := unpack_packetCurrent current

def refineRepresentation {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right)
    (packet : Packet root.fixedSource.material) : Representation root :=
  ⟨escape.nextPlan, packet⟩

theorem refinement_keeps_complete_residual {plan : List (Coordinate root.fixedSource.material)}
    {left right : Branch root} (escape : EscapeAt root plan left right)
    (packet : Packet root.fixedSource.material) :
    (refineRepresentation root escape packet).image = unpack packet := rfl

structure StepAt (before : Representation root) where
  private mk ::
  actual : BodyFullPackedIO.StepAt root before.residual
  next : Representation root
  next_plan : next.plan = before.plan
  next_residual : next.residual = actual.next

def execute (before : Representation root) : IO (StepAt root before) := do
  let actual ← BodyFullPackedIO.executePacked root before.residual
  return ⟨actual, ⟨before.plan, actual.next⟩, rfl, rfl⟩

theorem execute_whole_current {before : Representation root} (step : StepAt root before) :
    step.next.image = capture step.actual.generated.next := by
  change unpack step.next.residual = _
  rw [step.next_residual]
  exact step.actual.next_image

theorem execute_source_support {before : Representation root} (step : StepAt root before) :
    capture step.actual.generated.occurrence.1 = before.image :=
  BodyFullPackedIO.step_support_exact root step.actual

theorem continuation_current {before : Representation root} (first : StepAt root before)
    (second : StepAt root first.next) :
    second.actual.decoded.current = first.actual.generated.next := by
  apply BodyFullPackedIO.capture_injective
  exact second.actual.decoded.image_eq.trans (execute_whole_current root first)

theorem continuation_every_reader {Output : Type}
    (reader : BodyFullIO.Current root.fixedSource.material → Output)
    {before : Representation root} (first : StepAt root before) (second : StepAt root first.next) :
    reader second.actual.decoded.current = reader first.actual.generated.next := by
  rw [continuation_current root first second]

set_option linter.defProp false in
def step_whole_ledger_next {before : Representation root} (step : StepAt root before) :=
  And.intro (execute_source_support root step)
    (And.intro (execute_whole_current root step)
      (BodyFullIO.actual_word_ledger_next root.fixedSource step.actual.generated))

/-- Any finite autonomous word still invokes the original source operation.
Its visit chooses neural/damage/repair; refinement never selects that letter. -/
inductive TraceAt : (initial : Representation root) → Nat → Type
  | done (before : Representation root) : TraceAt before 0
  | more {before : Representation root} {fuel : Nat}
      (step : StepAt root before) (rest : TraceAt step.next fuel) : TraceAt before (fuel + 1)

def TraceAt.final {before : Representation root} {fuel : Nat} :
    TraceAt root before fuel → Representation root
  | .done before => before
  | .more _ rest => rest.final

def TraceAt.packed {before : Representation root} {fuel : Nat} :
    TraceAt root before fuel → BodyFullPackedIO.TraceAt root before.residual fuel
  | .done before => .done before.residual
  | .more step rest => .more step.actual (step.next_residual ▸ rest.packed)

theorem packed_final_cast {left right : Packet root.fixedSource.material} {fuel : Nat}
    (same : left = right) (trace : BodyFullPackedIO.TraceAt root left fuel) :
    (same ▸ trace).final = trace.final := by
  cases same
  rfl

theorem finite_autonomous_words_exact {before : Representation root} {fuel : Nat}
    (trace : TraceAt root before fuel) :
    trace.final.residual = trace.packed.final := by
  induction trace with
  | done before => rfl
  | more step rest previous =>
      simpa only [TraceAt.final, TraceAt.packed, BodyFullPackedIO.TraceAt.final,
        packed_final_cast] using previous

def runAccounted : (fuel : Nat) → (before : Representation root) → IO (TraceAt root before fuel)
  | 0, before => pure (.done before)
  | fuel + 1, before => do
      let step ← execute root before
      let rest ← runAccounted fuel step.next
      return .more step rest

end BodyFullDynamicRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
