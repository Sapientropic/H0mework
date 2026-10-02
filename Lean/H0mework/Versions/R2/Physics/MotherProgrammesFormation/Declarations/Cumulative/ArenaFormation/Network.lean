import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.Higher
import H0mework.Foundation.Source.RelationNetwork

/-! The existing complete relation-network graph constructor instantiated on
rank-formed mother-law material. Its only data input remains one material;
the rank parameter fixes the source construction schema. This scratch
instance keeps the signed fixed-base implementation unchanged. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetwork

open ResponsibilityLifecycle.LivingLawEvolution
open scoped Classical
noncomputable section

variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

-- Stream coordinates are fixed schema tags; pair is the original source operation.
def bit (m : M) (tag : Nat) (x : B) : Prop :=
  (MotherArenaHigher.read rank) m x tag = 0

def r2 (m : M) (tag : Nat) (x y : B) : Prop :=
  bit m tag ((MotherArenaHigher.pair rank) (x, y))

def r3 (m : M) (tag : Nat) (x y z : B) : Prop :=
  bit m tag ((MotherArenaHigher.pair rank)
    (x, (MotherArenaHigher.pair rank) (y, z)))

def r4 (m : M) (tag : Nat) (x y z w : B) : Prop :=
  bit m tag ((MotherArenaHigher.pair rank)
    (x, (MotherArenaHigher.pair rank) (y, (MotherArenaHigher.pair rank) (z, w))))

abbrev Support (m : M) := {x : B // bit m 0 x}
abbrev Anchor (m : M) := {x : B // bit m 1 x}
abbrev Incidence (m : M) := {x : B // bit m 2 x}
abbrev Lineage (m : M) := {x : B // bit m 3 x}
abbrev Responsibility (m : M) := {x : B // bit m 4 x}
abbrev Claim (m : M) := {x : B // bit m 5 x}

-- Distinct witnesses remain distinct values even at the same incidence.
abbrev OpenAt (m : M) (s : Support m) (r : Responsibility m) :=
  {w : B // r3 m 6 s.val r.val w}
abbrev HoldsAt (m : M) (s : Support m) (c : Claim m) :=
  {w : B // r3 m 7 s.val c.val w}
abbrev ObstructionAt (m : M) (s : Support m) :=
  {w : B // r2 m 8 s.val w}
abbrev SemanticChangeAt (m : M) (s : Support m) (c d : Claim m) :=
  {w : B // r4 m 9 s.val c.val d.val w}

def dispositionTag : WorldDispositionKind → Nat
  | .transfer => 10
  | .supportSettlement => 11
  | .lawSurfaceExtension => 12

abbrev DispositionAt (m : M) (s : Support m) (k : WorldDispositionKind) :=
  {w : B // r2 m (dispositionTag k) s.val w}

-- These are private assembly obligations, not caller input to the public factory.
structure Check (m : M) : Prop where
  anchor : ∀ s : Support m, ∃! a : Anchor m, r2 m 13 s.val a.val
  incidence : ∀ s : Support m, ∃! a : Incidence m, r2 m 14 s.val a.val
  lineage : ∀ s : Support m, ∃! a : Lineage m, r2 m 15 s.val a.val
  openClaim : ∀ (s : Support m) (r : Responsibility m) (w : OpenAt m s r),
    ∃! c : Claim m, r4 m 16 s.val r.val w.val c.val
  obstructionClaim : ∀ (s : Support m) (w : ObstructionAt m s),
    ∃! c : Claim m, r3 m 17 s.val w.val c.val

private def uniqueOutput {Y : Type} {p : Y → Prop} (h : ∃! y, p y) : Y :=
  Classical.choose h

private theorem uniqueOutput_spec {Y : Type} {p : Y → Prop}
    (h : ∃! y, p y) : p (uniqueOutput h) :=
  (Classical.choose_spec h).1

/-- The budget is actual source numeric data, not an imposed zero default. -/
def budget (m : M) (s : Support m) (r : Responsibility m) (w : OpenAt m s r) : Nat :=
  Nat.floor ((MotherArenaHigher.read rank) m
    ((MotherArenaHigher.pair rank)
      (s.val, (MotherArenaHigher.pair rank) (r.val, w.val))) 18)

private def assemble (m : M) (h : Check m) : WorldRelationNetwork.{0} where
  Support := Support m
  Anchor := Anchor m
  Incidence := Incidence m
  Lineage := Lineage m
  Responsibility := Responsibility m
  Claim := Claim m
  anchorAt := fun s => uniqueOutput (h.anchor s)
  incidenceAt := fun s => uniqueOutput (h.incidence s)
  lineageAt := fun s => uniqueOutput (h.lineage s)
  OpenAt := OpenAt m
  openClaimAt := fun {s} {r} w => uniqueOutput (h.openClaim s r w)
  openProgressBudgetAt := fun {s} {r} w => budget m s r w
  HoldsAt := HoldsAt m
  ObstructionAt := ObstructionAt m
  obstructionClaim := fun {s} w => uniqueOutput (h.obstructionClaim s w)
  SemanticChangeAt := SemanticChangeAt m
  DispositionAt := DispositionAt m

/-- One already formed mother law is the entire input. -/
def formNetwork (m : M) : Option WorldRelationNetwork.{0} :=
  if h : Check m then some (assemble m h) else none

theorem formNetwork_success (m : M) (h : Check m) :
    formNetwork m = some (assemble m h) := by
  simp only [formNetwork, dif_pos h]

theorem formNetwork_failure (m : M) (h : ¬ Check m) : formNetwork m = none := by
  simp only [formNetwork, dif_neg h]

/-- The actual selected claim has the exact stored graph edge. -/
theorem assembled_openClaim_graph (m : M) (h : Check m)
    (s : Support m) (r : Responsibility m) (w : OpenAt m s r) :
    r4 m 16 s.val r.val w.val ((assemble m h).openClaimAt w).val :=
  uniqueOutput_spec (h.openClaim s r w)

/-- A standalone complete Type-valued family decoder using another fixed slot.
It is a producer on source materials, not an arbitrary supplied F. -/
def Family (m : M) (index : B) : Type :=
  {w : B // r2 m 19 index w}

def formFamilyMember (m : M) (index address : B) : Option (Family m index) :=
  if h : r2 m 19 index address then some ⟨address, h⟩ else none

theorem every_family_member (m : M) (index : B) (w : Family m index) :
    formFamilyMember m index w.val = some w := by
  simp only [formFamilyMember, dif_pos w.property]
  rfl

/-- Coverage-side relation formation, using only the actual M reader. -/
theorem every_binary_graph (tag : Nat) (R : B → B → Prop) :
    ∃ m : M, ∀ x y, r2 m tag x y ↔ R x y := by
  obtain ⟨m, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (fun code _ => if R ((MotherArenaHigher.unpair rank) code).1
      ((MotherArenaHigher.unpair rank) code).2 then 0 else 1)
  refine ⟨m, fun x y => ?_⟩
  by_cases h : R x y <;>
    simp [r2, bit, hm, (MotherArenaHigher.unpair_pair rank), h]

/-- ONE material reconstructs EVERY fibre, including all witness values.
F and its embedding occur only in this coverage theorem, never in Family. -/
theorem every_embedded_dependent_family (F : B → Type)
    (encode : (Sigma F) ↪ B) :
    ∃ m : M, ∀ index : B,
      ∃ e : F index ≃ Family m index,
        ∀ w : F index, (e w).val = encode ⟨index, w⟩ := by
  obtain ⟨m, hm⟩ := every_binary_graph 19
    (fun index address => ∃ w : F index, encode ⟨index, w⟩ = address)
  refine ⟨m, fun index => ?_⟩
  let f : F index → Family m index := fun w =>
    ⟨encode ⟨index, w⟩, (hm index _).mpr ⟨w, rfl⟩⟩
  have inj : Function.Injective f := by
    intro x y hxy
    have h : (⟨index, x⟩ : Sigma F) = ⟨index, y⟩ :=
      encode.injective (congrArg Subtype.val hxy)
    exact (Function.Embedding.sigmaMk (β := F) index).injective h
  have surj : Function.Surjective f := by
    intro w
    obtain ⟨v, hv⟩ := (hm index w.val).mp w.property
    exact ⟨v, Subtype.ext hv⟩
  exact ⟨Equiv.ofBijective f ⟨inj, surj⟩, fun _ => rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaNetwork
