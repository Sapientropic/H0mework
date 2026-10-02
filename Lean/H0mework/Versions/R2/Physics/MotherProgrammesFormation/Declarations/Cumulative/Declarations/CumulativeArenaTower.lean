import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.GraphBuildBridge
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Rank
import Mathlib.Logic.Small.Basic

/-!
Graph-seeded full-prefix completion and rank-indexed set coverage.

A full-prefix variant of the proposed ordinal feedback tower. The initial
arena is the original M-graph arena. Each layer stores an original Build
readout as well as its source-address carrier and set value. Every new raw
carrier is the image of List of the actual preceding native addresses.

Ordinal is an index of a newly proposed transfinite formation schema, NOT
an original MotherVisit or an emitted physical time. This file supplies no
runtime installation, U8 trigger, or universal process-coverage theorem.
The source provenance of the transfinite schema must be audited with its
per-prefix installation, not inferred from kernel acceptance alone.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCumulativeArena

open MotherSmallSupport UniformSpace
open scoped Classical Topology
noncomputable section

abbrev W := ZFSet.{0}

/-- Internal recursive data, not an input accepted by the public tower. -/
structure Arena : Type 1 where
  Key : Type
  value : Key → W
  build : (k : Key) → ParentCompletion.Build (value k)

private def seed : Arena where
  Key := MotherGraphArenaTrial.Key
  value := MotherGraphArenaTrial.value
  build := fun k => MotherGraphBuildBridge.buildGraph k.1 k.2

private def parents (A : Arena) : Set W := Set.range A.value
private def packetSupport (A : Arena) (p : List A.Key) : Finset W :=
  (p.map A.value).toFinset
private def packetRead (A : Arena) (p : List A.Key) : W → ℝ :=
  finiteProfile (packetSupport A p)
private abbrev Raw (A : Arena) := Set.range (packetRead A)

private theorem packet_inside (A : Arena) (p : List A.Key) :
    (↑(packetSupport A p) : Set W) ⊆ parents A := by
  intro x hx
  obtain ⟨k, _, hk⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact ⟨k, hk⟩

private def fromPacket (A : Arena) (p : List A.Key) : Raw A :=
  ⟨packetRead A p, p, rfl⟩

private theorem raw_programme_surjective (A : Arena) :
    Function.Surjective (fromPacket A) := by
  rintro ⟨f, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

private instance rawSmall (A : Arena) : Small.{0} (Raw A) :=
  small_of_surjective (raw_programme_surjective A)

private theorem relative_raw_has_programme (A : Arena) (r : MotherSmallSupport.Raw (parents A)) :
    ∃ p : List A.Key, packetRead A p = r.val := by
  obtain ⟨F, hF, hread⟩ := r.property
  let address (x : F) : A.Key := Classical.choose (hF x.property)
  have address_value (x : F) : A.value (address x) = x.val :=
    Classical.choose_spec (hF x.property)
  let p := F.attach.toList.map address
  have support_eq : packetSupport A p = F := by
    ext x
    simp only [packetSupport, p, List.map_map, List.mem_toFinset, List.mem_map,
      Finset.mem_toList, Function.comp_apply, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨v, hv⟩
      rw [address_value] at hv
      exact hv ▸ v.property
    · intro hx
      exact ⟨⟨x, hx⟩, address_value ⟨x, hx⟩⟩
  exact ⟨p, (congrArg finiteProfile support_eq).trans hread⟩

private def rawEquiv (A : Arena) : Raw A ≃ᵤ MotherSmallSupport.Raw (parents A) where
  toFun := fun r => ⟨r.val, by
    obtain ⟨p, hp⟩ := r.property
    exact ⟨packetSupport A p, packet_inside A p, hp⟩⟩
  invFun := fun r => ⟨r.val, relative_raw_has_programme A r⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _

private abbrev NativeRaw (A : Arena) : Type := Shrink (Raw A)
private instance nativeUniform (A : Arena) : UniformSpace (NativeRaw A) :=
  UniformSpace.comap (equivShrink (Raw A)).symm inferInstance
private def nativeRawEquiv (A : Arena) : NativeRaw A ≃ᵤ Raw A :=
  (equivShrink (Raw A)).symm.toUniformEquivOfIsUniformInducing ⟨rfl⟩
private abbrev Material (A : Arena) : Type := Completion (NativeRaw A)
private def completedEquiv (A : Arena) : Material A ≃ᵤ Formed (parents A) :=
  (Completion.mapEquiv (nativeRawEquiv A)).trans (Completion.mapEquiv (rawEquiv A))

private instance parentsSmall (A : Arena) : Small.{0} (parents A) := by
  apply small_of_surjective (f := fun k : A.Key =>
    (⟨A.value k, ⟨k, rfl⟩⟩ : parents A))
  rintro ⟨x, k, hk⟩
  exact ⟨k, Subtype.ext hk⟩

private theorem selectedSmall (A : Arena) (m : Material A) :
    Small.{0} (selected (parents A) (completedEquiv A m)) := by
  let f : selected (parents A) (completedEquiv A m) → parents A :=
    fun x => ⟨x.val, by
      by_contra absent
      exact no_new_one (parents A) x.val absent (completedEquiv A m) x.property⟩
  exact small_of_injective (f := f) (fun x y same =>
    Subtype.ext (congrArg (fun value : parents A => value.val) same))

private def collected (A : Arena) (m : Material A) : W :=
  collect (parents A) (completedEquiv A m) (selectedSmall A m)

private theorem collected_forms (A : Arena) (m : Material A) :
    formSmall (parents A) (completedEquiv A m) = some (collected A m) :=
  formSmall_recovers (parents A) (completedEquiv A m) (selectedSmall A m)

private def originalMaterial (A : Arena) (m : Material A) : ParentCompletion.Material :=
  includeCompleted (Set.subset_univ (parents A)) (completedEquiv A m)

private theorem original_forms (A : Arena) (m : Material A) :
    formSmall Set.univ (originalMaterial A m) = some (collected A m) :=
  (MotherGraphBuildBridge.formSmall_include_univ (completedEquiv A m)).trans
    (collected_forms A m)

private def newBuild (A : Arena) (m : Material A) : ParentCompletion.Build (collected A m) :=
  ParentCompletion.Build.completed (originalMaterial A m) (original_forms A m)
    (fun x hx =>
      let inside : x ∈ parents A :=
        collect_uses_only_parents (parents A) (completedEquiv A m) (selectedSmall A m) hx
      let k := Classical.choose inside
      Eq.mp (congrArg ParentCompletion.Build (Classical.choose_spec inside)) (A.build k))

/-- This constructor takes only the internally constructed previous arena. -/
private def feedback (A : Arena) : Arena where
  Key := A.Key ⊕ Material A
  value := Sum.elim A.value (collected A)
  build := fun k => match k with
    | .inl old => A.build old
    | .inr m => newBuild A m

private theorem every_supported_value (A : Arena) (x : W)
    (supported : (x : Set W) ⊆ parents A) :
    ∃ m : Material A, collected A m = x := by
  obtain ⟨relative, _, hrelative⟩ := every_supported_set (parents A) x supported
  let m := (completedEquiv A).symm relative
  have h : formSmall (parents A) (completedEquiv A m) = some x := by
    simpa only [m, UniformEquiv.apply_symm_apply] using hrelative
  exact ⟨m, Option.some.inj ((collected_forms A m).symm.trans h)⟩

private abbrev Past (α : Ordinal.{0}) (earlier : ∀ β, β < α → Arena) :=
  seed.Key ⊕ (Σ β : Set.Iio α, (earlier β.val β.property).Key)

private def pastValue (α : Ordinal.{0}) (earlier : ∀ β, β < α → Arena) :
    Past α earlier → W
  | .inl k => seed.value k
  | .inr ⟨β, k⟩ => (earlier β.val β.property).value k

private def pastBuild (α : Ordinal.{0}) (earlier : ∀ β, β < α → Arena) :
    (k : Past α earlier) → ParentCompletion.Build (pastValue α earlier k)
  | .inl k => seed.build k
  | .inr ⟨β, k⟩ => (earlier β.val β.property).build k

/-- Ordinal.small_Iio pays local size. No future layer occurs here. -/
private def pastArena (α : Ordinal.{0}) (earlier : ∀ β, β < α → Arena) : Arena where
  Key := Shrink.{0} (Past α earlier)
  value := fun k => pastValue α earlier ((equivShrink (Past α earlier)).symm k)
  build := fun k => pastBuild α earlier ((equivShrink (Past α earlier)).symm k)

/-- The proposed public transfinite producer has no P/Type/decoder input. -/
def tower : Ordinal.{0} → Arena :=
  Ordinal.lt_wf.fix fun α earlier => feedback (pastArena α earlier)

private theorem tower_eq (α : Ordinal.{0}) :
    tower α = feedback (pastArena α (fun β _ => tower β)) :=
  WellFounded.fix_eq Ordinal.lt_wf (fun α earlier => feedback (pastArena α earlier)) α

abbrev Stage (α : Ordinal.{0}) : Type := (tower α).Key
def stageValue (α : Ordinal.{0}) : Stage α → W := (tower α).value
def stageBuild (α : Ordinal.{0}) (k : Stage α) : ParentCompletion.Build (stageValue α k) :=
  (tower α).build k

private theorem prior_in_past {β α : Ordinal.{0}} (h : β < α) (k : Stage β) :
    stageValue β k ∈ parents (pastArena α (fun γ _ => tower γ)) := by
  let p : Past α (fun γ _ => tower γ) := .inr ⟨⟨β, h⟩, k⟩
  refine ⟨equivShrink (Past α (fun γ _ => tower γ)) p, ?_⟩
  change pastValue α (fun γ _ => tower γ)
    ((equivShrink (Past α (fun γ _ => tower γ))).symm
      (equivShrink (Past α (fun γ _ => tower γ)) p)) = stageValue β k
  rw [Equiv.symm_apply_apply]
  rfl

/-- Stronger than an unspecified cofinal stage: the target's rank suffices.
This theorem does not identify ordinal depth with physical runtime depth. -/
theorem covers_at_rank (x : W) :
    ∃ k : Stage x.rank, stageValue x.rank k = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have supported : (x : Set W) ⊆ parents (pastArena x.rank (fun β _ => tower β)) := by
      intro y hy
      obtain ⟨k, hk⟩ := ih y hy
      rw [← hk]
      exact prior_in_past (ZFSet.rank_lt_of_mem hy) k
    obtain ⟨m, hm⟩ := every_supported_value
      (pastArena x.rank (fun β _ => tower β)) x supported
    change ∃ k : (tower x.rank).Key, (tower x.rank).value k = x
    rw [tower_eq]
    exact ⟨.inr m, hm⟩

theorem covers (x : W) : ∃ α : Ordinal.{0}, ∃ k : Stage α, stageValue α k = x := by
  obtain ⟨k, hk⟩ := covers_at_rank x
  exact ⟨x.rank, k, hk⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCumulativeArena
