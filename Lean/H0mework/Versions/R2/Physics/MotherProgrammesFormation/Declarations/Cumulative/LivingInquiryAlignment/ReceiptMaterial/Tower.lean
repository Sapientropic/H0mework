import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.SetLift
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.ZFC.Rank
import Mathlib.Logic.Small.Basic

/-! Receipt-sized extension of the existing cumulative source.

The seed keeps every original graph key, its canonically included set value,
and the recursively preserved parent Build. Ordinals remain construction
indices, and the source below accepts no target receipt or process.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptArena

open MotherSmallSupport UniformSpace
open scoped Classical Topology
noncomputable section
universe u

abbrev W := ZFSet.{u}

/-- The original collector commutes with whole-material inclusion. -/
theorem formSmall_include_univ {D : Set W.{u}} (m : Formed D) :
    formSmall Set.univ (includeCompleted (Set.subset_univ D) m) =
      formSmall D m := by
  let j := includeCompleted (Set.subset_univ D) m
  have selected_eq : selected Set.univ j = selected D m := by
    ext x
    change read Set.univ j x = 1 ↔ read D m x = 1
    rw [show read Set.univ j = read D m from
      read_includeCompleted (Set.subset_univ D) m]
  change formSmall Set.univ j = formSmall D m
  by_cases rightSmall : Small.{u} (selected D m)
  · have leftSmall : Small.{u} (selected Set.univ j) := selected_eq.symm ▸ rightSmall
    simp only [formSmall, dif_pos leftSmall, dif_pos rightSmall]
    apply congrArg some
    ext x
    rw [mem_collect, mem_collect]
    exact Iff.of_eq (congrArg (fun r : ℝ => r = 1)
      (congrFun (read_includeCompleted (Set.subset_univ D) m) x))
  · have leftSmall : ¬ Small.{u} (selected Set.univ j) :=
      fun h => rightSmall (selected_eq ▸ h)
    simp only [formSmall, dif_neg leftSmall, dif_neg rightSmall]

/-- Internal recursive data, not an input accepted by the public tower. -/
structure Arena : Type (u + 1) where
  Key : Type u
  value : Key → W.{u}
  build : (k : Key) → ParentCompletion.Build (value k)

private def seed : Arena.{u} where
  Key := ULift.{u, 0} MotherGraphArenaTrial.Key
  value := fun k => MotherReceiptSetLift.liftSet (MotherGraphArenaTrial.value k.down)
  build := fun k => MotherReceiptSetLift.build (MotherGraphBuildBridge.buildGraph k.down.1 k.down.2)

private def parents (A : Arena.{u}) : Set W.{u} := Set.range A.value
private def packetSupport (A : Arena.{u}) (p : List A.Key) : Finset W.{u} :=
  (p.map A.value).toFinset
private def packetRead (A : Arena.{u}) (p : List A.Key) : W.{u} → ℝ :=
  finiteProfile (packetSupport A p)
private abbrev Raw (A : Arena.{u}) := Set.range (packetRead A)

private theorem packet_inside (A : Arena.{u}) (p : List A.Key) :
    (↑(packetSupport A p) : Set W.{u}) ⊆ parents A := by
  intro x hx
  obtain ⟨k, _, hk⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact ⟨k, hk⟩

private def fromPacket (A : Arena.{u}) (p : List A.Key) : Raw A :=
  ⟨packetRead A p, p, rfl⟩

private theorem raw_programme_surjective (A : Arena.{u}) :
    Function.Surjective (fromPacket A) := by
  rintro ⟨f, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

private instance rawSmall (A : Arena.{u}) : Small.{u} (Raw A) :=
  small_of_surjective (raw_programme_surjective A)

private theorem relative_raw_has_programme (A : Arena.{u}) (r : MotherSmallSupport.Raw (parents A)) :
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

private def rawEquiv (A : Arena.{u}) : Raw A ≃ᵤ MotherSmallSupport.Raw (parents A) where
  toFun := fun r => ⟨r.val, by
    obtain ⟨p, hp⟩ := r.property
    exact ⟨packetSupport A p, packet_inside A p, hp⟩⟩
  invFun := fun r => ⟨r.val, relative_raw_has_programme A r⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _

private abbrev NativeRaw (A : Arena.{u}) : Type u := Shrink (Raw A)
private instance nativeUniform (A : Arena.{u}) : UniformSpace (NativeRaw A) :=
  UniformSpace.comap (equivShrink (Raw A)).symm inferInstance
private def nativeRawEquiv (A : Arena.{u}) : NativeRaw A ≃ᵤ Raw A :=
  (equivShrink (Raw A)).symm.toUniformEquivOfIsUniformInducing ⟨rfl⟩
private abbrev Material (A : Arena.{u}) : Type u := Completion (NativeRaw A)
private def completedEquiv (A : Arena.{u}) : Material A ≃ᵤ Formed (parents A) :=
  (Completion.mapEquiv (nativeRawEquiv A)).trans (Completion.mapEquiv (rawEquiv A))

private instance parentsSmall (A : Arena.{u}) : Small.{u} (parents A) := by
  apply small_of_surjective (f := fun k : A.Key =>
    (⟨A.value k, ⟨k, rfl⟩⟩ : parents A))
  rintro ⟨x, k, hk⟩
  exact ⟨k, Subtype.ext hk⟩

private theorem selectedSmall (A : Arena.{u}) (m : Material A) :
    Small.{u} (selected (parents A) (completedEquiv A m)) := by
  let f : selected (parents A) (completedEquiv A m) → parents A :=
    fun x => ⟨x.val, by
      by_contra absent
      exact no_new_one (parents A) x.val absent (completedEquiv A m) x.property⟩
  exact small_of_injective (f := f) (fun x y same =>
    Subtype.ext (congrArg (fun value : parents A => value.val) same))

private def collected (A : Arena.{u}) (m : Material A) : W.{u} :=
  collect (parents A) (completedEquiv A m) (selectedSmall A m)

private theorem collected_forms (A : Arena.{u}) (m : Material A) :
    formSmall (parents A) (completedEquiv A m) = some (collected A m) :=
  formSmall_recovers (parents A) (completedEquiv A m) (selectedSmall A m)

private def originalMaterial (A : Arena.{u}) (m : Material A) : ParentCompletion.Material :=
  includeCompleted (Set.subset_univ (parents A)) (completedEquiv A m)

private theorem original_forms (A : Arena.{u}) (m : Material A) :
    formSmall Set.univ (originalMaterial A m) = some (collected A m) :=
  (formSmall_include_univ (completedEquiv A m)).trans
    (collected_forms A m)

private def newBuild (A : Arena.{u}) (m : Material A) : ParentCompletion.Build (collected A m) :=
  ParentCompletion.Build.completed (originalMaterial A m) (original_forms A m)
    (fun x hx =>
      let inside : x ∈ parents A :=
        collect_uses_only_parents (parents A) (completedEquiv A m) (selectedSmall A m) hx
      let k := Classical.choose inside
      Eq.mp (congrArg ParentCompletion.Build (Classical.choose_spec inside)) (A.build k))

/-- This constructor takes only the internally constructed previous arena. -/
private def feedback (A : Arena.{u}) : Arena.{u} where
  Key := A.Key ⊕ Material A
  value := Sum.elim A.value (collected A)
  build := fun k => match k with
    | .inl old => A.build old
    | .inr m => newBuild A m

private theorem every_supported_value (A : Arena.{u}) (x : W.{u})
    (supported : (x : Set W.{u}) ⊆ parents A) :
    ∃ m : Material A, collected A m = x := by
  obtain ⟨relative, _, hrelative⟩ := every_supported_set (parents A) x supported
  let m := (completedEquiv A).symm relative
  have h : formSmall (parents A) (completedEquiv A m) = some x := by
    simpa only [m, UniformEquiv.apply_symm_apply] using hrelative
  exact ⟨m, Option.some.inj ((collected_forms A m).symm.trans h)⟩

private abbrev Past (α : Ordinal.{u}) (earlier : ∀ β, β < α → Arena.{u}) :=
  seed.{u}.Key ⊕ (Σ β : Set.Iio α, (earlier β.val β.property).Key)

private def pastValue (α : Ordinal.{u}) (earlier : ∀ β, β < α → Arena.{u}) :
    Past α earlier → W.{u}
  | .inl k => seed.value k
  | .inr ⟨β, k⟩ => (earlier β.val β.property).value k

private def pastBuild (α : Ordinal.{u}) (earlier : ∀ β, β < α → Arena.{u}) :
    (k : Past α earlier) → ParentCompletion.Build (pastValue α earlier k)
  | .inl k => seed.build k
  | .inr ⟨β, k⟩ => (earlier β.val β.property).build k

/-- Ordinal.small_Iio pays local size. No future layer occurs here. -/
private def pastArena (α : Ordinal.{u}) (earlier : ∀ β, β < α → Arena.{u}) : Arena.{u} where
  Key := Shrink.{u} (Past α earlier)
  value := fun k => pastValue α earlier ((equivShrink (Past α earlier)).symm k)
  build := fun k => pastBuild α earlier ((equivShrink (Past α earlier)).symm k)

/-- The proposed public transfinite producer has no P/Type/decoder input. -/
def tower : Ordinal.{u} → Arena.{u} :=
  Ordinal.lt_wf.fix fun α earlier => feedback (pastArena α earlier)

private theorem tower_eq (α : Ordinal.{u}) :
    tower α = feedback (pastArena α (fun β _ => tower β)) :=
  WellFounded.fix_eq Ordinal.lt_wf (fun α earlier => feedback (pastArena α earlier)) α

abbrev Stage (α : Ordinal.{u}) : Type u := (tower α).Key
def stageValue (α : Ordinal.{u}) : Stage α → W.{u} := (tower α).value
def stageBuild (α : Ordinal.{u}) (k : Stage α) : ParentCompletion.Build (stageValue α k) :=
  (tower α).build k

private theorem prior_in_past {β α : Ordinal.{u}} (h : β < α) (k : Stage β) :
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
theorem covers_at_rank (x : W.{u}) :
    ∃ k : Stage x.rank, stageValue x.rank k = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have supported : (x : Set W.{u}) ⊆ parents (pastArena x.rank (fun β _ => tower β)) := by
      intro y hy
      obtain ⟨k, hk⟩ := ih y hy
      rw [← hk]
      exact prior_in_past (ZFSet.rank_lt_of_mem hy) k
    obtain ⟨m, hm⟩ := every_supported_value
      (pastArena x.rank (fun β _ => tower β)) x supported
    change ∃ k : (tower x.rank).Key, (tower x.rank).value k = x
    rw [tower_eq]
    exact ⟨.inr m, hm⟩

theorem covers (x : W.{u}) : ∃ α : Ordinal.{u}, ∃ k : Stage α, stageValue α k = x := by
  obtain ⟨k, hk⟩ := covers_at_rank x
  exact ⟨x.rank, k, hk⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptArena
