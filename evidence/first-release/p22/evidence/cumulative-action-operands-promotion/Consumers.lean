import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Action
import Lean
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Coordinates
import SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Recovery
import SaturationMonoid.PhysicsCore.Stage9C.Revision.SpinPair.Action
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ReceiptMaterialControls
open MotherReceiptHigher MotherReceiptPayload
open scoped Classical
noncomputable section

def HighFamily : Bool → Type 3
  | true => Type 2
  | false => ULift.{3, 0} Nat

theorem actual_high_family_and_whole_old_material (oldRank : Ordinal.{0})
    (old : MotherArenaHigher.Material oldRank) (selectedType : Type 2) :
    ∃ rank : Ordinal.{3}, ∃ material : Material rank,
      ∃ available : (formJoint material).isSome,
      ∃ address : MotherArenaHigher.Base oldRank ↪ Base rank,
      ∃ p : Presentation Bool HighFamily ⟨true, selectedType⟩ ((formJoint material).get available),
        readArena oldRank address material = old ∧ p.restrict = ⟨true, selectedType⟩ ∧
        (∀ T : Type 2, (p.receipt true).symm (p.receipt true T) = T) ∧
        p.receipt false (ULift.up 37) ≠ p.receipt false (ULift.up 41) ∧
        p.answer false ≠ p.answer true ∧
        Function.LeftInverse (restrictArena oldRank rank address) (includeArena oldRank rank address) := by
  obtain ⟨rank, material, value, address, formed, original, ⟨p⟩, retained⟩ :=
    every_payload_and_arena oldRank old Bool HighFamily ⟨true, selectedType⟩
  have available : (formJoint material).isSome := by rw [formed]; rfl
  have exactValue : (formJoint material).get available = value := by simp only [formed, Option.get_some]
  let actual : Presentation Bool HighFamily ⟨true, selectedType⟩ ((formJoint material).get available) := exactValue.symm ▸ p
  refine ⟨rank, material, available, address, actual, original, actual.restrict_eq,
    fun T => (actual.receipt true).symm_apply_apply T, ?_, ?_, retained⟩
  · intro same
    have wrong := congrArg ULift.down ((actual.receipt false).injective same)
    cases wrong
  · intro same
    have wrong := actual.answer.injective same
    cases wrong

theorem ambiguous_nonempty_payload_rejected (rank : Ordinal.{3}) (base : Material rank)
    (first last : Point base) (different : first ≠ last) :
    ∃ material : Material rank, form material = none := by
  obtain ⟨selection, readback⟩ := read_surjective rank (fun _ _ => 0)
  have invalid : ¬ ∃! point : Point base, bit selection 0 (pointAddress base point) := by
    rintro ⟨selected, _present, unique⟩
    apply different
    exact (unique first (by simp only [bit, readback])).trans
      (unique last (by simp only [bit, readback])).symm
  refine ⟨pack rank (base, selection), ?_⟩
  unfold form
  rw [split_pack]
  dsimp only
  exact dif_neg invalid

theorem finite_visit_evaluates_every_high_key (rank : Ordinal.{3})
    (address input : MotherReceiptSource.Key rank) :
    let programme : MotherReceiptSource.Programme rank :=
      ⟨1, (fun _ => address), Stage9C.Revision.SpinPair.visit 10⟩
    MotherReceiptSource.finiteLaw rank programme input =
      MotherPointwiseLaws.finiteLaw (Stage9C.Revision.SpinPair.visit 10)
        (MotherStreamLaws.pad 1 (fun _ => MotherReceiptSource.observe rank address input)) := rfl

theorem full_binary_material_lift :
    ∃ old : ParentCompletion.Material.{0},
      MotherSmallSupport.read Set.univ old ∅ = 1 ∧
      MotherSmallSupport.read Set.univ old {∅} = 0 ∧
      MotherReceiptSetLift.restrictMaterial (MotherReceiptSetLift.liftMaterial.{3} old) = old ∧
      ∀ key : ZFSet.{0},
        MotherSmallSupport.read Set.univ (MotherReceiptSetLift.liftMaterial.{3} old)
          (MotherReceiptSetLift.liftSet key) = MotherSmallSupport.read Set.univ old key := by
  let profile : ZFSet.{0} → ℝ := fun key => if key = ∅ then 1 else 0
  have allowed : profile ∈ MotherSmallSupport.Allowed (Set.univ : Set ZFSet.{0}) := by
    refine ⟨fun key => ?_, fun _ _ => Set.mem_univ _⟩
    unfold profile
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨old, readback, _⟩ := MotherSmallSupport.every_supported_profile Set.univ profile allowed
  have different : ({∅} : ZFSet.{0}) ≠ ∅ := by
    intro same
    have member : (∅ : ZFSet.{0}) ∈ {∅} := ZFSet.mem_singleton.mpr rfl
    rw [same] at member
    exact ZFSet.notMem_empty ∅ member
  refine ⟨old, ?_, ?_, MotherReceiptSetLift.restrict_liftMaterial old,
    MotherReceiptSetLift.liftMaterial_read_old old⟩
  · rw [readback]
    simp only [profile, if_pos rfl]
  · rw [readback]
    simp only [profile, if_neg different]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ReceiptMaterialControls
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionTranslationControls
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Stage9C.Revision
open scoped Classical
noncomputable section

def Rank := MotherArenaHigher.carrierRank (Bool ⊕ (Bool ⊕ Bool))
def leftCode : Bool ↪ MotherArenaHigher.Base Rank :=
  Function.Embedding.inl.trans (MotherArenaHigher.carrierAddress (Bool ⊕ (Bool ⊕ Bool)))
def rightCode : (Bool ⊕ Bool) ↪ MotherArenaHigher.Base Rank :=
  Function.Embedding.inr.trans (MotherArenaHigher.carrierAddress (Bool ⊕ (Bool ⊕ Bool)))
def retract (extra : Bool) : ConstructiveRetract Bool (Bool ⊕ Bool) where
  forward := Sum.inl
  backward := fun value => match value with | .inl old => old | .inr _ => extra
  backward_forward := fun _ => rfl

def family (extra : Bool) (index : Bool) := retract (if index then extra else !extra)
def read (material : MotherArenaHigher.Material Rank) :=
  MotherActionRetract.form leftCode (fun _ => leftCode) (fun _ => rightCode) material

theorem non_surjective_both_backward_programs :
    ¬ Function.Surjective (retract false).forward ∧
    ∃ first last : MotherArenaHigher.Material Rank,
      read first = some (family false) ∧ read last = some (family true) ∧
      first ≠ last ∧
      (family false true).backward (.inr true) = false ∧
      (family true true).backward (.inr true) = true := by
  refine ⟨?_, ?_⟩
  · intro onto
    obtain ⟨value, same⟩ := onto (.inr false)
    cases same
  · obtain ⟨first, firstFormed⟩ := MotherActionRetract.every_retract
      leftCode (fun _ => leftCode) (fun _ => rightCode) (family false)
    obtain ⟨last, lastFormed⟩ := MotherActionRetract.every_retract
      leftCode (fun _ => leftCode) (fun _ => rightCode) (family true)
    refine ⟨first, last, firstFormed, lastFormed, ?_, rfl, rfl⟩
    intro same
    have equalFamilies := Option.some.inj (firstFormed.symm.trans ((congrArg read same).trans lastFormed))
    have falseTrue := congrArg (fun values => (values true).backward (.inr true)) equalFamilies
    cases falseTrue

theorem bad_backward_material_rejected :
    ∃ forwardMaterial backwardMaterial : MotherArenaHigher.Material Rank,
      MotherArenaReceipts.NativeSection.form
        (MotherArenaObligation.sigmaEmbedding leftCode (fun _ => leftCode))
        (fun _ => rightCode) forwardMaterial = some (fun point => Sum.inl point.2) ∧
      MotherArenaReceipts.NativeSection.form
        (MotherArenaObligation.sigmaEmbedding leftCode (fun _ => rightCode))
        (fun _ => leftCode) backwardMaterial = some (fun _ => false) ∧
      read (MotherArenaHigher.pack Rank (forwardMaterial, backwardMaterial)) = none := by
  obtain ⟨forwardMaterial, forwardFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (MotherArenaObligation.sigmaEmbedding leftCode (fun _ => leftCode))
    (fun _ => rightCode) (fun point => Sum.inl point.2)
  obtain ⟨backwardMaterial, backwardFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (MotherArenaObligation.sigmaEmbedding leftCode (fun _ => rightCode))
    (fun _ => leftCode) (fun _ => false)
  refine ⟨forwardMaterial, backwardMaterial, forwardFormed, backwardFormed, ?_⟩
  have invalid : ¬ (∀ (_index : Bool) (value : Bool), false = value) := by
    intro accepted
    have impossible := accepted true true
    cases impossible
  simp only [read, MotherActionRetract.form, MotherArenaHigher.split_pack,
    forwardFormed, backwardFormed, Option.bind_some, dif_neg invalid]

theorem full_self_translation (N : WorldRelationNetwork.{0})
    (original : TypedSemanticWorldNetworkTranslationAt N N) :
    ∃ rank : Ordinal.{0}, ∃ coordinates : MotherActionTranslation.Coordinates (rank := rank) N,
      ∃ material : MotherArenaHigher.Material rank,
        MotherActionTranslation.form coordinates coordinates material = some original := by
  obtain ⟨rank, networkMaterial, generated, formed, ⟨presentation⟩⟩ := MotherArenaNetworkOrigin.every_network N
  let coordinates := MotherActionTranslation.Coordinates.pullback presentation
    (MotherActionTranslation.coordinatesOfNetwork networkMaterial generated formed)
  obtain ⟨material, actual⟩ := MotherActionTranslation.every_translation coordinates coordinates original
  exact ⟨rank, coordinates, material, actual⟩

theorem spin_pair_full_translation :
    ∃ rank : Ordinal.{0}, ∃ coordinates : MotherActionTranslation.Coordinates (rank := rank) MaterialN,
      ∃ material : MotherArenaHigher.Material rank,
        MotherActionTranslation.form coordinates coordinates material =
          some (MotherNativeAction.read SpinPair.actionProgram).translation :=
  full_self_translation MaterialN (MotherNativeAction.read SpinPair.actionProgram).translation

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ActionTranslationControls
open Lean Elab Command
open SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private partial def recoveryClosure (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then recoveryClosure env rest seen
      else
        let children := match env.checked.get.find? name with
          | some info => info.getUsedConstantsAsSet.toArray.toList
          | none => []
        recoveryClosure env (children ++ rest) (seen.insert name)


run_cmd do
  let env ← getEnv
  for module in env.header.moduleNames do
    if "scratch.".isPrefixOf module.toString then throwError "PRODUCTION_SCRATCH_IMPORT {module}"
  let controls := [``ReceiptMaterialControls.actual_high_family_and_whole_old_material, ``ReceiptMaterialControls.ambiguous_nonempty_payload_rejected, ``ReceiptMaterialControls.finite_visit_evaluates_every_high_key, ``ReceiptMaterialControls.full_binary_material_lift, ``ActionTranslationControls.non_surjective_both_backward_programs, ``ActionTranslationControls.bad_backward_material_rejected, ``ActionTranslationControls.full_self_translation, ``ActionTranslationControls.spin_pair_full_translation]
  let closure := recoveryClosure env controls
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : NameSet := {}
  let mut edges := 0
  for name in closure.toArray do
    let some info := env.checked.get.find? name | throwError "CONTROL_MISSING {name}"
    if info.isUnsafe || info.isPartial then throwError "CONTROL_UNSAFE_PARTIAL {name}"
    edges := edges + info.getUsedConstantsAsSet.size
    match info with
    | .axiomInfo _ =>
        unless allowed.contains name do throwError "CONTROL_AXIOM {name}"
        axioms := axioms.insert name
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (info.value? true).isSome do throwError "CONTROL_MISSING_VALUE {name}"
    | _ => pure ()
  for name in controls do
    let used ← collectAxioms name
    logInfo m!"CONTROL {name} axioms={used}"
  logInfo m!"CONTROLS_PASS count={controls.length} closure={closure.size} edges={edges} axioms={axioms.toArray} unsafe=0 partial=0"
