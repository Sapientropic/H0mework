import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.GraphBuildBridge

/-! Structural inclusion of the original graph seed and its complete parent
history into the universe required by an actual action receipt. No new set
or dependency is supplied by the caller of the lifted seed. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptSetLift
open scoped Classical
noncomputable section
universe u

def pre : PSet.{0} → PSet.{u}
  | .mk index members => .mk (ULift.{u, 0} index) (fun value => pre (members value.down))

theorem pre_equiv (first last : PSet.{0}) : PSet.Equiv (pre.{u} first) (pre.{u} last) ↔ PSet.Equiv first last := by
  induction first generalizing last with
  | mk A f ih =>
    cases last with
    | mk C g =>
      constructor
      · intro same
        constructor
        · intro a
          obtain ⟨c, equal⟩ := same.1 (ULift.up a)
          exact ⟨c.down, (ih a (g c.down)).mp equal⟩
        · intro c
          obtain ⟨a, equal⟩ := same.2 (ULift.up c)
          exact ⟨a.down, (ih a.down (g c)).mp equal⟩
      · intro same
        constructor
        · intro a
          obtain ⟨c, equal⟩ := same.1 a.down
          exact ⟨ULift.up c, (ih a.down (g c)).mpr equal⟩
        · intro c
          obtain ⟨a, equal⟩ := same.2 c.down
          exact ⟨ULift.up a, (ih a (g c.down)).mpr equal⟩

def liftSet : ZFSet.{0} → ZFSet.{u} :=
  Quotient.lift (fun value => ZFSet.mk (pre value))
    (fun first last same => Quotient.sound ((pre_equiv first last).mpr same))

theorem liftSet_injective : Function.Injective liftSet.{u} := by
  intro first last
  induction first using Quotient.inductionOn
  induction last using Quotient.inductionOn
  intro same
  exact Quotient.sound ((pre_equiv _ _).mp (Quotient.exact same))

theorem lift_mem (first last : ZFSet.{0}) : liftSet.{u} first ∈ liftSet last ↔ first ∈ last := by
  induction first using Quotient.inductionOn with
  | h first =>
    induction last using Quotient.inductionOn with
    | h last =>
      cases last with
      | mk A members =>
        constructor
        · rintro ⟨value, same⟩
          exact ⟨value.down, (pre_equiv first (members value.down)).mp same⟩
        · rintro ⟨value, same⟩
          exact ⟨ULift.up value, (pre_equiv first (members value)).mpr same⟩

theorem member_preimage {member : ZFSet.{u}} {old : ZFSet.{0}}
    (inside : member ∈ liftSet old) : ∃ original ∈ old, liftSet original = member := by
  induction old using Quotient.inductionOn with
  | h old =>
    induction member using Quotient.inductionOn with
    | h member =>
      cases old with
      | mk A members =>
        obtain ⟨value, same⟩ := inside
        exact ⟨ZFSet.mk (members value.down), ⟨value.down, PSet.Equiv.refl _⟩,
          Quotient.sound same.symm⟩

theorem lift_empty : liftSet.{u} ∅ = ∅ := by
  apply ZFSet.ext
  intro member
  constructor
  · intro inside
    obtain ⟨original, impossible, _⟩ := member_preimage inside
    exact False.elim (ZFSet.notMem_empty original impossible)
  · intro impossible
    exact False.elim (ZFSet.notMem_empty member impossible)

open MotherSmallSupport

def materialProfile (material : ParentCompletion.Material.{0}) (member : ZFSet.{u}) : ℝ :=
  if ∃ old, liftSet old = member ∧ read Set.univ material old = 1 then 1 else 0

theorem materialProfile_allowed (material : ParentCompletion.Material.{0}) :
    materialProfile.{u} material ∈ Allowed (Set.univ : Set ZFSet.{u}) := by
  refine ⟨fun member => ?_, fun _ _ => Set.mem_univ _⟩
  unfold materialProfile
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The whole parent material is included, before any collector is read. -/
def liftMaterial (material : ParentCompletion.Material.{0}) : ParentCompletion.Material.{u} :=
  (every_supported_profile Set.univ (materialProfile material) (materialProfile_allowed material)).choose

theorem liftMaterial_read (material : ParentCompletion.Material.{0}) :
    read Set.univ (liftMaterial.{u} material) = materialProfile material :=
  (every_supported_profile Set.univ (materialProfile material) (materialProfile_allowed material)).choose_spec.1

theorem liftMaterial_read_old (material : ParentCompletion.Material.{0}) (old : ZFSet.{0}) :
    read Set.univ (liftMaterial.{u} material) (liftSet old) = read Set.univ material old := by
  rw [liftMaterial_read]
  have selected : (∃ original, liftSet.{u} original = liftSet old ∧
      read Set.univ material original = 1) ↔ read Set.univ material old = 1 := by
    constructor
    · rintro ⟨original, same, one⟩
      exact liftSet_injective same ▸ one
    · exact fun one => ⟨old, rfl, one⟩
  unfold materialProfile
  rcases read_binary Set.univ material old with zero | one
  · rw [if_neg (fun inside => zero_ne_one (zero.symm.trans (selected.mp inside)))]
    exact zero.symm
  · rw [if_pos (selected.mpr one)]
    exact one.symm

def restrictMaterial (material : ParentCompletion.Material.{u}) : ParentCompletion.Material.{0} :=
  (every_supported_profile Set.univ (fun old => read Set.univ material (liftSet old))
    ⟨fun old => read_binary Set.univ material (liftSet old), fun _ _ => Set.mem_univ _⟩).choose

theorem restrictMaterial_read (material : ParentCompletion.Material.{u}) :
    read Set.univ (restrictMaterial material) = fun old => read Set.univ material (liftSet old) :=
  (every_supported_profile Set.univ (fun old => read Set.univ material (liftSet old))
    ⟨fun old => read_binary Set.univ material (liftSet old), fun _ _ => Set.mem_univ _⟩).choose_spec.1

theorem restrict_liftMaterial (material : ParentCompletion.Material.{0}) :
    restrictMaterial (liftMaterial.{u} material) = material := by
  apply (read_uniformEmbedding Set.univ).injective
  rw [restrictMaterial_read]
  funext old
  exact liftMaterial_read_old material old

theorem liftMaterial_forms {result : ZFSet.{0}} (material : ParentCompletion.Material.{0})
    (formed : formSmall Set.univ material = some result) :
    formSmall Set.univ (liftMaterial.{u} material) = some (liftSet result) := by
  have members (member : ZFSet.{u}) :
      read Set.univ (liftMaterial material) member = 1 ↔ member ∈ liftSet result := by
    rw [liftMaterial_read]
    have profile_one : materialProfile material member = 1 ↔
        ∃ old, liftSet old = member ∧ read Set.univ material old = 1 := by
      unfold materialProfile
      split <;> simp_all only [zero_ne_one, iff_self]
    rw [profile_one]
    constructor
    · rintro ⟨old, same, one⟩
      rw [← same]
      exact (lift_mem old result).mpr ((ParentCompletion.formed_members material result formed old).mp one)
    · intro inside
      obtain ⟨old, member, same⟩ := member_preimage inside
      exact ⟨old, same, (ParentCompletion.formed_members material result formed old).mpr member⟩
  have selected_eq : selected Set.univ (liftMaterial.{u} material) = (liftSet result : Set ZFSet.{u}) :=
    Set.ext members
  have small : Small.{u} (selected Set.univ (liftMaterial.{u} material)) := by
    rw [selected_eq]
    exact ZFSet.small_coe (liftSet result)
  have collected : collect Set.univ (liftMaterial.{u} material) small = liftSet result := by
    apply ZFSet.ext
    intro member
    exact (mem_collect Set.univ (liftMaterial material) small member).trans (members member)
  exact (formSmall_recovers Set.univ (liftMaterial material) small).trans (congrArg some collected)

/-- Replay the entire original parent tree under the membership-preserving
inclusion. Completed nodes keep every original parent dependency. -/
def build {old : ZFSet.{0}} (node : ParentCompletion.Build old) : ParentCompletion.Build (liftSet.{u} old) := by
  induction node with
  | seed => exact Eq.mp (congrArg ParentCompletion.Build lift_empty.symm) ParentCompletion.Build.seed
  | @completed result material formed parents ih =>
      refine ParentCompletion.Build.completed (liftMaterial material) (liftMaterial_forms material formed)
        (fun member inside => ?_)
      let availableParent := member_preimage inside
      let original := Classical.choose availableParent
      have parent := (Classical.choose_spec availableParent).1
      have same := (Classical.choose_spec availableParent).2
      exact Eq.mp (congrArg ParentCompletion.Build same) (ih original parent)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherReceiptSetLift
