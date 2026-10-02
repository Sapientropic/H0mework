import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.GraphArenaTrial
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.Declarations.ParentCompletion.Packets

/-!
Dependent recovery of original construction trees from source graphs.

The source input remains the original successful M-graph and its B-address.
The complete material used by Build is restored from the native completion
of the already defined source-only Key programme carrier. No external Build
or target process enters this producer.

The graph retains all native parent addresses. Build is a dependent readout,
not an injective encoding of the graph: equal-valued parent addresses are
represented by one fixed actual parent when projecting to Build.parents.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherGraphBuildBridge

open MotherSmallSupport UniformSpace
open scoped Classical Topology
noncomputable section


/-- The original collector commutes with whole-material inclusion. -/
theorem formSmall_include_univ {D : Set MotherGraphArenaTrial.W} (m : Formed D) :
    formSmall Set.univ (includeCompleted (Set.subset_univ D) m) =
      formSmall D m := by
  let j := includeCompleted (Set.subset_univ D) m
  have selected_eq : selected Set.univ j = selected D m := by
    ext x
    change read Set.univ j x = 1 ↔ read D m x = 1
    rw [show read Set.univ j = read D m from
      read_includeCompleted (Set.subset_univ D) m]
  change formSmall Set.univ j = formSmall D m
  by_cases rightSmall : Small.{0} (selected D m)
  · have leftSmall : Small.{0} (selected Set.univ j) := selected_eq.symm ▸ rightSmall
    simp only [formSmall, dif_pos leftSmall, dif_pos rightSmall]
    apply congrArg some
    ext x
    rw [mem_collect, mem_collect]
    exact Iff.of_eq (congrArg (fun r : ℝ => r = 1)
      (congrFun (read_includeCompleted (Set.subset_univ D) m) x))
  · have leftSmall : ¬ Small.{0} (selected Set.univ j) :=
      fun h => rightSmall (selected_eq ▸ h)
    simp only [formSmall, dif_neg leftSmall, dif_neg rightSmall]

/-- All construction parents of a graph node have actual addresses in Key. -/
theorem node_supported (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) :
    (MotherGraphArenaTrial.collapse g b : Set MotherGraphArenaTrial.W) ⊆ MotherGraphArenaTrial.parents := by
  intro x hx
  obtain ⟨a, ha⟩ := (MotherGraphArenaTrial.mem_collapse g b x).mp hx
  exact ⟨MotherGraphArenaTrial.childAt g b a, ha⟩

/-- This target is computed from source g; it is not an external P or W-input. -/
def nodeSource (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) : MotherGraphArenaTrial.NativeMaterial :=
  (MotherGraphArenaTrial.every_supported_target (MotherGraphArenaTrial.collapse g b) (node_supported g b)).choose

theorem nodeSource_forms (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) :
    MotherGraphArenaTrial.formNative (nodeSource g b) = some (MotherGraphArenaTrial.collapse g b) :=
  (MotherGraphArenaTrial.every_supported_target (MotherGraphArenaTrial.collapse g b) (node_supported g b)).choose_spec

/-- The exact material passed to the original univ collector. -/
def nodeMaterial (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) : ParentCompletion.Material :=
  MotherGraphArenaTrial.restore (nodeSource g b)

theorem nodeMaterial_forms (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) :
    formSmall Set.univ (nodeMaterial g b) = some (MotherGraphArenaTrial.collapse g b) := by
  change formSmall Set.univ
    (includeCompleted (Set.subset_univ MotherGraphArenaTrial.parents)
      (MotherGraphArenaTrial.completedEquiv (nodeSource g b))) = _
  rw [formSmall_include_univ]
  exact nodeSource_forms g b

/-- A canonical original parent address, computed only from this graph. -/
def parentAddress (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) (x : MotherGraphArenaTrial.W)
    (hx : x ∈ MotherGraphArenaTrial.collapse g b) : MotherGraphArenaTrial.Pred g b :=
  ((MotherGraphArenaTrial.mem_collapse g b x).mp hx).choose

theorem parentAddress_value (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) (x : MotherGraphArenaTrial.W)
    (hx : x ∈ MotherGraphArenaTrial.collapse g b) :
    MotherGraphArenaTrial.collapse g (parentAddress g b x hx).val = x :=
  ((MotherGraphArenaTrial.mem_collapse g b x).mp hx).choose_spec

/-- Dependent well-founded recursion retains complete actual parent Builds. -/
def buildGraph (g : MotherGraphArenaTrial.Good) : (b : MotherGraphArenaTrial.B) → ParentCompletion.Build (MotherGraphArenaTrial.collapse g b) :=
  g.property.fix fun b earlier =>
    ParentCompletion.Build.completed (nodeMaterial g b) (nodeMaterial_forms g b)
      (fun x hx =>
        let a := parentAddress g b x hx
        Eq.mp (congrArg ParentCompletion.Build (parentAddress_value g b x hx))
          (earlier a.val a.property))

def graphParents (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) (x : MotherGraphArenaTrial.W)
    (hx : x ∈ MotherGraphArenaTrial.collapse g b) : ParentCompletion.Build x :=
  Eq.mp (congrArg ParentCompletion.Build (parentAddress_value g b x hx))
    (buildGraph g (parentAddress g b x hx).val)

theorem buildGraph_eq (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) :
    buildGraph g b =
      ParentCompletion.Build.completed (nodeMaterial g b) (nodeMaterial_forms g b)
        (graphParents g b) := by
  unfold buildGraph
  rw [WellFounded.fix_eq]
  rfl

/-- The same native material, complete parent data and original consumer. -/
theorem same_material_parent_completion (g : MotherGraphArenaTrial.Good) (b : MotherGraphArenaTrial.B) :
    ∃ actual : ParentCompletion.Completed
        (ParentCompletion.Build.completed (nodeMaterial g b) (nodeMaterial_forms g b)
          (graphParents g b)),
      ParentCompletion.restoreCompletion
        (ParentCompletion.Build.completed (nodeMaterial g b) (nodeMaterial_forms g b)
          (graphParents g b)) actual = MotherGraphArenaTrial.restore (nodeSource g b) ∧
      ParentCompletion.collectNode
        (ParentCompletion.Build.completed (nodeMaterial g b) (nodeMaterial_forms g b)
          (graphParents g b)) actual = some (MotherGraphArenaTrial.collapse g b) :=
  ParentCompletion.completed_node_collected (nodeMaterial g b) (MotherGraphArenaTrial.collapse g b)
    (nodeMaterial_forms g b) (graphParents g b)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherGraphBuildBridge
