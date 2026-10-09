import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedReactiveJoint.Current
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Fields
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Normed

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CPS1ReactiveField
noncomputable section
open CPS1ElectronicSource CPS1AddressedHydrolysis
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def nuclei (body : CPS1AddressedReactiveJoint.Body frame) : List CPS1AtomicDynamics.Body.Node :=
  body.nodes.filter isNucleus

def electrons (body : CPS1AddressedReactiveJoint.Body frame) : List CPS1AtomicDynamics.Body.Node :=
  body.nodes.filter isElectron

def electronCount (body : CPS1AddressedReactiveJoint.Body frame) : Nat := (electrons body).length

def modes (body : CPS1AddressedReactiveJoint.Body frame) : Nat := max 1 ((electronCount body+1)/2)

abbrev NuclearIndex (body : CPS1AddressedReactiveJoint.Body frame) := Fin (nuclei body).length
abbrev ModeIndex (body : CPS1AddressedReactiveJoint.Body frame) := Fin (modes body)
abbrev PrimitiveIndex (body : CPS1AddressedReactiveJoint.Body frame) := (NuclearIndex body × ModeIndex body) × Bool

def nucleus (body : CPS1AddressedReactiveJoint.Body frame) (index : NuclearIndex body) :
    CPS1AtomicDynamics.Body.Node := (nuclei body).get index

def position (body : CPS1AddressedReactiveJoint.Body frame) (index : NuclearIndex body) : Point :=
  Geometry.nucleusPosition (nucleus body index)

def rawJet (body : CPS1AddressedReactiveJoint.Body frame) (index : PrimitiveIndex body)
    (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (position body index.1.1) index.1.2.val jet)

def rawField (body : CPS1AddressedReactiveJoint.Body frame) (index : PrimitiveIndex body) : SpinSpace :=
  rawJet body index 0

theorem primitive_source (current : CPS1AddressedReactiveJoint.Occurrence frame)
    (body : CPS1AddressedReactiveJoint.Body frame)
    (actual : CPS1AddressedReactiveJoint.admission current = .ok body) (index : PrimitiveIndex body) :
    ∃ particle ∈ CPS1AddressedReactiveJoint.particles body.atoms,
      (nucleus body index.1.1).particle = particle.readout ∧
      CPS1AddressedReactiveJoint.Rows.row? body.sourceRows particle.address =
        some (nucleus body index.1.1).row ∧
      rawField body index = PiLp.single 2 index.2
        (orbitalField (Geometry.nucleusPosition (nucleus body index.1.1)) index.1.2.val 0) := by
  have paid := CPS1AddressedReactiveJoint.admitted_body current.atomic current.measurements body actual
  have member : nucleus body index.1.1 ∈ body.nodes :=
    List.mem_of_mem_filter (List.get_mem _ _)
  rcases paid.2.2.2.2.2.2.2.2.2 _ member with ⟨_,particle,held,source,row⟩
  exact ⟨particle,held,source,row,rfl⟩

theorem nucleus_fields_independent (body : CPS1AddressedReactiveJoint.Body frame) (nuclear : NuclearIndex body) :
    LinearIndependent ℂ (fun index : ModeIndex body × Bool => rawField body ((nuclear,index.1),index.2)) := by
  have spatial : ∀ spin : Bool, LinearIndependent ℂ
      (fun mode : ModeIndex body => orbitalField (position body nuclear) mode.val 0) :=
    fun _ => orbitals_independent (position body nuclear) (modes body)
  have blocks : LinearIndependent ℂ (fun index : Σ _ : Bool, ModeIndex body =>
      (PiLp.single 2 index.1 (orbitalField (position body nuclear) index.2.val 0) : SpinSpace)) :=
    PiLp.linearIndependent_single (p := 2) (𝕜 := ℂ) (fun (_ : Bool) (mode : ModeIndex body) =>
      orbitalField (position body nuclear) mode.val 0) spatial
  have injective : Function.Injective (fun index : ModeIndex body × Bool =>
      (⟨index.2,index.1⟩ : Σ _ : Bool, ModeIndex body)) := by
    intro left right same
    have spin := congrArg Sigma.fst same
    have mode : left.1 = right.1 := by
      cases left
      cases right
      cases same
      rfl
    exact Prod.ext mode spin
  exact blocks.comp (fun index : ModeIndex body × Bool => ⟨index.2,index.1⟩) injective

theorem nuclear_rank (body : CPS1AddressedReactiveJoint.Body frame) (nuclear : NuclearIndex body) :
    electronCount body ≤ CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (rawField body) := by
  have paid := CPS1MolecularFrame.FiniteNormed.independent_subfamily_rank_le
    (rawField body) (fun index : ModeIndex body × Bool => ((nuclear,index.1),index.2))
    (nucleus_fields_independent body nuclear)
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at paid
  have enough : electronCount body ≤ modes body*2 := by
    unfold modes
    omega
  exact enough.trans paid

theorem native_nucleus (current : CPS1AddressedReactiveJoint.Occurrence frame)
    (body : CPS1AddressedReactiveJoint.Body frame)
    (actual : CPS1AddressedReactiveJoint.admission current = .ok body) (positive : 0 < electronCount body) :
    Nonempty (NuclearIndex body) := by
  have paid := CPS1AddressedReactiveJoint.admitted_body current.atomic current.measurements body actual
  cases atoms : body.atoms with
  | nil =>
    have empty : body.nodes = [] := by
      have fromSource := paid.2.2.2.2.2.2.2.1
      simpa only [atoms,CPS1AddressedReactiveJoint.particles,List.zipIdx_nil,List.flatMap_nil,List.map_nil,
        List.map_eq_nil_iff] using fromSource
    simp only [electronCount,electrons,empty,List.filter_nil,List.length_nil] at positive
    omega
  | cons atom rest =>
    let particle : CPS1AddressedReactiveJoint.Particle :=
      ⟨.nucleus atom.origin,atom,⟨.nucleus 0,atom.descriptor,
        (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int)⟩⟩
    have generated : particle ∈ CPS1AddressedReactiveJoint.particles body.atoms := by
      rw [atoms]
      apply List.mem_flatMap.mpr
      refine ⟨(atom,0),?_,List.mem_cons_self⟩
      simp
    have existsNode : ∃ node ∈ body.nodes, node.particle = particle.readout := by
      have fromSource := paid.2.2.2.2.2.2.2.1
      have member : particle.readout ∈ body.nodes.map CPS1AtomicDynamics.Body.Node.particle :=
        fromSource ▸ List.mem_map.mpr ⟨particle,generated,rfl⟩
      exact List.mem_map.mp member
    rcases existsNode with ⟨node,held,source⟩
    have member : node ∈ nuclei body := List.mem_filter.mpr ⟨held,by simp [isNucleus,source,particle]⟩
    rcases List.mem_iff_get.mp member with ⟨index,_⟩
    exact ⟨index⟩

theorem native_rank (current : CPS1AddressedReactiveJoint.Occurrence frame)
    (body : CPS1AddressedReactiveJoint.Body frame)
    (actual : CPS1AddressedReactiveJoint.admission current = .ok body) :
    electronCount body ≤ CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (rawField body) := by
  by_cases positive : 0 < electronCount body
  · obtain ⟨nuclear⟩ := native_nucleus current body actual positive
    exact nuclear_rank body nuclear
  · omega

end
end CPS1ReactiveField
