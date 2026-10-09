import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Current
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveField
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame} {current : Occurrence frame}

def oldCount (source : Inlet current) : Nat := Fintype.card (OldElectronIndex source)
def isWater (atom : CPS1AddressedHydrolysis.Atom) : Bool :=
  match atom.origin with | .old _ => false | .water .. => true
def waterAtoms (source : Inlet current) : List CPS1AddressedHydrolysis.Atom := source.body.atoms.filter isWater
def newCount (source : Inlet current) : Nat :=
  ((CPS1AddressedReactiveJoint.particles (waterAtoms source)).filter
    (fun particle => CPS1ElectronicSource.isElectron ⟨particle.readout,⟨0,0,1⟩⟩)).length
def addedModes (source : Inlet current) : Nat := max 1 ((oldCount source+newCount source+1)/2)
abbrev AddedPrimitive (source : Inlet current) :=
  (NuclearIndex source.body × Fin (addedModes source)) × Bool

def addedJet (source : Inlet current) (index : AddedPrimitive source) (jet : Fin 3 → Nat) : SpinSpace :=
  PiLp.single 2 index.2 (orbitalField (position source.body index.1.1) index.1.2.val jet)
def addedField (source : Inlet current) (index : AddedPrimitive source) : SpinSpace := addedJet source index 0

def oldProjection (source : Inlet current) (field : SpinSpace) : SpinSpace :=
  ∑ old, inner ℂ (source.oldFields old) field • source.oldFields old

def residualField (source : Inlet current) (index : AddedPrimitive source) : SpinSpace :=
  addedField source index-oldProjection source (addedField source index)

theorem residual_orthogonal (source : Inlet current) (old : OldElectronIndex source)
    (index : AddedPrimitive source) : inner ℂ (source.oldFields old) (residualField source index) = 0 := by
  have orthonormal : Orthonormal ℂ source.oldFields := source.good
  rw [residualField,inner_sub_right,oldProjection,orthonormal.inner_right_fintype]
  exact sub_self _

theorem added_nuclear_independent (source : Inlet current) (nuclear : NuclearIndex source.body) :
    LinearIndependent ℂ (fun index : Fin (addedModes source) × Bool => addedField source ((nuclear,index.1),index.2)) := by
  have spatial : ∀ spin : Bool, LinearIndependent ℂ
      (fun mode : Fin (addedModes source) => orbitalField (position source.body nuclear) mode.val 0) :=
    fun _ => orbitals_independent (position source.body nuclear) (addedModes source)
  have blocks : LinearIndependent ℂ (fun index : Σ _ : Bool, Fin (addedModes source) =>
      (PiLp.single 2 index.1 (orbitalField (position source.body nuclear) index.2.val 0) : SpinSpace)) :=
    PiLp.linearIndependent_single (p := 2) (𝕜 := ℂ)
      (fun (_ : Bool) (mode : Fin (addedModes source)) => orbitalField (position source.body nuclear) mode.val 0) spatial
  have injective : Function.Injective (fun index : Fin (addedModes source) × Bool =>
      (⟨index.2,index.1⟩ : Σ _ : Bool, Fin (addedModes source))) := by
    intro left right same
    have spin := congrArg Sigma.fst same
    have mode : left.1 = right.1 := by
      cases left
      cases right
      cases same
      rfl
    exact Prod.ext mode spin
  exact blocks.comp (fun index : Fin (addedModes source) × Bool => ⟨index.2,index.1⟩) injective

def oldSpace (source : Inlet current) : Submodule ℂ SpinSpace := Submodule.span ℂ (Set.range source.oldFields)
def residualSpace (source : Inlet current) : Submodule ℂ SpinSpace := Submodule.span ℂ (Set.range (residualField source))

theorem added_span_le (source : Inlet current) :
    Submodule.span ℂ (Set.range (addedField source)) ≤ oldSpace source ⊔ residualSpace source := by
  apply Submodule.span_le.mpr
  rintro field ⟨index,rfl⟩
  have left : oldProjection source (addedField source index) ∈ oldSpace source := by
    apply Submodule.sum_mem
    intro old _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self old))
  have right : residualField source index ∈ residualSpace source :=
    Submodule.subset_span (Set.mem_range_self index)
  exact Submodule.mem_sup.mpr ⟨oldProjection source (addedField source index),left,
    residualField source index,right,by unfold residualField; abel⟩

theorem water_nucleus (source : Inlet current) (positive : 0 < newCount source) :
    ∃ nuclear : NuclearIndex source.body,
      ∃ water slot particle, particle ∈ CPS1AddressedReactiveJoint.particles source.body.atoms ∧
        particle.address = .nucleus (.water water slot) ∧
        (nucleus source.body nuclear).particle = particle.readout := by
  have nonempty : waterAtoms source ≠ [] := by
    intro empty
    simp only [newCount,empty,CPS1AddressedReactiveJoint.particles,List.zipIdx_nil,List.flatMap_nil,
      List.filter_nil,List.length_nil] at positive
    omega
  obtain ⟨atom,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have original : atom ∈ source.body.atoms := List.mem_of_mem_filter member
  have born : isWater atom = true := (List.mem_filter.mp member).2
  cases origin : atom.origin with
  | old index => simp only [isWater,origin] at born; cases born
  | water water slot =>
    obtain ⟨atomSlot,atSlot⟩ := List.mem_iff_get.mp original
    let particle : CPS1AddressedReactiveJoint.Particle :=
      ⟨.nucleus atom.origin,atom,⟨.nucleus atomSlot.val,atom.descriptor,
        (CPS1AtomicDynamics.Charged.atomicNumber atom.descriptor.source.element : Int)⟩⟩
    have generated : particle ∈ CPS1AddressedReactiveJoint.particles source.body.atoms := by
      apply List.mem_flatMap.mpr
      refine ⟨(atom,atomSlot.val),?_,List.mem_cons_self⟩
      have held := List.get_mem source.body.atoms.zipIdx
        ⟨atomSlot.val,by simpa only [List.length_zipIdx] using atomSlot.isLt⟩
      have atSlotElem : source.body.atoms[atomSlot.val] = atom := by simpa only [List.get_eq_getElem] using atSlot
      simpa only [List.get_eq_getElem,List.getElem_zipIdx,atSlotElem,Nat.zero_add] using held
    have paid := CPS1AddressedReactiveJoint.admitted_body current.ingress.atomic current.ingress.measurements
      source.body source.actual
    have mapped := paid.2.2.2.2.2.2.2.1
    have existsNode : ∃ node ∈ source.body.nodes, node.particle = particle.readout := by
      have present : particle.readout ∈ source.body.nodes.map CPS1AtomicDynamics.Body.Node.particle :=
        mapped ▸ List.mem_map.mpr ⟨particle,generated,rfl⟩
      exact List.mem_map.mp present
    obtain ⟨node,held,identity⟩ := existsNode
    have member : node ∈ nuclei source.body := List.mem_filter.mpr ⟨held,by simp [isNucleus,identity,particle]⟩
    obtain ⟨nuclear,same⟩ := List.mem_iff_get.mp member
    refine ⟨nuclear,water,slot,particle,generated,by simp only [particle,origin],?_⟩
    change ((nuclei source.body).get nuclear).particle = particle.readout
    rw [same]
    exact identity

theorem source_residual_rank (source : Inlet current) :
    newCount source ≤ CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (residualField source) := by
  classical
  by_cases positive : 0 < newCount source
  · obtain ⟨nuclear,_⟩ := water_nucleus source positive
    have paid := CPS1MolecularFrame.FiniteNormed.independent_subfamily_rank_le
      (addedField source) (fun index : Fin (addedModes source) × Bool => ((nuclear,index.1),index.2))
      (added_nuclear_independent source nuclear)
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at paid
    have enough : oldCount source+newCount source ≤ addedModes source*2 := by unfold addedModes; omega
    have lower := enough.trans paid
    let : FiniteDimensional ℂ (oldSpace source) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range source.oldFields)
    let : FiniteDimensional ℂ (residualSpace source) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range (residualField source))
    have upper := Submodule.finrank_mono (added_span_le source)
    have sumRank := Submodule.finrank_sup_add_finrank_inf_eq (oldSpace source) (residualSpace source)
    have oldRank : Module.finrank ℂ (oldSpace source) = oldCount source :=
      finrank_span_eq_card source.good.linearIndependent
    have residualRank : Module.finrank ℂ (residualSpace source) =
        CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (residualField source) :=
      (CPS1MolecularFrame.FiniteNormed.rank_exact _).symm
    rw [CPS1MolecularFrame.FiniteNormed.rank_exact] at lower
    rw [oldRank,residualRank] at sumRank
    omega
  · omega

abbrev AddedElectronIndex (source : Inlet current) := Fin (newCount source)
abbrev ResidualIndex (source : Inlet current) := CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (residualField source)

def selectedDirection (source : Inlet current) (slot : AddedElectronIndex source) : ResidualIndex source :=
  (Fintype.equivFin (ResidualIndex source)).symm
    ⟨slot.val,slot.isLt.trans_le (source_residual_rank source)⟩

theorem selected_injective (source : Inlet current) : Function.Injective (selectedDirection source) := by
  intro left right same
  have index := (Fintype.equivFin (ResidualIndex source)).symm.injective same
  have values := congrArg (fun item : Fin (Fintype.card (ResidualIndex source)) => item.val) index
  exact Fin.ext values

def addedOccupied (source : Inlet current) (slot : AddedElectronIndex source) : SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (residualField source) (selectedDirection source slot)

theorem added_occupied_orthonormal (source : Inlet current) : Orthonormal ℂ (addedOccupied source) :=
  (CPS1MolecularFrame.FiniteNormed.field_orthonormal (residualField source)).comp
    (selectedDirection source) (selected_injective source)

theorem old_added_orthogonal (source : Inlet current) (old : OldElectronIndex source)
    (slot : AddedElectronIndex source) : inner ℂ (source.oldFields old) (addedOccupied source slot) = 0 := by
  have inside := CPS1MolecularFrame.FiniteNormed.field_mem_span (residualField source) (selectedDirection source slot)
  have zero : ∀ field ∈ Submodule.span ℂ (Set.range (residualField source)),
      inner ℂ (source.oldFields old) field = 0 := by
    intro field member
    induction member using Submodule.span_induction with
    | mem field member =>
      rcases member with ⟨index,rfl⟩
      exact residual_orthogonal source old index
    | zero => exact inner_zero_right _
    | add first second _ _ left right => rw [inner_add_right,left,right,add_zero]
    | smul scalar field _ paid => rw [inner_smul_right,paid,mul_zero]
  exact zero _ inside

abbrev OccupiedIndex (source : Inlet current) := OldElectronIndex source ⊕ AddedElectronIndex source
def occupiedFields (source : Inlet current) : OccupiedIndex source → SpinSpace :=
  Sum.elim source.oldFields (addedOccupied source)

theorem occupied_prefix (source : Inlet current) (old : OldElectronIndex source) :
    occupiedFields source (.inl old) = source.old.currentFields old := rfl

theorem occupied_orthonormal (source : Inlet current) : Orthonormal ℂ (occupiedFields source) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro first second
  cases first with
  | inl first =>
    cases second with
    | inl second => simpa only [occupiedFields,Sum.elim_inl,Sum.inl.injEq,Inlet.oldFields] using orthonormal_iff_ite.mp source.good first second
    | inr second => simp only [occupiedFields,Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,if_false]; exact old_added_orthogonal source first second
  | inr first =>
    cases second with
    | inl second =>
      simp only [occupiedFields,Sum.elim_inl,Sum.elim_inr,Sum.inr_ne_inl,if_false]
      rw [← inner_conj_symm,old_added_orthogonal,map_zero]
    | inr second => simpa only [occupiedFields,Sum.elim_inr,Sum.inr.injEq] using orthonormal_iff_ite.mp (added_occupied_orthonormal source) first second

theorem occupied_electron_account (source : Inlet current) :
    Fintype.card (OccupiedIndex source) = oldCount source+newCount source ∧
      (∑ slot : OccupiedIndex source, ‖occupiedFields source slot‖^2) =
        ((oldCount source+newCount source : Nat) : ℝ) := by
  constructor
  · simp only [OccupiedIndex,Fintype.card_sum,AddedElectronIndex,Fintype.card_fin,oldCount]
  · simp only [(occupied_orthonormal source).norm_eq_one,one_pow,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_sum,Fintype.card_fin,oldCount]

end
end CPS1ReactiveField
