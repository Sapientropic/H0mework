import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Carried

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace CPS1ReactiveField.Carried
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame} {current : Occurrence frame}

def freshAtoms (old : Snapshot) (source : Inlet current) : List CPS1AddressedHydrolysis.Atom :=
  source.body.atoms.filter (fun atom => isWater atom && !old.waterOrigins.contains atom.origin)
def freshCount (old : Snapshot) (source : Inlet current) : Nat :=
  ((CPS1AddressedReactiveJoint.particles (freshAtoms old source)).filter
    (fun particle => isElectron ⟨particle.readout,⟨0,0,1⟩⟩)).length
def renewalModes (old : Snapshot) (source : Inlet current) : Nat := max 1 ((old.Ne+freshCount old source+1)/2)
abbrev RenewalPrimitive (old : Snapshot) (source : Inlet current) :=
  (NuclearIndex source.body × Fin (renewalModes old source)) × Bool

def renewalPrimitive (old : Snapshot) (source : Inlet current) (index : RenewalPrimitive old source) : Primitive :=
  ⟨.reactive (bodyOrigin source index.1.1),position source.body index.1.1,index.1.2.val,index.2⟩
def renewalField (old : Snapshot) (source : Inlet current) (index : RenewalPrimitive old source) : SpinSpace :=
  (renewalPrimitive old source index).jet 0
def carriedProjection (old : Snapshot) (field : SpinSpace) : SpinSpace :=
  ∑ slot, inner ℂ (old.fields slot) field • old.fields slot
def renewalResidual (old : Snapshot) (source : Inlet current) (index : RenewalPrimitive old source) : SpinSpace :=
  renewalField old source index-carriedProjection old (renewalField old source index)

theorem fresh_nucleus (old : Snapshot) (source : Inlet current) (positive : 0 < freshCount old source) :
    ∃ nuclear : NuclearIndex source.body, ∃ particle,
      particle ∈ CPS1AddressedReactiveJoint.particles source.body.atoms ∧
      particle.atom ∈ freshAtoms old source ∧ (nucleus source.body nuclear).particle = particle.readout := by
  have nonempty : freshAtoms old source ≠ [] := by
    intro empty
    simp only [freshCount,empty,CPS1AddressedReactiveJoint.particles,List.zipIdx_nil,List.flatMap_nil,
      List.filter_nil,List.length_nil] at positive
    omega
  obtain ⟨atom,atomMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have original : atom ∈ source.body.atoms := List.mem_of_mem_filter atomMember
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
  have paid := CPS1AddressedReactiveJoint.admitted_body current.ingress.atomic current.ingress.measurements source.body source.actual
  have mapped := paid.2.2.2.2.2.2.2.1
  have existsNode : ∃ node ∈ source.body.nodes, node.particle = particle.readout := by
    have present : particle.readout ∈ source.body.nodes.map CPS1AtomicDynamics.Body.Node.particle :=
      mapped ▸ List.mem_map.mpr ⟨particle,generated,rfl⟩
    exact List.mem_map.mp present
  obtain ⟨node,held,identity⟩ := existsNode
  have member : node ∈ nuclei source.body := List.mem_filter.mpr ⟨held,by simp [isNucleus,identity,particle]⟩
  obtain ⟨nuclear,same⟩ := List.mem_iff_get.mp member
  refine ⟨nuclear,particle,generated,atomMember,?_⟩
  change ((nuclei source.body).get nuclear).particle = particle.readout
  rw [same]
  exact identity

theorem renewal_independent (old : Snapshot) (source : Inlet current) (nuclear : NuclearIndex source.body) :
    LinearIndependent ℂ (fun index : Fin (renewalModes old source) × Bool => renewalField old source ((nuclear,index.1),index.2)) := by
  have spatial : ∀ spin : Bool, LinearIndependent ℂ
      (fun mode : Fin (renewalModes old source) => orbitalField (position source.body nuclear) mode.val 0) :=
    fun _ => orbitals_independent (position source.body nuclear) (renewalModes old source)
  have blocks : LinearIndependent ℂ (fun index : Σ _ : Bool, Fin (renewalModes old source) =>
      (PiLp.single 2 index.1 (orbitalField (position source.body nuclear) index.2.val 0) : SpinSpace)) :=
    PiLp.linearIndependent_single (p := 2) (𝕜 := ℂ)
      (fun (_ : Bool) (mode : Fin (renewalModes old source)) => orbitalField (position source.body nuclear) mode.val 0) spatial
  have injective : Function.Injective (fun index : Fin (renewalModes old source) × Bool =>
      (⟨index.2,index.1⟩ : Σ _ : Bool, Fin (renewalModes old source))) := by
    intro left right same
    have spin := congrArg Sigma.fst same
    have mode : left.1 = right.1 := by cases left; cases right; cases same; rfl
    exact Prod.ext mode spin
  exact blocks.comp (fun index : Fin (renewalModes old source) × Bool => ⟨index.2,index.1⟩) injective

theorem renewal_residual_rank (old : Snapshot) (good : old.Good) (source : Inlet current) :
    freshCount old source ≤ CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (renewalResidual old source) := by
  classical
  by_cases positive : 0 < freshCount old source
  · obtain ⟨nuclear,_⟩ := fresh_nucleus old source positive
    have paid := CPS1MolecularFrame.FiniteNormed.independent_subfamily_rank_le
      (renewalField old source) (fun index : Fin (renewalModes old source) × Bool => ((nuclear,index.1),index.2))
      (renewal_independent old source nuclear)
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at paid
    have enough : old.Ne+freshCount old source ≤ renewalModes old source*2 := by unfold renewalModes; omega
    have lower := enough.trans paid
    let oldSpace := Submodule.span ℂ (Set.range old.fields)
    let remainder := Submodule.span ℂ (Set.range (renewalResidual old source))
    let : FiniteDimensional ℂ oldSpace := FiniteDimensional.span_of_finite ℂ (Set.finite_range old.fields)
    let : FiniteDimensional ℂ remainder := FiniteDimensional.span_of_finite ℂ (Set.finite_range (renewalResidual old source))
    have inclusion : Submodule.span ℂ (Set.range (renewalField old source)) ≤ oldSpace ⊔ remainder := by
      apply Submodule.span_le.mpr
      rintro field ⟨index,rfl⟩
      have projected : carriedProjection old (renewalField old source index) ∈ oldSpace := by
        apply Submodule.sum_mem
        intro slot _
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self slot))
      exact Submodule.mem_sup.mpr ⟨_,projected,_,Submodule.subset_span (Set.mem_range_self index),
        by unfold renewalResidual; abel⟩
    have upper := Submodule.finrank_mono inclusion
    have sumRank := Submodule.finrank_sup_add_finrank_inf_eq oldSpace remainder
    have oldRank : Module.finrank ℂ oldSpace = old.Ne := finrank_span_eq_card good.linearIndependent
    have remainingRank : Module.finrank ℂ remainder =
        CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (renewalResidual old source) :=
      (CPS1MolecularFrame.FiniteNormed.rank_exact _).symm
    rw [CPS1MolecularFrame.FiniteNormed.rank_exact] at lower
    rw [oldRank,remainingRank] at sumRank
    omega
  · omega

abbrev RenewalDirection (old : Snapshot) (source : Inlet current) :=
  CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (renewalResidual old source)
def direction (old : Snapshot) (good : old.Good) (source : Inlet current) (slot : Fin (freshCount old source)) :
    RenewalDirection old source :=
  (Fintype.equivFin (RenewalDirection old source)).symm ⟨slot.val,slot.isLt.trans_le (renewal_residual_rank old good source)⟩
def newOccupied (old : Snapshot) (good : old.Good) (source : Inlet current) (slot : Fin (freshCount old source)) : SpinSpace :=
  CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (renewalResidual old source) (direction old good source slot)

def renewedCoefficient (old : Snapshot) (good : old.Good) (source : Inlet current)
    (primitive : old.PrimitiveIndex ⊕ RenewalPrimitive old source) (slot : old.ElectronIndex ⊕ Fin (freshCount old source)) : ℂ :=
  match slot with
  | .inl slot => match primitive with | .inl index => old.occupied index slot | .inr _ => 0
  | .inr slot => ∑ raw, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
      (renewalResidual old source) raw (direction old good source slot)*
        (match primitive with
        | .inl index => -(∑ oldSlot, inner ℂ (old.fields oldSlot) (renewalField old source raw)*old.occupied index oldSlot)
        | .inr index => if index = raw then 1 else 0)

def nodeIsFresh (old : Snapshot) (source : Inlet current) (node : CPS1AtomicDynamics.Body.Node) : Bool :=
  ((source.body.atoms[nodeSlot node]?).map (fun atom => isWater atom && !old.waterOrigins.contains atom.origin)).getD false
def freshNodes (old : Snapshot) (source : Inlet current) : List CPS1AtomicDynamics.Body.Node :=
  source.body.nodes.filter (nodeIsFresh old source)

@[reducible] def renewed (old : Snapshot) (good : old.Good) (source : Inlet current) : Snapshot :=
  ⟨old.PrimitiveIndex ⊕ RenewalPrimitive old source,inferInstance,inferInstance,
    old.ElectronIndex ⊕ Fin (freshCount old source),inferInstance,inferInstance,
    Sum.elim old.primitive (renewalPrimitive old source),renewedCoefficient old good source,
    old.nuclei ++ (freshNodes old source).filter isNucleus,
    old.waterOrigins ++ (freshAtoms old source).map CPS1AddressedHydrolysis.Atom.origin,
    old.electronInertia,old.reserve⟩

theorem renewed_prefix (old : Snapshot) (good : old.Good) (source : Inlet current) (slot : old.ElectronIndex) :
    (renewed old good source).fields (.inl slot) = old.fields slot := by
  simp only [Snapshot.fields,Snapshot.jet,renewed,renewedCoefficient,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,zero_smul,Finset.sum_const_zero,add_zero]

theorem renewed_added (old : Snapshot) (good : old.Good) (source : Inlet current) (slot : Fin (freshCount old source)) :
    (renewed old good source).fields (.inr slot) = newOccupied old good source slot := by
  classical
  simp only [Snapshot.fields,Snapshot.jet,renewed,renewedCoefficient,Finset.sum_smul,mul_smul]
  rw [Finset.sum_comm]
  have synthesis (raw : RenewalPrimitive old source) :
      (∑ primitive : old.PrimitiveIndex ⊕ RenewalPrimitive old source,
        (match primitive with
        | .inl index => -(∑ oldSlot, inner ℂ (old.fields oldSlot) (renewalField old source raw)*old.occupied index oldSlot)
        | .inr index => if index = raw then 1 else 0) •
          (Sum.elim old.primitive (renewalPrimitive old source) primitive).jet 0) = renewalResidual old source raw := by
    rw [Fintype.sum_sum_type]
    have priorPart : (∑ primitive, -(∑ oldSlot, inner ℂ (old.fields oldSlot) (renewalField old source raw)*old.occupied primitive oldSlot) •
        (old.primitive primitive).jet 0) = -carriedProjection old (renewalField old source raw) := by
      simp only [neg_smul,Finset.sum_neg_distrib,Finset.sum_smul,mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum,carriedProjection,Snapshot.fields,Snapshot.jet]
    simp only [Sum.elim_inl,Sum.elim_inr,priorPart,ite_smul,one_smul,zero_smul,
      Finset.sum_ite_eq',Finset.mem_univ,if_true]
    exact neg_add_eq_sub _ _
  change _ = CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (renewalResidual old source) (direction old good source slot)
  rw [CPS1MolecularFrame.FiniteNormed.field_synthesis]
  apply Finset.sum_congr rfl
  intro raw _
  rw [← Finset.smul_sum]
  exact congrArg (fun field => CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ)
    (renewalResidual old source) raw (direction old good source slot) • field) (synthesis raw)

theorem renewed_good (old : Snapshot) (good : old.Good) (source : Inlet current) : (renewed old good source).Good := by
  classical
  have injective : Function.Injective (direction old good source) := by
    intro left right same
    have indices := (Fintype.equivFin (RenewalDirection old source)).symm.injective same
    exact Fin.ext (congrArg (fun index : Fin (Fintype.card (RenewalDirection old source)) => index.val) indices)
  have addedGood : Orthonormal ℂ (newOccupied old good source) :=
    (CPS1MolecularFrame.FiniteNormed.field_orthonormal (renewalResidual old source)).comp
      (direction old good source) injective
  have orthogonal (oldSlot : old.ElectronIndex) (slot : Fin (freshCount old source)) :
      inner ℂ (old.fields oldSlot) (newOccupied old good source slot) = 0 := by
    have within := CPS1MolecularFrame.FiniteNormed.field_mem_span (renewalResidual old source) (direction old good source slot)
    have zero : ∀ field ∈ Submodule.span ℂ (Set.range (renewalResidual old source)), inner ℂ (old.fields oldSlot) field = 0 := by
      intro field member
      induction member using Submodule.span_induction with
      | mem field member =>
        rcases member with ⟨raw,rfl⟩
        rw [renewalResidual,inner_sub_right,carriedProjection,good.inner_right_fintype,sub_self]
      | zero => exact inner_zero_right _
      | add first second _ _ left right => rw [inner_add_right,left,right,add_zero]
      | smul scalar field _ paid => rw [inner_smul_right,paid,mul_zero]
    exact zero _ within
  apply orthonormal_iff_ite.mpr
  intro first second
  cases first with
  | inl first =>
    cases second with
    | inl second => simpa only [renewed_prefix,Sum.inl.injEq] using orthonormal_iff_ite.mp good first second
    | inr second => simp only [renewed_prefix,renewed_added,Sum.inl_ne_inr,if_false]; exact orthogonal first second
  | inr first =>
    cases second with
    | inl second =>
      simp only [renewed_prefix,renewed_added,Sum.inr_ne_inl,if_false]
      rw [← inner_conj_symm,orthogonal,map_zero]
    | inr second => simpa only [renewed_added,Sum.inr.injEq] using orthonormal_iff_ite.mp addedGood first second

theorem renewed_Ne (old : Snapshot) (good : old.Good) (source : Inlet current) :
    (renewed old good source).Ne = old.Ne+freshCount old source := by
  simp only [Snapshot.Ne,renewed,Fintype.card_sum,Fintype.card_fin]

end
end CPS1ReactiveField.Carried
