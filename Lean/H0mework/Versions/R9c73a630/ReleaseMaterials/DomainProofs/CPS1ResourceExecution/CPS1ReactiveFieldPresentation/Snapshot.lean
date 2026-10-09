import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Continuation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CPS1ReactiveField.FinitePresentation
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace

structure Snapshot where
  primitiveCount : Nat
  electronCount : Nat
  primitive : Fin primitiveCount → Carried.Primitive
  occupied : Matrix (Fin primitiveCount) (Fin electronCount) ℂ
  fields : Fin electronCount → SpinSpace
  nuclei : List CPS1AtomicDynamics.Body.Node
  waterOrigins : List CPS1AddressedHydrolysis.Origin
  electronInertia : ℝ
  energy : ℝ
  reserve : ℝ
  account : ℝ

@[reducible] def snapshot (source : Carried.Snapshot) : Snapshot :=
  ⟨Fintype.card source.PrimitiveIndex,source.Ne,
    fun index => source.primitive ((Fintype.equivFin source.PrimitiveIndex).symm index),
    fun primitive slot => source.occupied ((Fintype.equivFin source.PrimitiveIndex).symm primitive)
      ((Fintype.equivFin source.ElectronIndex).symm slot),
    fun slot => source.fields ((Fintype.equivFin source.ElectronIndex).symm slot),
    source.nuclei,source.waterOrigins,source.electronInertia,source.energy,source.reserve,source.account⟩

theorem sum_fin {I A : Type} [Fintype I] [AddCommMonoid A] (value : I → A) :
    (∑ index : Fin (Fintype.card I), value ((Fintype.equivFin I).symm index)) = ∑ index : I, value index :=
  Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

def Snapshot.jet (source : Snapshot) (slot : Fin source.electronCount) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, source.occupied primitive slot • (source.primitive primitive).jet jet

theorem primitive_exact (source : Carried.Snapshot) (index : source.PrimitiveIndex) :
    (snapshot source).primitive (Fintype.equivFin source.PrimitiveIndex index) = source.primitive index := by
  simp only [Equiv.symm_apply_apply]

theorem coefficient_exact (source : Carried.Snapshot) (primitive : source.PrimitiveIndex) (slot : source.ElectronIndex) :
    (snapshot source).occupied (Fintype.equivFin source.PrimitiveIndex primitive)
      (Fintype.equivFin source.ElectronIndex slot) = source.occupied primitive slot := by
  simp only [Equiv.symm_apply_apply]

theorem field_exact (source : Carried.Snapshot) (slot : source.ElectronIndex) :
    (snapshot source).fields (Fintype.equivFin source.ElectronIndex slot) = source.fields slot := by
  simp only [Equiv.symm_apply_apply]

theorem jet_exact (source : Carried.Snapshot) (slot : Fin (snapshot source).electronCount) (jet : Fin 3 → Nat) :
    (snapshot source).jet slot jet = source.jet ((Fintype.equivFin source.ElectronIndex).symm slot) jet := by
  unfold Snapshot.jet Carried.Snapshot.jet
  exact sum_fin (fun primitive : source.PrimitiveIndex =>
    source.occupied primitive ((Fintype.equivFin source.ElectronIndex).symm slot) • (source.primitive primitive).jet jet)

theorem jet_field (source : Carried.Snapshot) (slot : Fin (snapshot source).electronCount) :
    (snapshot source).jet slot 0 = (snapshot source).fields slot := jet_exact source slot 0

theorem good_exact (source : Carried.Snapshot) (good : source.Good) :
    Orthonormal ℂ (snapshot source).fields :=
  good.comp (Fintype.equivFin source.ElectronIndex).symm (Fintype.equivFin source.ElectronIndex).symm.injective

theorem accounts_exact (source : Carried.Snapshot) :
    (snapshot source).electronCount = source.Ne ∧
    (snapshot source).nuclei = source.nuclei ∧ (snapshot source).waterOrigins = source.waterOrigins ∧
    (snapshot source).electronInertia = source.electronInertia ∧
    (snapshot source).energy = source.energy ∧ (snapshot source).reserve = source.reserve ∧
    (snapshot source).account = source.account ∧
    (snapshot source).account = (snapshot source).energy+(snapshot source).reserve :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem electron_norm_account (source : Carried.Snapshot) (good : source.Good) :
    (∑ slot : Fin (snapshot source).electronCount, ‖(snapshot source).fields slot‖^2) =
      ((snapshot source).electronCount : ℝ) := by
  simp only [(good_exact source good).norm_eq_one,one_pow,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]

def prefixIndex {frame : CPS1Recycling.Frame} {current : CPS1ReactiveField.Occurrence frame}
    (old : Carried.Snapshot) (good : old.Good) (source : Inlet current)
    (slot : Fin (snapshot old).electronCount) : Fin (snapshot (Carried.renewed old good source)).electronCount :=
  Fintype.equivFin (Carried.renewed old good source).ElectronIndex
    (.inl ((Fintype.equivFin old.ElectronIndex).symm slot))

theorem prefix_exact {frame : CPS1Recycling.Frame} {current : CPS1ReactiveField.Occurrence frame}
    (old : Carried.Snapshot) (good : old.Good) (source : Inlet current)
    (slot : Fin (snapshot old).electronCount) :
    (snapshot (Carried.renewed old good source)).fields (prefixIndex old good source slot) = (snapshot old).fields slot := by
  rw [prefixIndex,field_exact,Carried.renewed_prefix]

theorem prefix_injective {frame : CPS1Recycling.Frame} {current : CPS1ReactiveField.Occurrence frame}
    (old : Carried.Snapshot) (good : old.Good) (source : Inlet current) :
    Function.Injective (prefixIndex old good source) :=
  (Fintype.equivFin (Carried.renewed old good source).ElectronIndex).injective.comp
    (Sum.inl_injective.comp (Fintype.equivFin old.ElectronIndex).symm.injective)

end
end CPS1ReactiveField.FinitePresentation
