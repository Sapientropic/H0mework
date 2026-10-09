import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Frame
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.State

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix
variable {frame : CPS1Recycling.Frame}

abbrev Occupation (source : CPS1ElectronicSource.State frame) :=
  Matrix (CPS1MolecularFrame.ActualIndex source) (ElectronIndex source.geometry) ℂ

def occupiedFieldsAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source) :
    ElectronIndex source.geometry → SpinSpace :=
  CPS1ElectronicEvolution.fields (basisAt source positions) occupied

theorem occupied_rank_full (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied) =
      electronCount frame source.geometry.originJoint := by
  apply Nat.le_antisymm _ enough
  simpa only [ElectronIndex,Fintype.card_fin] using
    CPS1MolecularFrame.FiniteNormed.rank_le_source_card (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)

theorem occupied_ordered_nonzero (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied))
    (index : Fin (Fintype.card (ElectronIndex source.geometry))) :
    gramSchmidtNormed ℂ (CPS1MolecularFrame.FiniteNormed.ordered
      (occupiedFieldsAt source positions occupied)) index ≠ 0 := by
  have full : Fintype.card (CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ)
      (occupiedFieldsAt source positions occupied)) =
      Fintype.card (Fin (Fintype.card (ElectronIndex source.geometry))) := by
    simpa only [CPS1MolecularFrame.FiniteNormed.rank,ElectronIndex,Fintype.card_fin] using
      occupied_rank_full source positions occupied enough
  have onto := ((Fintype.bijective_iff_injective_and_card
    (Subtype.val : CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ)
      (occupiedFieldsAt source positions occupied) → Fin (Fintype.card (ElectronIndex source.geometry)))).mpr
    ⟨Subtype.val_injective,full⟩).2
  obtain ⟨generated,same⟩ := onto index
  exact same ▸ generated.property

def normalizedIndex (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied))
    (slot : ElectronIndex source.geometry) :
    CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (occupiedFieldsAt source positions occupied) :=
  ⟨Fintype.equivFin (ElectronIndex source.geometry) slot,
    occupied_ordered_nonzero source positions occupied enough _⟩

def normalizationMatrix (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Matrix (ElectronIndex source.geometry) (ElectronIndex source.geometry) ℂ :=
  fun old slot => CPS1MolecularFrame.FiniteNormed.coefficients
    (𝕜 := ℂ) (occupiedFieldsAt source positions occupied) old
    (normalizedIndex source positions occupied enough slot)

def normalizeOccupied (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Occupation source := occupied * normalizationMatrix source positions occupied enough

theorem normalized_index_injective (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Function.Injective (normalizedIndex source positions occupied enough) := by
  intro first second same
  exact (Fintype.equivFin (ElectronIndex source.geometry)).injective (congrArg Subtype.val same)

theorem normalized_index_surjective (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Function.Surjective (normalizedIndex source positions occupied enough) := by
  intro index
  refine ⟨(Fintype.equivFin (ElectronIndex source.geometry)).symm index.val,?_⟩
  apply Subtype.ext
  exact (Fintype.equivFin (ElectronIndex source.geometry)).apply_symm_apply index.val

theorem fields_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    (basis : ι → SpinSpace) (left : Matrix ι κ ℂ) (right : Matrix κ ν ℂ) (slot : ν) :
    CPS1ElectronicEvolution.fields basis (left * right) slot =
      CPS1ElectronicEvolution.fields (CPS1ElectronicEvolution.fields basis left) right slot := by
  classical
  simp only [CPS1ElectronicEvolution.fields,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,mul_smul]
  rw [Finset.sum_comm]
  simp only [smul_smul,mul_comm]

theorem normalized_fields (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    occupiedFieldsAt source positions (normalizeOccupied source positions occupied enough) =
      fun slot => CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ)
        (occupiedFieldsAt source positions occupied) (normalizedIndex source positions occupied enough slot) := by
  funext slot
  unfold occupiedFieldsAt normalizeOccupied
  rw [fields_mul]
  exact (CPS1MolecularFrame.FiniteNormed.field_synthesis
    (occupiedFieldsAt source positions occupied) (normalizedIndex source positions occupied enough slot)).symm

theorem normalized_orthonormal (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Orthonormal ℂ (occupiedFieldsAt source positions (normalizeOccupied source positions occupied enough)) := by
  rw [normalized_fields]
  exact (CPS1MolecularFrame.FiniteNormed.field_orthonormal (occupiedFieldsAt source positions occupied)).comp
    _ (normalized_index_injective source positions occupied enough)

theorem normalization_span_exact (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) :
    Submodule.span ℂ (Set.range (occupiedFieldsAt source positions
      (normalizeOccupied source positions occupied enough))) =
      Submodule.span ℂ (Set.range (occupiedFieldsAt source positions occupied)) := by
  rw [normalized_fields]
  have range : Set.range (fun slot => CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ)
      (occupiedFieldsAt source positions occupied) (normalizedIndex source positions occupied enough slot)) =
      Set.range (CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)) := by
    simpa only [Function.comp_def] using
      (normalized_index_surjective source positions occupied enough).range_comp
        (CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (occupiedFieldsAt source positions occupied))
  rw [range]
  exact CPS1MolecularFrame.FiniteNormed.span_exact _

theorem normalization_current_fields (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : Occupation source)
    (enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied))
    (good : Orthonormal ℂ (occupiedFieldsAt source positions occupied)) :
    occupiedFieldsAt source positions (normalizeOccupied source positions occupied enough) =
      occupiedFieldsAt source positions occupied := by
  rw [normalized_fields]
  funext slot
  let raw := occupiedFieldsAt source positions occupied
  have ordered : Orthonormal ℂ (CPS1MolecularFrame.FiniteNormed.ordered raw) :=
    good.comp _ (Fintype.equivFin (ElectronIndex source.geometry)).symm.injective
  have unchanged := gramSchmidt_of_orthogonal ℂ ordered.2
  change gramSchmidtNormed ℂ (CPS1MolecularFrame.FiniteNormed.ordered raw)
    (Fintype.equivFin (ElectronIndex source.geometry) slot) = raw slot
  rw [gramSchmidtNormed,unchanged,ordered.1]
  simp only [RCLike.ofReal_one,inv_one,one_smul,CPS1MolecularFrame.FiniteNormed.ordered,
    Equiv.symm_apply_apply]

inductive Failure
  | inherited (failure : CPS1MolecularFrame.Failure)
  | missingOccupiedDirections
  | singularSourceFrame
  deriving DecidableEq

def normalize? (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) : Except Failure (Occupation source) := by
  classical
  exact if enough : electronCount frame source.geometry.originJoint ≤
      CPS1MolecularFrame.FiniteNormed.rank (𝕜 := ℂ) (occupiedFieldsAt source positions occupied)
    then .ok (normalizeOccupied source positions occupied enough)
    else .error .missingOccupiedDirections

theorem normalize_generated (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied next : Occupation source) (actual : normalize? source positions occupied = .ok next) :
    Orthonormal ℂ (occupiedFieldsAt source positions next) ∧
      Submodule.span ℂ (Set.range (occupiedFieldsAt source positions next)) =
        Submodule.span ℂ (Set.range (occupiedFieldsAt source positions occupied)) := by
  unfold normalize? at actual
  split at actual
  · cases Except.ok.inj actual
    exact ⟨normalized_orthonormal source positions occupied _,normalization_span_exact source positions occupied _⟩
  · cases actual

def sourceMomenta (source : CPS1ElectronicSource.State frame) : NuclearConfiguration source :=
  fun index axis => CPS1MolecularFrame.momentum source index axis

structure Material (frame : CPS1Recycling.Frame) where
  reference : CPS1ElectronicSource.State frame
  positions : NuclearConfiguration reference
  momenta : NuclearConfiguration reference
  occupied : Occupation reference
  reserve : ℝ

def Material.currentFields (state : Material frame) : ElectronIndex state.reference.geometry → SpinSpace :=
  occupiedFieldsAt state.reference state.positions state.occupied

def Good (state : Material frame) : Prop := Orthonormal ℂ state.currentFields

def Material.reprice (state : Material frame) (reserve : ℝ) : Material frame :=
  {state with reserve := reserve}

def Material.nuclearRow (state : Material frame) (index : CPS1MolecularFrame.NuclearIndex state.reference) :
    CPS1AtomicDynamics.Body.Row :=
  {(CPS1MolecularFrame.nucleus state.reference index).row with
    position := euclideanPoint (state.positions index)
    momentum := euclideanPoint (state.momenta index)}

def Material.nuclearIndex? (state : Material frame) (address : CPS1AtomicDynamics.Charged.Address) :
    Option (CPS1MolecularFrame.NuclearIndex state.reference) :=
  (List.finRange state.reference.geometry.nuclei.length).find?
    (fun index => CPS1MolecularFrame.address state.reference index = address)

def Material.currentRow (state : Material frame)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row) :
    CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row :=
  (entry.1,match state.nuclearIndex? entry.1 with
    | none => entry.2
    | some index => state.nuclearRow index)

def Material.currentJoint (state : Material frame) : CPS1EnzymeBath.Joint.State frame :=
  {state.reference.geometry.originJoint with
    rows := state.reference.geometry.originJoint.rows.map state.currentRow
    reserve := state.reserve}

theorem current_joint_source (state : Material frame) :
    state.currentJoint.originBody = state.reference.geometry.originJoint.originBody ∧
      state.currentJoint.components = state.reference.geometry.originJoint.components ∧
      state.currentJoint.nextOccurrence = state.reference.geometry.originJoint.nextOccurrence ∧
      state.currentJoint.reserve = state.reserve ∧
      CPS1EnzymeBath.Joint.particles frame state.currentJoint =
        CPS1EnzymeBath.Joint.particles frame state.reference.geometry.originJoint := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem current_joint_addresses (state : Material frame) :
    state.currentJoint.rows.map Prod.fst = state.reference.geometry.originJoint.rows.map Prod.fst := by
  simp only [Material.currentJoint,List.map_map,Function.comp_def,Material.currentRow]

theorem unrelated_row_retained (state : Material frame)
    (entry : CPS1AtomicDynamics.Charged.Address × CPS1AtomicDynamics.Body.Row)
    (absent : state.nuclearIndex? entry.1 = none) : state.currentRow entry = entry := by
  simp only [Material.currentRow,absent]

theorem reprice_fields (state : Material frame) (reserve : ℝ) :
    (state.reprice reserve).currentFields = state.currentFields := rfl

theorem reprice_good (state : Material frame) (reserve : ℝ) (good : Good state) :
    Good (state.reprice reserve) := good

end
end CPS1Deformation
