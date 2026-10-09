import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Response
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1AddressedCurrentPair
noncomputable section
open CPS1ElectronicSource CPS1Deformation CPS1AddressedTransfer
open CPS1MolecularFrame (NuclearIndex PrimitiveIndex ActualIndex)
open scoped BigOperators InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def prefixRaw (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (depth : Nat) : Set SpinSpace :=
  (fun primitive : PrimitiveIndex source => rawJetAt source positions primitive 0) ''
    {primitive | primitive.1.1 = first ∨ primitive.1.1.val < depth}

/-- The selected source nucleus is first; all other raw blocks enter in the
actual nuclear row order. Its repeated row contributes a zero increment. -/
def prefixSpace (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (depth : Nat) : Submodule ℂ SpinSpace :=
  Submodule.span ℂ (prefixRaw source positions first depth)

instance prefixFinite (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (depth : Nat) :
    FiniteDimensional ℂ (prefixSpace source positions first depth) := by
  apply FiniteDimensional.span_of_finite
  exact (Set.toFinite _).image _

instance prefixComplete (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (depth : Nat) :
    CompleteSpace (prefixSpace source positions first depth) := FiniteDimensional.complete ℂ _

theorem prefix_monotone (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) : Monotone (prefixSpace source positions first) := by
  intro left right ordered
  apply Submodule.span_mono
  rintro field ⟨primitive,admitted,rfl⟩
  exact ⟨primitive,admitted.imp_right (fun lower => lt_of_lt_of_le lower ordered),rfl⟩

theorem prefix_zero (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) : prefixSpace source positions first 0 = siteSpace source positions first := by
  rw [site_basis_span]
  apply congrArg (Submodule.span ℂ)
  ext field
  constructor
  · rintro ⟨⟨⟨nuclear,mode⟩,spin⟩,admitted,rfl⟩
    have same : nuclear = first := admitted.resolve_right (Nat.not_lt_zero _)
    subst nuclear
    exact ⟨(mode,spin),rfl⟩
  · rintro ⟨⟨mode,spin⟩,rfl⟩
    exact ⟨((first,mode),spin),Or.inl rfl,rfl⟩

theorem prefix_repeated (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) :
    prefixSpace source positions first (first.val+1) = prefixSpace source positions first first.val := by
  apply congrArg (Submodule.span ℂ)
  ext field
  constructor <;> rintro ⟨primitive,admitted,rfl⟩
  · refine ⟨primitive,?_,rfl⟩
    rcases admitted with same | earlier
    · exact Or.inl same
    · by_cases same : primitive.1.1 = first
      · exact Or.inl same
      · right
        have different : primitive.1.1.val ≠ first.val := fun equality => same (Fin.ext equality)
        omega
  · exact ⟨primitive,admitted.imp_right (fun earlier => by omega),rfl⟩

def fullSpace (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source) :
    Submodule ℂ SpinSpace := Submodule.span ℂ (Set.range (fun primitive : PrimitiveIndex source =>
      rawJetAt source positions primitive 0))

theorem prefix_full (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) :
    prefixSpace source positions first source.geometry.nuclei.length = fullSpace source positions := by
  apply congrArg (Submodule.span ℂ)
  ext field
  constructor
  · rintro ⟨primitive,_,rfl⟩
    exact ⟨primitive,rfl⟩
  · rintro ⟨primitive,rfl⟩
    exact ⟨primitive,Or.inr primitive.1.1.isLt,rfl⟩

def incrementSpace (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (index : NuclearIndex source) : Submodule ℂ SpinSpace :=
  (prefixSpace source positions first index.val)ᗮ ⊓ prefixSpace source positions first (index.val+1)

instance incrementFinite (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : FiniteDimensional ℂ (incrementSpace source positions first index) :=
  Submodule.finiteDimensional_of_le (inf_le_right : incrementSpace source positions first index ≤ _)

instance incrementComplete (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : CompleteSpace (incrementSpace source positions first index) :=
  FiniteDimensional.complete ℂ _

private theorem nested_difference (S T : Submodule ℂ SpinSpace)
    [S.HasOrthogonalProjection] [T.HasOrthogonalProjection] [(Sᗮ ⊓ T).HasOrthogonalProjection]
    (nested : S ≤ T) :
    (Sᗮ ⊓ T).starProjection = T.starProjection-S.starProjection := by
  apply ContinuousLinearMap.ext
  intro field
  change (Sᗮ ⊓ T).starProjection field = T.starProjection field-S.starProjection field
  have commuting : S.starProjection (T.starProjection field) = S.starProjection field := by
    simpa only [ContinuousLinearMap.comp_apply] using
      DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le nested) field
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · constructor
    · rw [← commuting]
      exact S.sub_starProjection_mem_orthogonal _
    · exact T.sub_mem (T.starProjection_apply_mem _) (nested (S.starProjection_apply_mem _))
  · intro other member
    have outer := (Submodule.mem_orthogonal' _ _).mp (T.sub_starProjection_mem_orthogonal field) other member.2
    have inner := member.1 (S.starProjection field) (S.starProjection_apply_mem field)
    have split : field-(T.starProjection field-S.starProjection field) =
        (field-T.starProjection field)+S.starProjection field := by abel
    rw [split,inner_add_left,outer,inner,add_zero]

theorem increment_projection (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) :
    (incrementSpace source positions first index).starProjection =
      (prefixSpace source positions first (index.val+1)).starProjection-
        (prefixSpace source positions first index.val).starProjection :=
  nested_difference _ _ (prefix_monotone source positions first (by omega))

def sectorSpace (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : Submodule ℂ SpinSpace :=
  if index = first then siteSpace source positions first else incrementSpace source positions first index

instance sectorFinite (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : FiniteDimensional ℂ (sectorSpace source positions first index) := by
  by_cases same : index = first
  · have equality : sectorSpace source positions first index = siteSpace source positions first :=
      if_pos same
    exact equality.symm ▸ (inferInstance : FiniteDimensional ℂ (siteSpace source positions first))
  · have equality : sectorSpace source positions first index = incrementSpace source positions first index :=
      if_neg same
    exact equality.symm ▸ (inferInstance : FiniteDimensional ℂ (incrementSpace source positions first index))

instance sectorComplete (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : CompleteSpace (sectorSpace source positions first index) :=
  FiniteDimensional.complete ℂ _

def projection (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) : SpinSpace →L[ℂ] SpinSpace :=
  (sectorSpace source positions first index).starProjection

theorem first_projection (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) : projection source positions first first = siteProjection source positions first := by
  simp [projection,sectorSpace,siteProjection]

theorem projection_increment (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first index : NuclearIndex source) :
    projection source positions first index =
      ((prefixSpace source positions first (index.val+1)).starProjection-
        (prefixSpace source positions first index.val).starProjection) +
      (if index = first then (prefixSpace source positions first 0).starProjection else 0) := by
  classical
  by_cases same : index = first
  · subst index
    simp only [first_projection,prefix_repeated,sub_self,zero_add,ite_true,prefix_zero]
    rfl
  · simp only [projection,sectorSpace,if_neg same,increment_projection,add_zero]

private theorem telescoping {M : Type*} [AddCommGroup M] (values : Nat → M) (count : Nat) :
    (∑ index : Fin count, (values (index.val+1)-values index.val)) = values count-values 0 := by
  induction count with
  | zero => simp
  | succ count previous =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,previous]
    abel

theorem projections_sum (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) :
    ∑ index : NuclearIndex source, projection source positions first index =
      (prefixSpace source positions first source.geometry.nuclei.length).starProjection := by
  classical
  simp_rw [projection_increment]
  rw [Finset.sum_add_distrib]
  rw [telescoping (fun depth => (prefixSpace source positions first depth).starProjection)
    source.geometry.nuclei.length]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  abel

theorem basis_in_full (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (index : ActualIndex source) : basisAt source positions index ∈ fullSpace source positions := by
  apply Submodule.sum_mem
  intro primitive _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨primitive,rfl⟩)

theorem occupied_in_full (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (occupied : Occupation source) (slot : ElectronIndex source.geometry) :
    occupiedFieldsAt source positions occupied slot ∈ fullSpace source positions := by
  apply Submodule.sum_mem
  intro index _
  exact Submodule.smul_mem _ _ (basis_in_full source positions index)

theorem projections_reconstruct (source : CPS1ElectronicSource.State frame) (positions : NuclearConfiguration source)
    (first : NuclearIndex source) (field : SpinSpace) (generated : field ∈ fullSpace source positions) :
    ∑ index : NuclearIndex source, projection source positions first index field = field := by
  rw [← sum_apply,projections_sum]
  apply Submodule.starProjection_eq_self_iff.mpr
  rw [prefix_full]
  exact generated

end
end CPS1AddressedCurrentPair
