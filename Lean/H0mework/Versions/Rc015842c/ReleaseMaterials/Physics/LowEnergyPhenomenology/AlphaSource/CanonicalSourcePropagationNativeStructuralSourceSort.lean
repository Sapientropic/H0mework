import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeSourceDictionaryNormalization

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
noncomputable section
namespace LowEnergy.SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback

noncomputable def nativeMergeFuel : ℕ → List SourceTerm → List SourceTerm → List SourceTerm
  | 0, left, right => left++right
  | _+1, [], right => right
  | _+1, left, [] => left
  | n+1, a::left, b::right => if nativeSourceKey a ≤ nativeSourceKey b then
      a::nativeMergeFuel n left (b::right)
    else b::nativeMergeFuel n (a::left) right

theorem nativeMergeFuel_perm (fuel : ℕ) (left right : List SourceTerm) :
    (nativeMergeFuel fuel left right).Perm (left++right) := by
  induction fuel generalizing left right with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases left with
    | nil => simp [nativeMergeFuel]
    | cons a left => cases right with
      | nil => simp [nativeMergeFuel]
      | cons b right =>
        simp only [nativeMergeFuel]
        split_ifs
        · exact (ih left (b::right)).cons a
        · exact ((ih (a::left) right).cons b).trans List.perm_middle.symm

noncomputable def nativeSortFuel : ℕ → List SourceTerm → List SourceTerm
  | 0, terms => terms
  | _+1, [] => []
  | _+1, [a] => [a]
  | n+1, a::b::rest =>
      let terms := a::b::rest
      let cut := terms.length/2
      let left := nativeSortFuel n (terms.take cut)
      let right := nativeSortFuel n (terms.drop cut)
      nativeMergeFuel (left.length+right.length) left right

theorem nativeSortFuel_perm (fuel : ℕ) (terms : List SourceTerm) :
    (nativeSortFuel fuel terms).Perm terms := by
  induction fuel generalizing terms with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases terms with
    | nil => exact List.Perm.refl _
    | cons a rest => cases rest with
      | nil => exact List.Perm.refl _
      | cons b rest =>
        change (nativeMergeFuel _ _ _).Perm (a::b::rest)
        exact (nativeMergeFuel_perm _ _ _).trans
          (((ih _).append (ih _)).trans (List.Perm.of_eq (List.take_append_drop _ _)))

def nativeFuelCanonical (terms : List SourceTerm) : List SourceTerm :=
  sourceAdjacentNormalize (nativeSortFuel terms.length terms)

theorem nativeFuelCanonical_value (terms : List SourceTerm) (p : Fin 4 → ℂ) :
    sourceMatrix (nativeFuelCanonical terms) p = sourceMatrix terms p := by
  rw [nativeFuelCanonical,sourceAdjacentNormalize_value]
  exact ((nativeSortFuel_perm _ terms).map (fun term => term.matrix p)).sum_eq

end LowEnergy.SourcePropagationNativeActionHessian
