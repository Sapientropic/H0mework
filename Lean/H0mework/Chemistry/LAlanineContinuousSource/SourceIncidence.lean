import H0mework.Chemistry.LAlanineContinuousSource.SourceRectangle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangle

open SourceFiniteData SourceGaussianModel SourceSignedEvaluator

noncomputable section

theorem actual_group_count : rawGroups.size = 94 := rfl

def memberRegistration (basis : Basis) : Prop :=
  (source_terms basis).all (fun term => decide (groupForTerm term < 94)) = true

theorem all_members_registered : ∀ basis : Basis, memberRegistration basis := by
  unfold memberRegistration
  decide +kernel

theorem source_term_registered (basis : Basis) (term : SourceGaussianModel.Term)
    (member : term ∈ source_terms basis) : groupForTerm term < 94 := by
  have source := all_members_registered basis
  have registered : ∀ t ∈ source_terms basis, groupForTerm t < 94 := by
    simpa only [memberRegistration, List.all_eq_true, decide_eq_true_eq] using source
  exact registered term member

theorem actual_group_terms : ∀ g : Group,
    groupForTerm (groupTerm g) = g.val ∧
    (groupTerm g).exponent = groupExponent g ∧
    (groupTerm g).centre 0 = groupCentre g 0 ∧
    (groupTerm g).centre 1 = groupCentre g 1 ∧
    (groupTerm g).centre 2 = groupCentre g 2 := by
  decide +kernel

theorem group_steps_registered (f : Field) (g : Group) : steps f (groupTerm g) = groupSteps f g := by
  simp only [steps, groupSteps, (actual_group_terms g).1]

theorem source_jet_prefix (jet : Jet) : multiindex jet = SourceFiniteData.jetMulti (jetIndex jet) := by
  funext axis
  fin_cases jet <;> fin_cases axis <;> rfl

def sourceGroup (basis : Basis) (term : SourceGaussianModel.Term) (member : term ∈ source_terms basis) : Group :=
  ⟨groupForTerm term, source_term_registered basis term member⟩

def lookupGroup (term : SourceGaussianModel.Term) : Group :=
  ⟨groupForTerm term % 94, Nat.mod_lt _ (by decide)⟩

def radialAgreement (basis : Basis) : Prop :=
  (source_terms basis).all (fun term => decide (
    term.exponent = (groupTerm (lookupGroup term)).exponent ∧
    term.centre 0 = (groupTerm (lookupGroup term)).centre 0 ∧
    term.centre 1 = (groupTerm (lookupGroup term)).centre 1 ∧
    term.centre 2 = (groupTerm (lookupGroup term)).centre 2)) = true

theorem actual_radial_agreement : ∀ basis : Basis, radialAgreement basis := by
  unfold radialAgreement
  decide +kernel

theorem lookupGroup_registered (basis : Basis) (term : SourceGaussianModel.Term)
    (member : term ∈ source_terms basis) : lookupGroup term = sourceGroup basis term member := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (source_term_registered basis term member)

theorem source_radial_same_group (f : Field) (basis : Basis) (term : SourceGaussianModel.Term)
    (member : term ∈ source_terms basis) :
    radialPair term (actualBox f) = radialPair (groupTerm (sourceGroup basis term member)) (actualBox f) := by
  have source := List.all_eq_true.mp (actual_radial_agreement basis) term member
  have conditions := of_decide_eq_true source
  rw [lookupGroup_registered basis term member] at conditions
  simp only [radialPair, relative, conditions.1, conditions.2.1, conditions.2.2.1, conditions.2.2.2]

theorem reduction_from_groups (f : Field)
    (groups : ∀ g : Group, TermReductionValid (groupTerm g) (actualBox f) (groupSteps f g).1 (groupSteps f g).2)
    (basis : Basis) (term : SourceGaussianModel.Term) (member : term ∈ source_terms basis) :
    TermReductionValid term (actualBox f) (steps f term).1 (steps f term).2 := by
  have sameSteps : steps f term = groupSteps f (sourceGroup basis term member) := rfl
  unfold TermReductionValid
  rw [sameSteps, source_radial_same_group f basis term member]
  exact groups (sourceGroup basis term member)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangle
