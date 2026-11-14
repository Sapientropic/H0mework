import H0mework.Foundation.Relations.ScalarPresentation
import Mathlib.Tactic.Abel

/-! A finite table determines a certificate for its difference from the single net-value entry. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ScalarRelationPresentation

noncomputable section

variable {R G : Type*} [CommRing R] [AddCommGroup G] [Module R G]

private def tableOfEntries (entries : List (G × R)) : G →₀ R :=
  (entries.map fun (point, coefficient) => Finsupp.single point coefficient).sum

private def certificateOfEntries : List (G × R) → RelationIndex R G →₀ R
  | [] => -Finsupp.single (Sum.inr (0, 0)) 1
  | (point, coefficient) :: tail =>
      -Finsupp.single (Sum.inr (coefficient, point)) 1 + certificateOfEntries tail +
        Finsupp.single
          (Sum.inl (coefficient • point, freeEvaluation (R := R) G (tableOfEntries tail))) 1

private theorem certificateOfEntries_read (entries : List (G × R)) :
    relationMap (R := R) G (certificateOfEntries entries) =
      tableOfEntries entries - Finsupp.single (freeEvaluation (R := R) G (tableOfEntries entries)) 1 := by
  induction entries with
  | nil => simp [certificateOfEntries, tableOfEntries, relation, scalarRelation]
  | cons entry tail previous =>
      rcases entry with ⟨point, coefficient⟩
      simp only [certificateOfEntries, map_add, map_neg, relationMap_single, one_smul,
        relation, scalarRelation, additionRelation, previous, tableOfEntries, List.map_cons,
        List.sum_cons, freeEvaluation_single, Finsupp.smul_single, smul_eq_mul, mul_one]
      abel

/-- Enumerate the table's support and retain the scalar and addition relations for each entry. -/
def finiteTableCertificate (table : G →₀ R) : RelationIndex R G →₀ R :=
  certificateOfEntries (table.support.toList.map fun point => (point, table point))

theorem finiteTableCertificate_read (table : G →₀ R) :
    relationMap (R := R) G (finiteTableCertificate table) =
      table - Finsupp.single (freeEvaluation (R := R) G table) 1 := by
  have source :
      tableOfEntries (table.support.toList.map fun point => (point, table point)) = table := by
    unfold tableOfEntries
    rw [List.map_map]
    exact (Finset.sum_map_toList _ _).trans (Finsupp.sum_single table)
  unfold finiteTableCertificate
  rw [certificateOfEntries_read, source]

theorem relationRange_eq_kernel :
    LinearMap.range (relationMap (R := R) G) = LinearMap.ker (freeEvaluation (R := R) G) := by
  refine le_antisymm (relationRange_le_kernel (R := R) G) ?_
  intro table inKernel
  refine ⟨finiteTableCertificate table + Finsupp.single (Sum.inr (0, 0)) 1, ?_⟩
  rw [map_add, finiteTableCertificate_read, LinearMap.mem_ker.mp inKernel]
  simp [relation, scalarRelation]

end
end ScalarRelationPresentation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
