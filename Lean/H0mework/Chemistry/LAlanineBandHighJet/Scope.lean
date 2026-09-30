import H0mework.Chemistry.LAlanineBandHighJet.Cache
import H0mework.Chemistry.LAlanineRefinementSource.JetIncidence

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open SourceGaussianModel SourceFiniteData SourceJetIncidence

abbrev Scope := Fin 2
def degree (scope : Scope) : Nat := 3+scope.val
def jetCount (scope : Scope) : Nat := if scope.val=0 then 20 else 35

theorem count_le (scope : Scope) : jetCount scope ≤ 35 := by fin_cases scope <;> decide +kernel
 theorem degree_le (scope : Scope) : degree scope ≤ 4 := by unfold degree; omega
 theorem index_iff (scope : Scope) (j : JetIndex) :
    j.val < jetCount scope ↔ jetOrder (jetMulti j) ≤ degree scope := by
  fin_cases scope <;> fin_cases j <;> decide +kernel

noncomputable def jetFor (scope : Scope) (m : MultiIndex) (bound : jetOrder m ≤ degree scope) : Fin (jetCount scope) :=
  ⟨(sourceJetIndex m).val,(index_iff scope (sourceJetIndex m)).mpr (by
    rw [source_jet_recovered m (bound.trans (degree_le scope))]
    exact bound)⟩
 theorem jetFor_recovers (scope : Scope) (m : MultiIndex) (bound : jetOrder m ≤ degree scope) :
    jetMulti (prefixJet (count_le scope) (jetFor scope m bound)) = m :=
  source_jet_recovered m (bound.trans (degree_le scope))
 theorem prefix_degree (scope : Scope) (j : Fin (jetCount scope)) :
    jetOrder (jetMulti (prefixJet (count_le scope) j)) ≤ degree scope :=
  (index_iff scope _).mp j.isLt

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
