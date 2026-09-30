import H0mework.Fock.CopyGraph.Graph.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
open scoped InnerProductSpace
noncomputable section

theorem orthogonal (depth : Nat) (index : Index depth) :
    OrthogonalFamily ℂ (fun _ : Nat => ℂ) (fun coordinate => place (indexAfter depth index coordinate)) := by
  intro left right distinct a b
  change ⟪lp.single (E := fun _ : Nat => ℂ) 2 (indexAfter depth index left) a,
    lp.single (E := fun _ : Nat => ℂ) 2 (indexAfter depth index right) b⟫_ℂ = 0
  rw [lp.inner_single_left]
  have separate : indexAfter depth index left ≠ indexAfter depth index right :=
    fun same => distinct (index_injective depth index same)
  simp [lp.single_apply, separate]

def hilbertAction (depth : Nat) (index : Index depth) : H →ₗᵢ[ℂ] H := (orthogonal depth index).linearIsometry

theorem hilbert_single (depth : Nat) (index : Index depth) (coordinate : Nat) (scalar : ℂ) :
    hilbertAction depth index (lp.single 2 coordinate scalar) = lp.single 2 (indexAfter depth index coordinate) scalar :=
  (orthogonal depth index).linearIsometry_apply_single scalar

theorem hilbert_basis (depth : Nat) (index : Index depth) (coordinate : Nat) :
    hilbertAction depth index (basis coordinate) = basis (indexAfter depth index coordinate) :=
  hilbert_single depth index coordinate 1

theorem hilbert_source (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    hilbertAction depth index (readWord word) = readWord (complexAction depth index word) := by
  change (hilbertAction depth index).toLinearMap (Finsupp.linearCombination ℂ basis word) =
    Finsupp.linearCombination ℂ basis (Finsupp.mapDomain (indexAfter depth index) word)
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_mapDomain]
  congr 1
  exact congrArg (Finsupp.linearCombination ℂ) (funext (hilbert_basis depth index))

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
