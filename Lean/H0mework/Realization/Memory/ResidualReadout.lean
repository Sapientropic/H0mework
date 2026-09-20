import H0mework.Realization.Residual.TruthFormula
import H0mework.Realization.Memory.StorageDistinction

/-!
# Residual information-memory readout kernel

The root adapter needs only the early information/memory ontology, not the
later SAT/Hamiltonian projection chain.  This module keeps that readout on a
narrow dependency surface while preserving the established public names.
It defines no source, event, authority, or lifecycle outcome.
-/

noncomputable section

namespace SaturationMonoid
namespace ResidualProjection

open AffineRelaxation

/-- The information readout of a residual transport is its forced trace. -/
def residualInformationReadout
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r : E) : E :=
  linearResidualTrace keep r

/-- The residual-memory atom: a trace was actually produced. -/
inductive ResidualMemoryAtom where
  | traceProduced
  deriving DecidableEq, Repr

/-- Residual memory is recollectable trace production on the residual carrier. -/
def residualMemoryAct
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) :
    RecollectionAct E ResidualMemoryAtom where
  fires := fun r atom =>
    match atom with
    | ResidualMemoryAtom.traceProduced =>
        residualInformationReadout keep r ≠ 0

/-- Memory potential on the residual carrier is exactly nonzero information
trace. -/
theorem residualMemoryPotential_iff_informationTrace_nonzero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (r : E) :
    RecollectableMemoryPotential (residualMemoryAct keep) r ↔
      residualInformationReadout keep r ≠ 0 := by
  constructor
  · rintro ⟨atom, hfire⟩
    cases atom
    exact hfire
  · intro htrace
    exact ⟨ResidualMemoryAtom.traceProduced, htrace⟩

end ResidualProjection
end SaturationMonoid
