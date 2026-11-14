import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedContractiveInverse

noncomputable section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The actual Neumann inverse preserves the entire closed invariant source face. -/
theorem inverse_mem (action : E →L[𝕜] E) (strict : ‖action‖ < 1) (carrier : ClosedSubmodule 𝕜 E)
    (preserves : Set.MapsTo action carrier carrier) {value : E} (member : value ∈ carrier) :
    (↑(Units.oneSub action strict)⁻¹ : E →L[𝕜] E) value ∈ carrier := by
  have powers (index : Nat) : (action ^ index) value ∈ carrier := by
    induction index with
    | zero => simpa only [pow_zero, one_apply_eq_self] using member
    | succ n previous =>
      rw [pow_succ', mul_apply_eq_comp]
      exact preserves previous
  have source : HasSum (fun n : Nat => (action ^ n) value)
      ((↑(Units.oneSub action strict)⁻¹ : E →L[𝕜] E) value) :=
    (ContinuousLinearMap.apply 𝕜 E value).hasSum (summable_geometric_of_norm_lt_one strict).hasSum
  apply carrier.isClosed.mem_of_tendsto source
  exact Filter.Eventually.of_forall (fun indices => carrier.toSubmodule.sum_mem (fun n _ => powers n))

/-- Subtracting the source contraction reflects membership in the original closed face. -/
theorem sub_mem_iff (action : E →L[𝕜] E) (strict : ‖action‖ < 1) (carrier : ClosedSubmodule 𝕜 E)
    (preserves : Set.MapsTo action carrier carrier) (value : E) :
    value - action value ∈ carrier ↔ value ∈ carrier := by
  constructor
  · intro kept
    have read := inverse_mem action strict carrier preserves kept
    have restored : (↑(Units.oneSub action strict)⁻¹ : E →L[𝕜] E) (value - action value) = value :=
      congrArg (fun f : E →L[𝕜] E => f value) (Units.oneSub action strict).inv_mul
    exact restored ▸ read
  · intro kept
    exact carrier.toSubmodule.sub_mem kept (preserves kept)

end
end SourceGeneratedContractiveInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
