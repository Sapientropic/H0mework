import H0mework.Fock.CopyGraph.NormalInverseSolve

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalCorrection (one clockMean ratio direction strength denominator)
open SourceCopyProgram (Index)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def massMap (bound : Nat) (query : Fin (bound + 1) → Observed) :
    Space (observed (historyPMF bound) query) →L[ℂ] Space (observed (historyPMF bound) query) :=
  ContinuousLinearMap.id ℂ _ - (ratio bound : ℂ) • InnerProductSpace.rankOne ℂ (one bound query) (one bound query)

def solveMap (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    Space (observed (historyPMF bound) query) →L[ℂ] Space (observed (historyPMF bound) query) :=
  massMap bound query - ((strength depth bound index : ℂ) / (denominator depth bound index query : ℂ)) •
    ((InnerProductSpace.rankOne ℂ (direction bound query) (clockMean bound query)).comp (massMap bound query))

def decode (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    SourceJointClockGraph.Carrier →L[ℂ] Space (observed (historyPMF bound) query) :=
  (solveMap depth bound index query).comp (SourceConditionalGraphDecoder.action depth bound index query).adjoint

theorem mass_map_apply (bound : Nat) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) : massMap bound query value = massSolve bound query value := by
  simp only [massMap, massSolve, sub_apply, ContinuousLinearMap.id_apply, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]

theorem solve_map_apply (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) : solveMap depth bound index query value = solve depth bound index query value := by
  simp only [solveMap, solve, sub_apply, smul_apply, ContinuousLinearMap.comp_apply, mass_map_apply,
    InnerProductSpace.rankOne_apply, smul_smul]

variable [MeasurableSingletonClass Observed]

theorem decode_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    (SourceConditionalGraphDecoder.action depth bound index query).adjoint
      (SourceConditionalGraphDecoder.action depth bound index query (decode depth bound index query target)) =
        (SourceConditionalGraphDecoder.action depth bound index query).adjoint target := by
  change (SourceConditionalGraphDecoder.action depth bound index query).adjoint
    (SourceConditionalGraphDecoder.action depth bound index query
      (solveMap depth bound index query ((SourceConditionalGraphDecoder.action depth bound index query).adjoint target))) = _
  rw [solve_map_apply]
  exact solve_equation depth bound index query _

theorem decode_source (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (target : SourceJointClockGraph.Carrier) :
    decode depth bound index query target = SourceConditionalGraphDecoder.decode depth bound index query target := by
  have original := SourceConditionalCorrection.normal depth bound index query target
  rw [map_sub, sub_eq_zero] at original
  have equation := (decode_equation depth bound index query target).trans original
  exact ((SourceConditionalGraphDecoder.action depth bound index query).adjoint_comp_self_injective_iff.mpr
    (SourceConditionalGraphDecoder.source_injective depth bound index query)) equation

theorem decode_linear (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    decode depth bound index query = SourceConditionalGraphDecoder.decode depth bound index query := by
  apply ContinuousLinearMap.ext
  exact decode_source depth bound index query

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
