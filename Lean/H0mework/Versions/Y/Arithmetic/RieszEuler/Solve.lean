import H0mework.Versions.Y.Arithmetic.RieszEuler.SourceWard

/-! The two actual Ward equations are solved by the original source inverse. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler

open Complex Constructor
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem sourceEuler_equation (coordinate : BurnolCompletedMellinCoordinate) :
    burnolMeanZeroOneMinusSquare
      (sourceEuler coordinate - (star coordinate.value - 1 / 2) • burnolRieszSingleFourierSource coordinate) =
      Kernel.A coordinate • Response.eta -
        Kernel.beta coordinate • burnolMeanZeroTruncatedFourier Response.eta := by
  have first := congrArg burnolMeanZeroTruncatedFourier (original_source_meanZero_ward coordinate)
  rw [map_add, map_smul] at first
  have square :
      burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (sourceEuler coordinate)) =
      Kernel.beta coordinate • burnolMeanZeroTruncatedFourier Response.eta -
        burnolMeanZeroTruncatedFourier (returnEuler coordinate) :=
    eq_sub_of_add_eq ((add_comm _ _).trans first)
  have second := return_meanZero_ward coordinate
  have endpoints : burnolRieszReturnRaw coordinate (-q) = burnolRieszReturnRaw coordinate q :=
    burnolRieszSingleFourierReturnRaw_endpoints coordinate
  rw [endpoints, ← smul_add] at second
  change secondEuler coordinate + burnolMeanZeroTruncatedFourier (returnEuler coordinate) =
    burnolRieszReturnRaw coordinate q • Response.eta at second
  have returned := eq_sub_of_add_eq second
  rw [map_sub, map_smul, burnolRieszSingleFourierSource_equation]
  change (sourceEuler coordinate -
    burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (sourceEuler coordinate))) -
      (star coordinate.value - 1 / 2) •
        burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) = _
  rw [square, sourceEuler_def, returned]
  unfold Kernel.A
  module

private theorem response_v_equation :
    burnolMeanZeroOneMinusSquare Response.v = burnolMeanZeroTruncatedFourier Response.eta := by
  have source := congrArg burnolMeanZeroTruncatedFourier Response.u_equation
  change burnolMeanZeroTruncatedFourier
    (Response.u - burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier Response.u)) = _ at source
  rw [map_sub] at source
  exact source

theorem sourceEuler_eq (coordinate : BurnolCompletedMellinCoordinate) :
    sourceEuler coordinate =
      (star coordinate.value - 1 / 2) • burnolRieszSingleFourierSource coordinate +
        Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v := by
  have candidate : burnolMeanZeroOneMinusSquare
      (Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v) =
      Kernel.A coordinate • Response.eta -
        Kernel.beta coordinate • burnolMeanZeroTruncatedFourier Response.eta := by
    rw [map_sub, map_smul, map_smul, Response.u_equation, response_v_equation]
  have solved := congrArg burnolMeanZeroBlockInverse ((sourceEuler_equation coordinate).trans candidate.symm)
  have inverseLeft : burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare = 1 :=
    Ring.inverse_mul_cancel _ burnolMeanZeroOneMinusSquare_isUnit
  change (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare)
      (sourceEuler coordinate - (star coordinate.value - 1 / 2) • burnolRieszSingleFourierSource coordinate) =
    (burnolMeanZeroBlockInverse * burnolMeanZeroOneMinusSquare)
      (Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v) at solved
  rw [inverseLeft] at solved
  change sourceEuler coordinate - (star coordinate.value - 1 / 2) • burnolRieszSingleFourierSource coordinate =
    Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v at solved
  calc
    _ = (Kernel.A coordinate • Response.u - Kernel.beta coordinate • Response.v) +
        (star coordinate.value - 1 / 2) • burnolRieszSingleFourierSource coordinate :=
      sub_eq_iff_eq_add.mp solved
    _ = _ := by module

theorem returnEuler_eq (coordinate : BurnolCompletedMellinCoordinate) :
    returnEuler coordinate =
      -(star coordinate.value - 1 / 2) •
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) -
      Kernel.A coordinate • Response.v + Kernel.beta coordinate • Response.u := by
  have generated := eq_sub_of_add_eq (original_source_meanZero_ward coordinate)
  have response : Response.eta = Response.u - burnolMeanZeroTruncatedFourier Response.v :=
    Response.source_pair_equation.symm
  rw [generated, sourceEuler_eq, map_sub, map_add, map_smul, map_smul, map_smul, response]
  change Kernel.beta coordinate • (Response.u - burnolMeanZeroTruncatedFourier Response.v) -
    ((star coordinate.value - 1 / 2) •
        burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) +
      Kernel.A coordinate • Response.v -
      Kernel.beta coordinate • burnolMeanZeroTruncatedFourier Response.v) = _
  module

end
end OriginalRieszSource.Euler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
