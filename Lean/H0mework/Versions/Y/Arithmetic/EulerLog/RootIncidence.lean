import H0mework.Versions.Y.Arithmetic.EulerDerived.EndpointCokernelState
import H0mework.Versions.Y.Arithmetic.EulerLog.ExponentCofinalAction
import H0mework.Versions.Y.Arithmetic.EulerLog.GlobalGerm

/-!
# Root incidence of the arithmetic all-place faces

The Euler-log coefficients and the global endpoint cokernel class are sibling
dependent faces of the literal factorization occurrence.  The cofinal Euler
action is generated from the same runtime authority.  This file records those
exact projection identities; it does not invent a map between the two Euler
carriers.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlaceEulerLogIncidence

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockEndpointBoundaryCokernelGlobalState
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization
open CanonicalUnitArithmeticPrimeExponentEulerCofinalAction
open CanonicalUnitArithmeticRuntimeCofinalEuler
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open RootedAccountedUnfolding

noncomputable section

/-- The logarithmic coefficient face and endpoint class forget to the same
factorization occurrence, not merely isomorphic scalar shadows. -/
theorem globalEulerLog_endpointBoundary_same_factorizationOccurrence :
    globalEulerLogOccurrence.map (fun payload => payload.1.1) =
      globalEndpointBoundaryCokernelOccurrence.map Prod.fst := by
  rw [globalEndpointBoundaryCokernelOccurrence_projects]
  calc
    globalEulerLogOccurrence.map (fun payload => payload.1.1) =
        (globalEulerLogOccurrence.map Sigma.fst).map Prod.fst := by
      rw [RootedAccountedUnfolding.map_map]
      congr 1
    _ = globalGermOccurrence.map Prod.fst := by
      rw [globalEulerLogOccurrence_projects]
    _ = seedOccurrence := globalGermOccurrence_projects

/-- The same two faces and the runtime cofinal Euler action all forget to the
literal depth-zero runtime authority.  No cross-carrier intertwiner is claimed
here; that is a separate mathematical square. -/
theorem globalEulerLog_endpoint_cofinalAction_same_runtime :
    globalEulerLogOccurrence.map (fun payload => payload.1.1.1) =
        globalEndpointBoundaryCokernelOccurrence.map
          (fun payload => payload.1.1) ∧
      globalEulerLogOccurrence.map (fun payload => payload.1.1.1) =
        dependentEulerActionOccurrence.map (fun payload => payload.1.1) := by
  constructor
  · apply congrArg (fun occurrence => occurrence.map Sigma.fst)
      globalEulerLog_endpointBoundary_same_factorizationOccurrence
  · calc
      globalEulerLogOccurrence.map (fun payload => payload.1.1.1) =
          (seedOccurrence.map Sigma.fst) := by
        rw [← globalGermOccurrence_projects,
          ← globalEulerLogOccurrence_projects,
          RootedAccountedUnfolding.map_map,
          RootedAccountedUnfolding.map_map]
        congr 1
      _ = dependentEulerActionOccurrence.map (fun payload => payload.1.1) := by
        symm
        calc
          dependentEulerActionOccurrence.map (fun payload => payload.1.1) =
              (dependentEulerActionOccurrence.map Prod.fst).map Prod.fst := by
            rw [RootedAccountedUnfolding.map_map]
            congr 1
          _ = runtimeCofinalLimitOccurrence.map Prod.fst := by
            rw [globalEulerAction_preserves_runtime_root]
          _ = runtimeAuthorityOccurrence :=
            runtimeCofinalLimitOccurrence_projects
          _ = seedOccurrence.map Sigma.fst := by
            rfl

end
end AllPlaceEulerLogIncidence
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
