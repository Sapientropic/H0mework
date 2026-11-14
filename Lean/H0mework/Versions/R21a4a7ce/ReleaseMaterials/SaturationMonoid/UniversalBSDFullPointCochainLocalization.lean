import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDFinitePlaceFullPoint

/-!
# Universal BSD finite-place full-point cochain localization

The source-independent decomposition homomorphism and actual local geometric-point map generate
one homogeneous cochain localization.  Its degree-one map and cocycle projection are literal
readouts of that same chain occurrence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDFinitePlaceFullPoint

open CategoryTheory
open UniversalBSDGeometricGalois

noncomputable section
/-! ## Chain-level occurrence and its literal H¹ readout -/

/-- Actual homogeneous cochain localization at one finite place. -/
noncomputable def fullPointCochainLocalization
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    TopRep.homogeneousCochains (geometricPointTopRep source) ⟶
      TopRep.homogeneousCochains (finiteGeometricPointTopRep source q) :=
  ContinuousCohomology.cochainsMap
    (localToGlobalGaloisHom q)
    (globalGeometricPointToFiniteTopRepHom source q)

/-- Degree-one readout of the literal chain-level localization. -/
noncomputable def fullPointH1LocalizationReadout
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    continuousCohomology 1 (geometricPointTopRep source) ⟶
      continuousCohomology 1 (finiteGeometricPointTopRep source q) :=
  HomologicalComplex.homologyMap
    (fullPointCochainLocalization source q) 1

/-- The degree-one readout is definitionally the existing
`ContinuousCohomology.map` built from the same Galois and coefficient
morphisms. -/
theorem fullPointH1LocalizationReadout_eq_map
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    fullPointH1LocalizationReadout source q =
      ContinuousCohomology.map
        (localToGlobalGaloisHom q)
        (globalGeometricPointToFiniteTopRepHom source q) 1 :=
  rfl

/-- Independent cycle projection reads the same chain occurrence. -/
theorem fullPointCocycleProjection_natural
    (source : RationalEllipticCurveSource) (q : Nat.Primes) :
    ContinuousCohomology.π (geometricPointTopRep source) 1 ≫
        fullPointH1LocalizationReadout source q =
      ContinuousCohomology.cocyclesMap
          (localToGlobalGaloisHom q)
          (globalGeometricPointToFiniteTopRepHom source q) 1 ≫
        ContinuousCohomology.π (finiteGeometricPointTopRep source q) 1 :=
  ContinuousCohomology.π_map
    (localToGlobalGaloisHom q)
    (globalGeometricPointToFiniteTopRepHom source q) 1

end

end UniversalBSDFinitePlaceFullPoint
end SaturationMonoid
