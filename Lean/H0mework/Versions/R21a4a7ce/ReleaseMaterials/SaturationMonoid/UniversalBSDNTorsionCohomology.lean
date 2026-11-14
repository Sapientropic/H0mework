import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricNTorsion
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGlobalCohomology

/-!
# Universal BSD finite-torsion cochain occurrence

For every elliptic curve over `Q` and every natural number `n`, this module constructs the
actual homogeneous continuous cochains of `E[n](Qbar)`, the coefficient-inclusion chain map to
the full geometric-point cochains, and its degree-one Weil--Chatelet readout.  Both complexes and
the map are also extended by zero to integer degrees for later Selmer mapping-cone assembly.
-/

namespace SaturationMonoid
namespace UniversalBSDNTorsionCohomology

open CategoryTheory
open UniversalBSDGeometricGalois
open UniversalBSDGeometricNTorsion
open UniversalBSDSelmerCohomology

noncomputable section

/-- Actual global homogeneous continuous cochains with coefficients in `E[n](Qbar)`. -/
abbrev NTorsionContinuousCochainComplex
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  TopRep.homogeneousCochains (geometricNTorsionIntTopRep source n)

/-- Actual global `H¹(G_Q,E[n])`. -/
abbrev NTorsionGaloisH1
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  continuousCohomology 1 (geometricNTorsionIntTopRep source n)

/-- The coefficient inclusion `E[n] → E(Qbar)` on the actual homogeneous cochain occurrences. -/
noncomputable def nTorsionToPointCochainMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    NTorsionContinuousCochainComplex source n ⟶
      GlobalContinuousCochainComplex source :=
  ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ))
    (geometricNTorsionToGeometricPointTopRepHom source n)

/-- Cochain transition induced by multiplication `E[a*n] → E[n]`. -/
noncomputable def nTorsionTransitionCochainMap
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    NTorsionContinuousCochainComplex source (a * n) ⟶
      NTorsionContinuousCochainComplex source n :=
  ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ))
    (geometricNTorsionTransitionTopRepHom source a n)

/-- The same torsion transition extended by zero to integer degrees. -/
noncomputable def nTorsionTransitionCochainMapZ
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    (NTorsionContinuousCochainComplex source (a * n)).extend
        ComplexShape.embeddingUpNat ⟶
      (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap (nTorsionTransitionCochainMap source a n)
    ComplexShape.embeddingUpNat

/-- The same coefficient-inclusion chain map, extended by zero to integer degrees. -/
noncomputable def nTorsionToPointCochainMapZ
    (source : RationalEllipticCurveSource) (n : ℕ) :
    (NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat ⟶
      GlobalContinuousCochainComplexZ source :=
  HomologicalComplex.extendMap (nTorsionToPointCochainMap source n)
    ComplexShape.embeddingUpNat

instance nTorsionContinuousCochainComplexZ_isStrictlyGE
    (source : RationalEllipticCurveSource) (n : ℕ) :
    CochainComplex.IsStrictlyGE
      ((NTorsionContinuousCochainComplex source n).extend
        ComplexShape.embeddingUpNat) 0 :=
  inferInstance

/-- Degree-one readout of the actual coefficient-inclusion chain map. -/
noncomputable def nTorsionH1ToWeilChatelet
    (source : RationalEllipticCurveSource) (n : ℕ) :
    NTorsionGaloisH1 source n →+ WeilChatelet source :=
  (ContinuousCohomology.map
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ))
    (geometricNTorsionToGeometricPointTopRepHom source n) 1).hom
      |>.toLinearMap.toAddMonoidHom

/-- The H¹ map is literally the homology readout of the same source-generated cochain map. -/
theorem nTorsionH1Readout_eq_homologyMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    ContinuousCohomology.map
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup ℚ))
        (geometricNTorsionToGeometricPointTopRepHom source n) 1 =
      HomologicalComplex.homologyMap
        (nTorsionToPointCochainMap source n) 1 :=
  rfl

end

end UniversalBSDNTorsionCohomology
end SaturationMonoid
