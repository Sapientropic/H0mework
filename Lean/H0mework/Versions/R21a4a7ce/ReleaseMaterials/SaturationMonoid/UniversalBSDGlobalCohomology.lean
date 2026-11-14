import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricGalois

/-!
# Universal BSD global cohomological occurrence

For every elliptic curve over `Q`, this module exposes the actual homogeneous continuous
cochain complex of `E(Qbar)` and its degree-one Weil--Chatelet cohomology.  This is the global
cohomological input from which a perfect Selmer realization must be generated; no finite or perfect
replacement is assumed here.
-/

namespace SaturationMonoid
namespace UniversalBSDSelmerCohomology

open CategoryTheory
open CategoryTheory.Limits
open UniversalBSDGeometricGalois

noncomputable section

/-- Canonical zero object used when extending continuous cochains to integer degrees. -/
noncomputable instance topModuleCatHasZeroObject : HasZeroObject (TopModuleCat ℤ) :=
  hasZeroObject_of_hasInitial_object

/-- Canonical binary biproducts used by source-generated mapping cones in `TopModuleCat ℤ`. -/
noncomputable instance topModuleCatHasBinaryBiproducts :
    HasBinaryBiproducts (TopModuleCat ℤ) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Actual source-generated global homogeneous continuous cochains of `E(Qbar)`. -/
abbrev GlobalContinuousCochainComplex (source : RationalEllipticCurveSource) :=
  TopRep.homogeneousCochains (geometricPointTopRep source)

/-- The same actual global cochain occurrence, extended by zero to integer degrees.  This is the
indexing required by the universal Selmer mapping cone; no truncation or perfect replacement is
inserted here. -/
noncomputable abbrev GlobalContinuousCochainComplexZ
    (source : RationalEllipticCurveSource) :=
  (GlobalContinuousCochainComplex source).extend ComplexShape.embeddingUpNat

instance globalContinuousCochainComplexZ_isStrictlyGE
    (source : RationalEllipticCurveSource) :
    CochainComplex.IsStrictlyGE (GlobalContinuousCochainComplexZ source) 0 :=
  inferInstance

/-- Actual global Weil--Chatelet carrier `H¹(G_Q,E(Qbar))`. -/
abbrev WeilChatelet (source : RationalEllipticCurveSource) :=
  continuousCohomology 1 (geometricPointTopRep source)

/-- The degree-one cycle projection of the same actual cohomological occurrence. -/
noncomputable def globalCocycleProjection
    (source : RationalEllipticCurveSource) :
    ContinuousCohomology.cocycles (geometricPointTopRep source) 1 →+
      WeilChatelet source :=
  (ContinuousCohomology.π (geometricPointTopRep source) 1).hom.toAddMonoidHom

@[simp]
theorem globalCocycleProjection_apply
    (source : RationalEllipticCurveSource)
    (z : ContinuousCohomology.cocycles (geometricPointTopRep source) 1) :
    globalCocycleProjection source z =
      (ContinuousCohomology.π (geometricPointTopRep source) 1).hom z :=
  rfl

end

end UniversalBSDSelmerCohomology
end SaturationMonoid
