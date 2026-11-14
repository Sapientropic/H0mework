import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.CochainH1KernelConditionProducer
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDFinitePlaceNTorsionCohomology

/-!
# Universal BSD finite-place H1-kernel condition

This module forgets topology only after the actual finite-place coefficient
map has been generated, then applies the generic `ModuleCat ℤ` H1-kernel
condition producer.  No local-condition or Kummer exactness premise is used.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace UniversalBSDFinitePlaceH1KernelCondition

open CategoryTheory
open CategoryTheory.Limits
open CochainH1KernelConditionProducer
open UniversalBSDGeometricGalois
open UniversalBSDFinitePlaceFullPoint
open UniversalBSDFinitePlaceNTorsionCohomology

noncomputable section

/-- Forget topology from the actual finite-local `E[n]` cochain occurrence. -/
abbrev NTorsionModuleComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (FiniteLocalNTorsionCochainComplex source n q)

/-- Forget topology only after the actual coefficient map has been generated. -/
noncomputable def coefficientModuleMap
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (finiteNTorsionToPointCochainMap source n q)

/-- Generic two-term kernel condition specialized to the actual finite place. -/
noncomputable abbrev ConditionComplex
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :=
  CochainH1KernelConditionProducer.ConditionComplex
    (coefficientModuleMap source n q)

/-- The finite specialization inherits exactness from the generic producer. -/
theorem boundary_exact
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    (conditionShortComplex (coefficientModuleMap source n q)).Exact :=
  CochainH1KernelConditionProducer.boundary_exact
    (coefficientModuleMap source n q)

/-- Canonical finite-place readout `H¹(U) ≅ ker H¹(φ_q)`. -/
noncomputable def h1Iso
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    (ConditionComplex source n q).homology 1 ≅
      kernel (h1Map (coefficientModuleMap source n q)) :=
  CochainH1KernelConditionProducer.conditionH1Iso
    (coefficientModuleMap source n q)

/-- The specialized H¹ map is the actual finite coefficient-map kernel inclusion. -/
theorem h1Map_eq
    (source : RationalEllipticCurveSource) (n : ℕ) (q : Nat.Primes) :
    HomologicalComplex.homologyMap
        (conditionToSource (coefficientModuleMap source n q)) 1 =
      (h1Iso source n q).hom ≫
        kernel.ι (h1Map (coefficientModuleMap source n q)) :=
  CochainH1KernelConditionProducer.conditionH1Map_eq
    (coefficientModuleMap source n q)

end

end UniversalBSDFinitePlaceH1KernelCondition
end SaturationMonoid
