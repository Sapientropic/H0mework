import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Generic exterior determinant-line carrier

This file contains only the basis-free exterior-power shapes used by the
constructive root kernels.  It is deliberately domain-neutral: no BSD, zeta,
Selmer, analytic, or arithmetic occurrence is imported here.

The source-generated perfectness faces decide when these carriers are
eligible.  A determinant line or its rank-one fact is therefore a readout of
an already generated finite/perfect face, never an unconditional promise about
an arbitrary source carrier.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedExteriorDeterminantLine

open scoped TensorProduct

noncomputable section

/-! The top exterior line of a finite-dimensional vector space. -/
abbrev TopExteriorLine (K : Type*) (M : Type*) [Field K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] :=
  ⋀[K]^(Module.finrank K M) M

theorem topExteriorLine_finrank
    (K : Type*) (M : Type*) [Field K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] :
    Module.finrank K (TopExteriorLine K M) = 1 := by
  rw [TopExteriorLine, exteriorPower.finrank_eq]
  simp

/-! The alternating determinant carrier for amplitudes `[0,2]` and `[0,3]`.
These are shapes only; no determinant element or frame is installed here. -/
abbrev ThreeTermDeterminantLine
    (K : Type*) (C0 C1 C2 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2] :=
  (TopExteriorLine K C0 ⊗[K]
      (Module.Dual K (TopExteriorLine K C1))) ⊗[K]
    TopExteriorLine K C2

local instance threeTermDeterminantLineAddCommGroup
    (K : Type*) (C0 C1 C2 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2] :
    AddCommGroup (ThreeTermDeterminantLine K C0 C1 C2) :=
  Module.addCommMonoidToAddCommGroup K

theorem threeTermDeterminantLine_finrank
    (K : Type*) (C0 C1 C2 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2] :
    Module.finrank K (ThreeTermDeterminantLine K C0 C1 C2) = 1 := by
  simp only [ThreeTermDeterminantLine, Module.finrank_tensorProduct,
    topExteriorLine_finrank, Subspace.dual_finrank_eq, one_mul]

abbrev FourTermDeterminantLine
    (K : Type*) (C0 C1 C2 C3 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2]
    [AddCommGroup C3] [Module K C3] [FiniteDimensional K C3] :=
  ((TopExteriorLine K C0 ⊗[K]
      (Module.Dual K (TopExteriorLine K C1))) ⊗[K]
    TopExteriorLine K C2) ⊗[K]
      (Module.Dual K (TopExteriorLine K C3))

local instance fourTermDeterminantLineAddCommGroup
    (K : Type*) (C0 C1 C2 C3 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2]
    [AddCommGroup C3] [Module K C3] [FiniteDimensional K C3] :
    AddCommGroup (FourTermDeterminantLine K C0 C1 C2 C3) :=
  Module.addCommMonoidToAddCommGroup K

theorem fourTermDeterminantLine_finrank
    (K : Type*) (C0 C1 C2 C3 : Type*) [Field K]
    [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
    [AddCommGroup C1] [Module K C1] [FiniteDimensional K C1]
    [AddCommGroup C2] [Module K C2] [FiniteDimensional K C2]
    [AddCommGroup C3] [Module K C3] [FiniteDimensional K C3] :
    Module.finrank K (FourTermDeterminantLine K C0 C1 C2 C3) = 1 := by
  simp only [FourTermDeterminantLine, Module.finrank_tensorProduct,
    topExteriorLine_finrank, Subspace.dual_finrank_eq, one_mul]

end

end RootGeneratedExteriorDeterminantLine
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
