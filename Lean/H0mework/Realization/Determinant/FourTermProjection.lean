import Mathlib.LinearAlgebra.Dual.Basis
import H0mework.Realization.Determinant.ExactGluing

/-!
# Root-generated bounded perfect-complex determinant projection

An actual four-term integral cochain presentation stores only its three
differentials and the two `d ∘ d = 0` laws.  A generated finite-free
calculation receipt promotes it to a perfect presentation.  The generic
projection then forms the alternating graded integral determinant line,
its parity and intrinsic unit torsor.  Scalar extension reads the existing
`FourTermDeterminantLine`; no determinant element, frame, basis,
trivialization, cohomology cardinality or regulator is supplied.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace PerfectComplexDeterminantProjection

open RootGeneratedExteriorDeterminantLine
open GradedIntegralDeterminantLine
open LatticeDeterminantTrivialization
open scoped TensorProduct

attribute [local instance 2000] TensorProduct.leftModule

universe t u₀ u₁ u₂ u₃ w

noncomputable section

/-- Actual amplitude-`[0,3]` integral cochain presentation. -/
structure FourTermIntegralComplexAt
    (C₀ : Type u₀) (C₁ : Type u₁) (C₂ : Type u₂) (C₃ : Type u₃)
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup C₂] [AddCommGroup C₃] where
  d₀ : C₀ →ₗ[ℤ] C₁
  d₁ : C₁ →ₗ[ℤ] C₂
  d₂ : C₂ →ₗ[ℤ] C₃
  d₁_comp_d₀ : d₁.comp d₀ = 0
  d₂_comp_d₁ : d₂.comp d₁ = 0

/-- Root-owned actual perfect-presentation candidate. -/
structure RootGeneratedFourTermPerfectDeterminantProjectionAt
    {Root : Type w}
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup C₂] [AddCommGroup C₃]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (complexOccurrence : RootedAccountedUnfolding
      (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)) : Type where
  private mk ::

namespace RootGeneratedFourTermPerfectDeterminantProjectionAt

variable {Root : Type w}
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [AddCommGroup C₀] [AddCommGroup C₁]
variable [AddCommGroup C₂] [AddCommGroup C₃]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {complexOccurrence : RootedAccountedUnfolding
  (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)}

def generate : RootGeneratedFourTermPerfectDeterminantProjectionAt
    rootOccurrence complexOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFourTermPerfectDeterminantProjectionAt
      rootOccurrence complexOccurrence) : RootedAccountedUnfolding Root :=
  rootOccurrence

def actualComplex
    (_face : RootGeneratedFourTermPerfectDeterminantProjectionAt
      rootOccurrence complexOccurrence) :
    FourTermIntegralComplexAt C₀ C₁ C₂ C₃ :=
  complexOccurrence.root

end RootGeneratedFourTermPerfectDeterminantProjectionAt

/-- Generated perfectness receipt. -/
structure RootGeneratedFourTermPerfectCalculationAt
    {Root : Type w}
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup C₂] [AddCommGroup C₃]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {complexOccurrence : RootedAccountedUnfolding
      (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)}
    (face : RootGeneratedFourTermPerfectDeterminantProjectionAt
      rootOccurrence complexOccurrence) : Prop where
  free₀ : Module.Free ℤ C₀
  finite₀ : Module.Finite ℤ C₀
  free₁ : Module.Free ℤ C₁
  finite₁ : Module.Finite ℤ C₁
  free₂ : Module.Free ℤ C₂
  finite₂ : Module.Finite ℤ C₂
  free₃ : Module.Free ℤ C₃
  finite₃ : Module.Finite ℤ C₃

namespace RootGeneratedFourTermPerfectCalculationAt

variable {Root : Type w}
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [AddCommGroup C₀] [AddCommGroup C₁]
variable [AddCommGroup C₂] [AddCommGroup C₃]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {complexOccurrence : RootedAccountedUnfolding
  (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)}
variable {face : RootGeneratedFourTermPerfectDeterminantProjectionAt
  rootOccurrence complexOccurrence}

theorem generate
    (free₀ : Module.Free ℤ C₀) (finite₀ : Module.Finite ℤ C₀)
    (free₁ : Module.Free ℤ C₁) (finite₁ : Module.Finite ℤ C₁)
    (free₂ : Module.Free ℤ C₂) (finite₂ : Module.Finite ℤ C₂)
    (free₃ : Module.Free ℤ C₃) (finite₃ : Module.Finite ℤ C₃) :
    RootGeneratedFourTermPerfectCalculationAt face :=
  ⟨free₀, finite₀, free₁, finite₁,
    free₂, finite₂, free₃, finite₃⟩

end RootGeneratedFourTermPerfectCalculationAt

/-- Alternating integral determinant line of amplitude `[0,3]`. -/
abbrev IntegralFourTermDeterminantLine
    (C₀ : Type u₀) (C₁ : Type u₁) (C₂ : Type u₂) (C₃ : Type u₃)
    [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
    [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
    [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
    [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃] :=
  ((IntegralTopExteriorLine C₀ ⊗[ℤ]
      Module.Dual ℤ (IntegralTopExteriorLine C₁)) ⊗[ℤ]
    IntegralTopExteriorLine C₂) ⊗[ℤ]
      Module.Dual ℤ (IntegralTopExteriorLine C₃)

/-- Internal basis used only to prove that the alternating line is rank one. -/
noncomputable def integralFourTermLineBasis
    (C₀ : Type u₀) (C₁ : Type u₁) (C₂ : Type u₂) (C₃ : Type u₃)
    [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
    [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
    [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
    [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃] :
    Module.Basis (((Unit × Unit) × Unit) × Unit) ℤ
      (IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃) :=
  let frame₀ : IntegralDeterminantFrame (IntegralTopExteriorLine C₀) :=
    internalRankOneFrame (integralTopExteriorLine_finrank C₀)
  let frame₁ : IntegralDeterminantFrame (IntegralTopExteriorLine C₁) :=
    internalRankOneFrame (integralTopExteriorLine_finrank C₁)
  let frame₂ : IntegralDeterminantFrame (IntegralTopExteriorLine C₂) :=
    internalRankOneFrame (integralTopExteriorLine_finrank C₂)
  let frame₃ : IntegralDeterminantFrame (IntegralTopExteriorLine C₃) :=
    internalRankOneFrame (integralTopExteriorLine_finrank C₃)
  ((frame₀.tensorProduct frame₁.dualBasis).tensorProduct frame₂
    ).tensorProduct frame₃.dualBasis

theorem integralFourTermDeterminantLine_finrank
    (C₀ : Type u₀) (C₁ : Type u₁) (C₂ : Type u₂) (C₃ : Type u₃)
    [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
    [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
    [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
    [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃] :
    Module.finrank ℤ
      (IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃) = 1 :=
  calc
    _ = Fintype.card (((Unit × Unit) × Unit) × Unit) :=
      Module.finrank_eq_card_basis
        (integralFourTermLineBasis C₀ C₁ C₂ C₃)
    _ = 1 := by simp

/-- Total `ℤ/2` grading of the four-term determinant line. -/
def integralFourTermParity
    (C₀ : Type u₀) (C₁ : Type u₁) (C₂ : Type u₂) (C₃ : Type u₃)
    [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
    [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
    [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
    [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃] : Fin 2 :=
  ⟨(Module.finrank ℤ C₀ + Module.finrank ℤ C₁ +
      Module.finrank ℤ C₂ + Module.finrank ℤ C₃) % 2,
    Nat.mod_lt _ (by norm_num)⟩

structure RootGeneratedFourTermPerfectDeterminantStateAt
    {Root : Type w}
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup C₂] [AddCommGroup C₃]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {complexOccurrence : RootedAccountedUnfolding
      (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)}
    (face : RootGeneratedFourTermPerfectDeterminantProjectionAt
      rootOccurrence complexOccurrence)
    (calculation : RootGeneratedFourTermPerfectCalculationAt face) : Type where
  private mk ::

namespace RootGeneratedFourTermPerfectDeterminantStateAt

variable {Root : Type w}
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable [AddCommGroup C₀] [AddCommGroup C₁]
variable [AddCommGroup C₂] [AddCommGroup C₃]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {complexOccurrence : RootedAccountedUnfolding
  (FourTermIntegralComplexAt C₀ C₁ C₂ C₃)}
variable {face : RootGeneratedFourTermPerfectDeterminantProjectionAt
  rootOccurrence complexOccurrence}
variable {calculation : RootGeneratedFourTermPerfectCalculationAt face}

def realize : RootGeneratedFourTermPerfectDeterminantStateAt face calculation :=
  ⟨⟩

abbrev integralLine
    (_state : RootGeneratedFourTermPerfectDeterminantStateAt face calculation) :=
  let _ : Module.Free ℤ C₀ := calculation.free₀
  let _ : Module.Finite ℤ C₀ := calculation.finite₀
  let _ : Module.Free ℤ C₁ := calculation.free₁
  let _ : Module.Finite ℤ C₁ := calculation.finite₁
  let _ : Module.Free ℤ C₂ := calculation.free₂
  let _ : Module.Finite ℤ C₂ := calculation.finite₂
  let _ : Module.Free ℤ C₃ := calculation.free₃
  let _ : Module.Finite ℤ C₃ := calculation.finite₃
  IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃

def parity
    (_state : RootGeneratedFourTermPerfectDeterminantStateAt face calculation) :
    Fin 2 := by
  let _ : Module.Free ℤ C₀ := calculation.free₀
  let _ : Module.Finite ℤ C₀ := calculation.finite₀
  let _ : Module.Free ℤ C₁ := calculation.free₁
  let _ : Module.Finite ℤ C₁ := calculation.finite₁
  let _ : Module.Free ℤ C₂ := calculation.free₂
  let _ : Module.Finite ℤ C₂ := calculation.finite₂
  let _ : Module.Free ℤ C₃ := calculation.free₃
  let _ : Module.Finite ℤ C₃ := calculation.finite₃
  exact integralFourTermParity C₀ C₁ C₂ C₃

/-- Canonical unit torsor of the alternating integral determinant line. -/
noncomputable def unitTorsor
    (_state : RootGeneratedFourTermPerfectDeterminantStateAt face calculation) :
    CanonicalIntegralUnitTorsor (by
      let _ : Module.Free ℤ C₀ := calculation.free₀
      let _ : Module.Finite ℤ C₀ := calculation.finite₀
      let _ : Module.Free ℤ C₁ := calculation.free₁
      let _ : Module.Finite ℤ C₁ := calculation.finite₁
      let _ : Module.Free ℤ C₂ := calculation.free₂
      let _ : Module.Finite ℤ C₂ := calculation.finite₂
      let _ : Module.Free ℤ C₃ := calculation.free₃
      let _ : Module.Finite ℤ C₃ := calculation.finite₃
      exact IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃) := by
  let _ : Module.Free ℤ C₀ := calculation.free₀
  let _ : Module.Finite ℤ C₀ := calculation.finite₀
  let _ : Module.Free ℤ C₁ := calculation.free₁
  let _ : Module.Finite ℤ C₁ := calculation.finite₁
  let _ : Module.Free ℤ C₂ := calculation.free₂
  let _ : Module.Finite ℤ C₂ := calculation.finite₂
  let _ : Module.Free ℤ C₃ := calculation.free₃
  let _ : Module.Finite ℤ C₃ := calculation.finite₃
  let lineBasis := integralFourTermLineBasis C₀ C₁ C₂ C₃
  let _ : Module.Free ℤ
      (IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃) :=
    Module.Free.of_basis lineBasis
  let _ : Module.Finite ℤ
      (IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃) :=
    Module.Finite.of_basis lineBasis
  exact canonicalIntegralUnitTorsor
    (integralFourTermDeterminantLine_finrank C₀ C₁ C₂ C₃)

/-- Scalar/base-change realization shadow in the existing BSD determinant
kernel. -/
abbrev scalarLine
    (K : Type t) [Field K] [Algebra ℤ K]
    (_state : RootGeneratedFourTermPerfectDeterminantStateAt face calculation) :=
  let _ : Module.Free ℤ C₀ := calculation.free₀
  let _ : Module.Finite ℤ C₀ := calculation.finite₀
  let _ : Module.Free ℤ C₁ := calculation.free₁
  let _ : Module.Finite ℤ C₁ := calculation.finite₁
  let _ : Module.Free ℤ C₂ := calculation.free₂
  let _ : Module.Finite ℤ C₂ := calculation.finite₂
  let _ : Module.Free ℤ C₃ := calculation.free₃
  let _ : Module.Finite ℤ C₃ := calculation.finite₃
  FourTermDeterminantLine K
    (IntegralScalarExtension K C₀) (IntegralScalarExtension K C₁)
    (IntegralScalarExtension K C₂) (IntegralScalarExtension K C₃)

theorem scalarLine_finrank
    (K : Type t) [Field K] [Algebra ℤ K]
    (state : RootGeneratedFourTermPerfectDeterminantStateAt face calculation) :
    Module.finrank K (state.scalarLine K) = 1 := by
  let _ : Module.Free ℤ C₀ := calculation.free₀
  let _ : Module.Finite ℤ C₀ := calculation.finite₀
  let _ : Module.Free ℤ C₁ := calculation.free₁
  let _ : Module.Finite ℤ C₁ := calculation.finite₁
  let _ : Module.Free ℤ C₂ := calculation.free₂
  let _ : Module.Finite ℤ C₂ := calculation.finite₂
  let _ : Module.Free ℤ C₃ := calculation.free₃
  let _ : Module.Finite ℤ C₃ := calculation.finite₃
  exact fourTermDeterminantLine_finrank K _ _ _ _

end RootGeneratedFourTermPerfectDeterminantStateAt

/-! ## Termwise naturality -/

/-- Actual chain equivalence between two four-term presentations. -/
structure FourTermIntegralComplexEquivAt
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} {D₃ : Type u₃}
    [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup C₂] [AddCommGroup C₃]
    [AddCommGroup D₀] [AddCommGroup D₁]
    [AddCommGroup D₂] [AddCommGroup D₃]
    (source : FourTermIntegralComplexAt C₀ C₁ C₂ C₃)
    (target : FourTermIntegralComplexAt D₀ D₁ D₂ D₃) where
  e₀ : C₀ ≃ₗ[ℤ] D₀
  e₁ : C₁ ≃ₗ[ℤ] D₁
  e₂ : C₂ ≃ₗ[ℤ] D₂
  e₃ : C₃ ≃ₗ[ℤ] D₃
  commute₀ : e₁.toLinearMap.comp source.d₀ =
    target.d₀.comp e₀.toLinearMap
  commute₁ : e₂.toLinearMap.comp source.d₁ =
    target.d₁.comp e₁.toLinearMap
  commute₂ : e₃.toLinearMap.comp source.d₂ =
    target.d₂.comp e₂.toLinearMap

namespace FourTermIntegralComplexEquivAt

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} {D₃ : Type u₃}
variable [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
variable [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
variable [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
variable [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃]
variable [AddCommGroup D₀] [Module.Free ℤ D₀] [Module.Finite ℤ D₀]
variable [AddCommGroup D₁] [Module.Free ℤ D₁] [Module.Finite ℤ D₁]
variable [AddCommGroup D₂] [Module.Free ℤ D₂] [Module.Finite ℤ D₂]
variable [AddCommGroup D₃] [Module.Free ℤ D₃] [Module.Finite ℤ D₃]
variable {source : FourTermIntegralComplexAt C₀ C₁ C₂ C₃}
variable {target : FourTermIntegralComplexAt D₀ D₁ D₂ D₃}

/-- Chain equivalence generates the alternating integral determinant-line
transport, with odd degrees dualized contravariantly. -/
noncomputable def determinantLineTransport
    (equivalence : FourTermIntegralComplexEquivAt source target) :
    IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃ ≃ₗ[ℤ]
      IntegralFourTermDeterminantLine D₀ D₁ D₂ D₃ :=
  let line₀ := topExteriorLineEquiv equivalence.e₀
  let line₁ := topExteriorLineEquiv equivalence.e₁
  let line₂ := topExteriorLineEquiv equivalence.e₂
  let line₃ := topExteriorLineEquiv equivalence.e₃
  let first := TensorProduct.AlgebraTensorModule.congr line₀
    line₁.symm.dualMap
  let second := TensorProduct.AlgebraTensorModule.congr first line₂
  TensorProduct.AlgebraTensorModule.congr second line₃.symm.dualMap

end FourTermIntegralComplexEquivAt

/-- Root-owned naturality face. -/
structure RootGeneratedFourTermDeterminantNaturalityAt
    {Root : Type w}
    {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
    {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} {D₃ : Type u₃}
    [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
    [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
    [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
    [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃]
    [AddCommGroup D₀] [Module.Free ℤ D₀] [Module.Finite ℤ D₀]
    [AddCommGroup D₁] [Module.Free ℤ D₁] [Module.Finite ℤ D₁]
    [AddCommGroup D₂] [Module.Free ℤ D₂] [Module.Finite ℤ D₂]
    [AddCommGroup D₃] [Module.Free ℤ D₃] [Module.Finite ℤ D₃]
    {source : FourTermIntegralComplexAt C₀ C₁ C₂ C₃}
    {target : FourTermIntegralComplexAt D₀ D₁ D₂ D₃}
    (rootOccurrence : RootedAccountedUnfolding Root)
    (equivalenceOccurrence : RootedAccountedUnfolding
      (FourTermIntegralComplexEquivAt source target)) : Type where
  private mk ::

namespace RootGeneratedFourTermDeterminantNaturalityAt

variable {Root : Type w}
variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
variable {D₀ : Type u₀} {D₁ : Type u₁} {D₂ : Type u₂} {D₃ : Type u₃}
variable [AddCommGroup C₀] [Module.Free ℤ C₀] [Module.Finite ℤ C₀]
variable [AddCommGroup C₁] [Module.Free ℤ C₁] [Module.Finite ℤ C₁]
variable [AddCommGroup C₂] [Module.Free ℤ C₂] [Module.Finite ℤ C₂]
variable [AddCommGroup C₃] [Module.Free ℤ C₃] [Module.Finite ℤ C₃]
variable [AddCommGroup D₀] [Module.Free ℤ D₀] [Module.Finite ℤ D₀]
variable [AddCommGroup D₁] [Module.Free ℤ D₁] [Module.Finite ℤ D₁]
variable [AddCommGroup D₂] [Module.Free ℤ D₂] [Module.Finite ℤ D₂]
variable [AddCommGroup D₃] [Module.Free ℤ D₃] [Module.Finite ℤ D₃]
variable {source : FourTermIntegralComplexAt C₀ C₁ C₂ C₃}
variable {target : FourTermIntegralComplexAt D₀ D₁ D₂ D₃}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {equivalenceOccurrence : RootedAccountedUnfolding
  (FourTermIntegralComplexEquivAt source target)}

def generate : RootGeneratedFourTermDeterminantNaturalityAt rootOccurrence
    equivalenceOccurrence :=
  ⟨⟩

def root
    (_face : RootGeneratedFourTermDeterminantNaturalityAt rootOccurrence
      equivalenceOccurrence) : RootedAccountedUnfolding Root :=
  rootOccurrence

noncomputable def determinantLineTransport
    (_face : RootGeneratedFourTermDeterminantNaturalityAt rootOccurrence
      equivalenceOccurrence) :
    IntegralFourTermDeterminantLine C₀ C₁ C₂ C₃ ≃ₗ[ℤ]
      IntegralFourTermDeterminantLine D₀ D₁ D₂ D₃ :=
  equivalenceOccurrence.root.determinantLineTransport

end RootGeneratedFourTermDeterminantNaturalityAt

end

end PerfectComplexDeterminantProjection
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
