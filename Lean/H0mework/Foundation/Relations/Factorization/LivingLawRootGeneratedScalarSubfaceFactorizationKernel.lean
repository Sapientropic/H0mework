import H0mework.Foundation.Relations.ScalarDifferentialResidual

/-!
# Source-generated subface factorization

An actual source map `g : C → D` and an injective dependent-face map
`i : U → D` generate a complete disposition.  If the canonical quotient
residual `C → D / range(i)` vanishes, `g` factors uniquely through `U`.
Otherwise the source retains an explicit coordinate outside `range(i)`.

No caller-supplied lift, finite/projective hypothesis, determinant, inverse,
or residual-zero token enters the disposition.  Residual maps are natural
for every commuting source/subface square, with strict identity and
composition laws.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedSubfaceFactorization

noncomputable section

universe r c u d c' u' d'

variable {R : Type r} [CommRing R]
variable {C : Type c} {U : Type u} {D : Type d}
variable [AddCommGroup C] [AddCommGroup U] [AddCommGroup D]
variable [Module R C] [Module R U] [Module R D]

abbrev ResidualCarrier (subface : U →ₗ[R] D) :=
  D ⧸ LinearMap.range subface

def residualMap (source : C →ₗ[R] D) (subface : U →ₗ[R] D) :
    C →ₗ[R] ResidualCarrier subface :=
  (Submodule.mkQ (LinearMap.range subface)).comp source

@[simp] theorem residualMap_apply
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D) (value : C) :
    residualMap source subface value =
      Submodule.Quotient.mk (p := LinearMap.range subface) (source value) :=
  rfl

structure Factorization (source : C →ₗ[R] D) (subface : U →ₗ[R] D) where
  lift : C →ₗ[R] U
  commutes : subface.comp lift = source

structure ResidualCoordinate
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D) where
  coordinate : C
  source_not_mem_range : source coordinate ∉ LinearMap.range subface

def subfaceRangeEquiv
    (subface : U →ₗ[R] D) (injective : Function.Injective subface) :
    U ≃ₗ[R] LinearMap.range subface :=
  LinearEquiv.ofInjective subface injective

def sourceRangeMap
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (residual_zero : residualMap source subface = 0) :
    C →ₗ[R] LinearMap.range subface :=
  source.codRestrict (LinearMap.range subface) (by
    intro value
    have equality := LinearMap.congr_fun residual_zero value
    change Submodule.Quotient.mk (source value) = 0 at equality
    exact (Submodule.Quotient.mk_eq_zero _).mp equality)

def canonicalLift
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface)
    (residual_zero : residualMap source subface = 0) :
    C →ₗ[R] U :=
  (subfaceRangeEquiv subface injective).symm.toLinearMap.comp
    (sourceRangeMap source subface residual_zero)

theorem canonicalLift_commutes
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface)
    (residual_zero : residualMap source subface = 0) :
    subface.comp (canonicalLift source subface injective residual_zero) = source := by
  apply LinearMap.ext
  intro value
  have equality := (subfaceRangeEquiv subface injective).apply_symm_apply
    (sourceRangeMap source subface residual_zero value)
  exact congrArg Subtype.val equality

def canonicalFactorization
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface)
    (residual_zero : residualMap source subface = 0) :
    Factorization source subface where
  lift := canonicalLift source subface injective residual_zero
  commutes := canonicalLift_commutes source subface injective residual_zero

theorem factorization_unique
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface)
    (left right : Factorization source subface) :
    left.lift = right.lift := by
  apply LinearMap.ext
  intro value
  apply injective
  have leftAt := LinearMap.congr_fun left.commutes value
  have rightAt := LinearMap.congr_fun right.commutes value
  exact leftAt.trans rightAt.symm

theorem factorization_nonempty_iff_residualMap_eq_zero
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface) :
    Nonempty (Factorization source subface) ↔ residualMap source subface = 0 := by
  constructor
  · rintro ⟨factor⟩
    apply LinearMap.ext
    intro value
    change Submodule.Quotient.mk (source value) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨factor.lift value, ?_⟩
    exact LinearMap.congr_fun factor.commutes value
  · intro residual_zero
    exact ⟨canonicalFactorization source subface injective residual_zero⟩

theorem residualMap_ne_zero_iff_exists_coordinate
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D) :
    residualMap source subface ≠ 0 ↔
      Nonempty (ResidualCoordinate source subface) := by
  constructor
  · intro notZero
    have existsValue : ∃ value : C, residualMap source subface value ≠ 0 := by
      by_contra noValue
      apply notZero
      apply LinearMap.ext
      intro value
      by_contra value_ne
      exact noValue ⟨value, value_ne⟩
    obtain ⟨value, value_ne⟩ := existsValue
    refine ⟨⟨value, ?_⟩⟩
    intro value_mem
    apply value_ne
    exact (Submodule.Quotient.mk_eq_zero _).mpr value_mem
  · rintro ⟨coordinate⟩ zeroMap
    apply coordinate.source_not_mem_range
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have equality := LinearMap.congr_fun zeroMap coordinate.coordinate
    exact equality

inductive Disposition
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D) :
    Type (max c u d + 1) where
  | factors (factorization : Factorization source subface)
  | residual (coordinate : ResidualCoordinate source subface)

noncomputable def settle
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface) :
    Disposition source subface := by
  classical
  by_cases residual_zero : residualMap source subface = 0
  · exact .factors
      (canonicalFactorization source subface injective residual_zero)
  · exact Disposition.residual
      (((residualMap_ne_zero_iff_exists_coordinate source subface).mp
        residual_zero).some)

theorem settle_total
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (injective : Function.Injective subface) :
    Nonempty (Disposition source subface) :=
  ⟨settle source subface injective⟩

/-! ## Residual naturality -/

variable {C' : Type c'} {U' : Type u'} {D' : Type d'}
variable [AddCommGroup C'] [AddCommGroup U'] [AddCommGroup D']
variable [Module R C'] [Module R U'] [Module R D']

def residualTransport
    (subface : U →ₗ[R] D) (subface' : U' →ₗ[R] D')
    (faceMap : U →ₗ[R] U') (targetMap : D →ₗ[R] D')
    (subfaceSquare : targetMap.comp subface = subface'.comp faceMap) :
    ResidualCarrier subface →ₗ[R] ResidualCarrier subface' :=
  (LinearMap.range subface).liftQ
    ((Submodule.mkQ (LinearMap.range subface')).comp targetMap) (by
      intro value value_mem
      rw [LinearMap.mem_ker]
      rcases value_mem with ⟨faceValue, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨faceMap faceValue, ?_⟩
      exact (LinearMap.congr_fun subfaceSquare faceValue).symm)

@[simp] theorem residualTransport_mk
    (subface : U →ₗ[R] D) (subface' : U' →ₗ[R] D')
    (faceMap : U →ₗ[R] U') (targetMap : D →ₗ[R] D')
    (subfaceSquare : targetMap.comp subface = subface'.comp faceMap)
    (value : D) :
    residualTransport subface subface' faceMap targetMap subfaceSquare
        (Submodule.Quotient.mk value) =
      Submodule.Quotient.mk (targetMap value) := by
  exact Submodule.liftQ_apply _ _ _

theorem residualMap_naturality
    (source : C →ₗ[R] D) (subface : U →ₗ[R] D)
    (source' : C' →ₗ[R] D') (subface' : U' →ₗ[R] D')
    (sourceMap : C →ₗ[R] C') (faceMap : U →ₗ[R] U')
    (targetMap : D →ₗ[R] D')
    (sourceSquare : targetMap.comp source = source'.comp sourceMap)
    (subfaceSquare : targetMap.comp subface = subface'.comp faceMap) :
    (residualTransport subface subface' faceMap targetMap subfaceSquare).comp
        (residualMap source subface) =
      (residualMap source' subface').comp sourceMap := by
  apply LinearMap.ext
  intro value
  change Submodule.Quotient.mk (targetMap (source value)) =
    Submodule.Quotient.mk (source' (sourceMap value))
  exact congrArg (fun targetValue : D' =>
    Submodule.Quotient.mk (p := LinearMap.range subface') targetValue)
      (LinearMap.congr_fun sourceSquare value)

theorem residualTransport_id
    (subface : U →ₗ[R] D) :
    residualTransport subface subface LinearMap.id LinearMap.id rfl =
      LinearMap.id := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range subface) quotientValue
  rfl

variable {U'' : Type u'} {D'' : Type d'}
variable [AddCommGroup U''] [AddCommGroup D'']
variable [Module R U''] [Module R D'']

theorem residualTransport_comp
    (subface : U →ₗ[R] D)
    (subface' : U' →ₗ[R] D')
    (subface'' : U'' →ₗ[R] D'')
    (faceMap₁ : U →ₗ[R] U') (faceMap₂ : U' →ₗ[R] U'')
    (targetMap₁ : D →ₗ[R] D') (targetMap₂ : D' →ₗ[R] D'')
    (square₁ : targetMap₁.comp subface = subface'.comp faceMap₁)
    (square₂ : targetMap₂.comp subface' = subface''.comp faceMap₂)
    (square₁₂ : (targetMap₂.comp targetMap₁).comp subface =
      subface''.comp (faceMap₂.comp faceMap₁)) :
    residualTransport subface subface'' (faceMap₂.comp faceMap₁)
        (targetMap₂.comp targetMap₁) square₁₂ =
      (residualTransport subface' subface'' faceMap₂ targetMap₂ square₂).comp
        (residualTransport subface subface' faceMap₁ targetMap₁ square₁) := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range subface) quotientValue
  rfl

end
end SourceGeneratedSubfaceFactorization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
