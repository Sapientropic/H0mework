import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.GaussLemma
import H0mework.Versions.R2.Arithmetic.EulerGlobal.ZeroFibre

/-!
# Integral flatness of the generated full-Euler zero fibre

Every generated local determinant polynomial has constant coefficient one,
hence is primitive over `ℤ`.  Its `AdjoinRoot` is therefore torsion-free as
an integral module: Gauss' lemma detects scalar torsion after mapping to
`ℚ[X]`.  Joint faithfulness of the actual limit projections transports the
same torsion-freeness to the framework-generated global zero-fibre ring.

Over `ℤ`, torsion-free modules are flat.  This supplies the generic
base-change fact needed to identify coefficientwise integral cocycles with
the entire generated scalar cocycle kernel.  No finiteness, monicity,
analytic continuation, selected point, or evaluator extension is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiberFlatness

open CanonicalUnitArithmeticFactorizationEulerDependentDiagram
open CanonicalUnitArithmeticFactorizationFullEulerDerivedDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalDeterminantSection
open CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiber
open CategoryTheory.Limits

noncomputable section

theorem determinantPolynomial_isPrimitive
    (seed : FactorizationPayload) (stage : Nat) :
    (determinantPolynomial seed stage).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro scalar divides
  apply isUnit_iff_dvd_one.mpr
  have coefficientDivides :=
    (Polynomial.C_dvd_iff_dvd_coeff scalar
      (determinantPolynomial seed stage)).mp divides 0
  rwa [determinantPolynomial_coeff_zero] at coefficientDivides

theorem adjoinRoot_isTorsionFree_of_isPrimitive
    (polynomial : Polynomial ℤ) (primitive : polynomial.IsPrimitive) :
    Module.IsTorsionFree ℤ (AdjoinRoot polynomial) where
  isSMulRegular := by
    intro scalar regular left right equality
    rw [← sub_eq_zero]
    let difference := left - right
    have scaledZero : scalar • difference = 0 := by
      unfold difference
      rw [smul_sub]
      exact sub_eq_zero.mpr equality
    change difference = 0
    revert scaledZero
    induction difference using AdjoinRoot.induction_on with
    | ih representative =>
        intro scaledZero
        rw [AdjoinRoot.smul_mk] at scaledZero
        apply AdjoinRoot.mk_eq_zero.mpr
        apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
          polynomial representative primitive).mpr
        have mappedDivisibility := Polynomial.map_dvd
          (Int.castRingHom ℚ)
          (AdjoinRoot.mk_eq_zero.mp scaledZero)
        rcases mappedDivisibility with ⟨quotient, quotientEquation⟩
        have scalarNonzero : (scalar : ℚ) ≠ 0 := by
          exact_mod_cast regular.ne_zero
        refine ⟨quotient * Polynomial.C (scalar : ℚ)⁻¹, ?_⟩
        have mappedSmul :
            (scalar • representative).map (Int.castRingHom ℚ) =
              Polynomial.C (scalar : ℚ) *
                representative.map (Int.castRingHom ℚ) := by
          simp [Polynomial.smul_eq_C_mul]
        rw [mappedSmul] at quotientEquation
        have constantMulInverse :
            Polynomial.C (scalar : ℚ) *
                Polynomial.C (scalar : ℚ)⁻¹ = 1 := by
          rw [← Polynomial.C_mul]
          simp [scalarNonzero]
        calc
          representative.map (Int.castRingHom ℚ) =
              (Polynomial.C (scalar : ℚ) *
                  representative.map (Int.castRingHom ℚ)) *
                Polynomial.C (scalar : ℚ)⁻¹ := by
                  calc
                    _ = 1 * representative.map (Int.castRingHom ℚ) := by
                      rw [one_mul]
                    _ = (Polynomial.C (scalar : ℚ) *
                          Polynomial.C (scalar : ℚ)⁻¹) *
                            representative.map (Int.castRingHom ℚ) := by
                      rw [constantMulInverse]
                    _ = _ := by ring
          _ = (polynomial.map (Int.castRingHom ℚ) * quotient) *
                Polynomial.C (scalar : ℚ)⁻¹ := by
                  rw [quotientEquation]
          _ = polynomial.map (Int.castRingHom ℚ) *
                (quotient * Polynomial.C (scalar : ℚ)⁻¹) := by
                  ring

theorem localZeroFiberIsTorsionFree (stage : Nat) :
    Module.IsTorsionFree ℤ
      (AdjoinRoot
        (GlobalDeterminantSectionDiagram.obj
          (Opposite.op stage)).polynomial) :=
  adjoinRoot_isTorsionFree_of_isPrimitive _
    (by
      rw [globalSection_local_restriction]
      exact determinantPolynomial_isPrimitive seedOccurrence.root stage)

noncomputable instance globalZeroFiberIsTorsionFree :
    Module.IsTorsionFree ℤ GlobalZeroFiberRing where
  isSMulRegular := by
    intro scalar regular left right equality
    apply Concrete.limit_ext
    intro stage
    have localTorsionFree : Module.IsTorsionFree ℤ
        (AdjoinRoot
          (GlobalDeterminantSectionDiagram.obj stage).polynomial) := by
      simpa using localZeroFiberIsTorsionFree stage.unop
    have localRegular : Function.Injective
        (fun value : AdjoinRoot
          (GlobalDeterminantSectionDiagram.obj stage).polynomial =>
            scalar • value) :=
      @Module.IsTorsionFree.isSMulRegular ℤ
        (AdjoinRoot
          (GlobalDeterminantSectionDiagram.obj stage).polynomial)
        _ _ _ localTorsionFree scalar regular
    apply localRegular
    let projection := (limit.π GlobalZeroFiberDiagram stage).hom
    calc
      scalar • projection left = projection (scalar • left) := by
        rw [map_zsmul]
      _ = projection (scalar • right) := congrArg projection equality
      _ = scalar • projection right := by
        rw [map_zsmul]

noncomputable instance globalZeroFiberFlat :
    Module.Flat ℤ GlobalZeroFiberRing := inferInstance

end
end CanonicalUnitArithmeticFactorizationFullEulerGlobalZeroFiberFlatness
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
