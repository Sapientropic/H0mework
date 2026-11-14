import Mathlib.Algebra.Module.Torsion.Basic
import H0mework.Versions.R21a4a7ce.ReleaseMaterials.SaturationMonoid.UniversalBSDGeometricGalois

/-!
# Universal BSD arbitrary geometric torsion Galois representation

For every elliptic curve over `Q` and natural number `n`, this module equips the actual geometric `E[n]` carrier over
`Qbar` with its restricted integral absolute-Galois representation. The matching Galois action
has open point stabilizers and is jointly continuous for the discrete coefficient topology.
-/

namespace SaturationMonoid
namespace UniversalBSDGeometricNTorsion

open UniversalBSDGeometricGalois

open CategoryTheory

noncomputable section

set_option maxHeartbeats 1200000

/-! ## The actual global `E[n]` integral representation -/

/-- Actual geometric `n`-torsion on the source-generated curve. -/
abbrev GeometricNTorsion
    (source : RationalEllipticCurveSource) (n : ℕ) :=
  AddSubgroup.torsionBy (GeometricPoints source) n

instance geometricNTorsionTopology
    (source : RationalEllipticCurveSource) (n : ℕ) :
    TopologicalSpace (GeometricNTorsion source n) :=
  ⊥

instance geometricNTorsionDiscreteTopology
    (source : RationalEllipticCurveSource) (n : ℕ) :
    DiscreteTopology (GeometricNTorsion source n) :=
  ⟨rfl⟩

instance geometricNTorsionContinuousIntSMul
    (source : RationalEllipticCurveSource) (n : ℕ) :
    ContinuousSMul ℤ (GeometricNTorsion source n) :=
  ⟨continuous_of_discreteTopology⟩

noncomputable def geometricNTorsionGaloisAddHom
    (source : RationalEllipticCurveSource) (n : ℕ)
    (sigma : Field.absoluteGaloisGroup ℚ) :
    GeometricNTorsion source n →+
      GeometricNTorsion source n :=
  (geometricPointGaloisMap source sigma).domRestrict
      (AddSubgroup.torsionBy (GeometricPoints source) n) |>.codRestrict
    (AddSubgroup.torsionBy (GeometricPoints source) n) (fun point ↦ by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      change n • geometricPointGaloisMap source sigma point.1 = 0
      rw [← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.mp point.property, map_zero])

instance geometricNTorsionGaloisSMul
    (source : RationalEllipticCurveSource) (n : ℕ) :
    SMul (Field.absoluteGaloisGroup ℚ)
      (GeometricNTorsion source n) :=
  ⟨fun sigma point ↦
    geometricNTorsionGaloisAddHom source n sigma point⟩

instance geometricNTorsionGaloisMulAction
    (source : RationalEllipticCurveSource) (n : ℕ) :
    MulAction (Field.absoluteGaloisGroup ℚ)
      (GeometricNTorsion source n) where
  one_smul point := by
    rcases point with ⟨(_ | ⟨x, y, hpoint⟩), hn⟩ <;> rfl
  mul_smul sigma tau point := by
    apply Subtype.ext
    exact geometricPointGaloisMap_comp source sigma tau point.1

theorem geometricNTorsion_stabilizer_isOpen
    (source : RationalEllipticCurveSource) (n : ℕ)
    (point : GeometricNTorsion source n) :
    IsOpen
      (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) point :
        Set (Field.absoluteGaloisGroup ℚ)) := by
  have hstabilizer :
      (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) point :
          Set (Field.absoluteGaloisGroup ℚ)) =
        (MulAction.stabilizer (Field.absoluteGaloisGroup ℚ) point.1 :
          Set (Field.absoluteGaloisGroup ℚ)) := by
    ext sigma
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [hstabilizer]
  exact geometricPoints_stabilizer_isOpen source point.1

instance geometricNTorsionContinuousGaloisSMul
    (source : RationalEllipticCurveSource) (n : ℕ) :
    ContinuousSMul (Field.absoluteGaloisGroup ℚ)
      (GeometricNTorsion source n) :=
  continuousSMul_iff_stabilizer_isOpen.mpr
    (geometricNTorsion_stabilizer_isOpen source n)

noncomputable def geometricNTorsionGaloisContinuousLinearMap
    (source : RationalEllipticCurveSource) (n : ℕ)
    (sigma : Field.absoluteGaloisGroup ℚ) :
    GeometricNTorsion source n →L[ℤ]
      GeometricNTorsion source n :=
  ContinuousLinearMap.mk
    (geometricNTorsionGaloisAddHom source n sigma).toIntLinearMap
    continuous_of_discreteTopology

noncomputable def geometricNTorsionGaloisMonoidHom
    (source : RationalEllipticCurveSource) (n : ℕ) :
    Field.absoluteGaloisGroup ℚ →*
      (GeometricNTorsion source n →L[ℤ]
        GeometricNTorsion source n) where
  toFun := geometricNTorsionGaloisContinuousLinearMap source n
  map_one' := by
    ext point
    rcases point with ⟨(_ | ⟨x, y, hpoint⟩), hn⟩ <;> rfl
  map_mul' sigma tau := by
    ext point
    change geometricPointGaloisMap source (sigma * tau) point.1 =
      geometricPointGaloisMap source sigma
        (geometricPointGaloisMap source tau point.1)
    exact geometricPointGaloisMap_comp source sigma tau point.1

/-- The actual geometric `E[n]` carrier with integral coefficients and restricted Galois action. -/
noncomputable def geometricNTorsionIntTopRep
    (source : RationalEllipticCurveSource) (n : ℕ) :
    TopRep ℤ (Field.absoluteGaloisGroup ℚ) :=
  TopRep.of (ContRepresentation.ofMonoidHom
    (geometricNTorsionGaloisMonoidHom source n))

@[simp]
theorem geometricNTorsionIntTopRep_rho_apply
    (source : RationalEllipticCurveSource) (n : ℕ)
    (sigma : Field.absoluteGaloisGroup ℚ)
    (point : GeometricNTorsion source n) :
    (geometricNTorsionIntTopRep source n).ρ sigma point =
      geometricNTorsionGaloisAddHom source n sigma point :=
  rfl

/-- The integral `TopRep` action is pointwise the jointly continuous Galois action above. -/
theorem geometricNTorsionIntTopRep_rho_eq_smul
    (source : RationalEllipticCurveSource) (n : ℕ)
    (sigma : Field.absoluteGaloisGroup ℚ)
    (point : GeometricNTorsion source n) :
    (geometricNTorsionIntTopRep source n).ρ sigma point =
      sigma • point :=
  rfl

noncomputable def geometricNTorsionToGeometricPointContinuousLinearMap
    (source : RationalEllipticCurveSource) (n : ℕ) :
    GeometricNTorsion source n →L[ℤ]
      GeometricPoints source :=
  ContinuousLinearMap.mk
    (AddSubgroup.subtype
      (AddSubgroup.torsionBy (GeometricPoints source) n)).toIntLinearMap
    continuous_of_discreteTopology

/-- Actual coefficient inclusion `E[n](Qbar) → E(Qbar)`. -/
noncomputable def geometricNTorsionToGeometricPointTopRepHom
    (source : RationalEllipticCurveSource) (n : ℕ) :
    geometricNTorsionIntTopRep source n ⟶
      geometricPointTopRep source :=
  TopRep.ofHom ⟨
    geometricNTorsionToGeometricPointContinuousLinearMap source n,
    by
      intro sigma
      ext point
      rfl
  ⟩

@[simp]
theorem geometricNTorsionToGeometricPointTopRepHom_apply
    (source : RationalEllipticCurveSource) (n : ℕ)
    (point : GeometricNTorsion source n) :
    (geometricNTorsionToGeometricPointTopRepHom source n).hom point = point.1 :=
  rfl

/-! ## Multiplication transitions between torsion levels -/

/-- Multiplication by `a` sends actual `E[a*n]` into actual `E[n]`. -/
noncomputable def geometricNTorsionTransitionAddHom
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    GeometricNTorsion source (a * n) →+
      GeometricNTorsion source n :=
  (nsmulAddMonoidHom a).domRestrict
      (AddSubgroup.torsionBy (GeometricPoints source) (a * n)) |>.codRestrict
    (AddSubgroup.torsionBy (GeometricPoints source) n) (fun point ↦ by
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      change n • a • point.1 = 0
      rw [← mul_nsmul]
      exact AddSubgroup.torsionBy.nsmul_iff.mp point.property)

@[simp]
theorem geometricNTorsionTransitionAddHom_apply
    (source : RationalEllipticCurveSource) (a n : ℕ)
    (point : GeometricNTorsion source (a * n)) :
    (geometricNTorsionTransitionAddHom source a n point).1 = a • point.1 :=
  rfl

noncomputable def geometricNTorsionTransitionContinuousLinearMap
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    GeometricNTorsion source (a * n) →L[ℤ]
      GeometricNTorsion source n :=
  ContinuousLinearMap.mk
    (geometricNTorsionTransitionAddHom source a n).toIntLinearMap
    continuous_of_discreteTopology

/-- Actual Galois-equivariant transition between the integral torsion representations. -/
noncomputable def geometricNTorsionTransitionTopRepHom
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    geometricNTorsionIntTopRep source (a * n) ⟶
      geometricNTorsionIntTopRep source n :=
  TopRep.ofHom ⟨
    geometricNTorsionTransitionContinuousLinearMap source a n,
    by
      intro sigma
      ext point
      dsimp [geometricNTorsionTransitionContinuousLinearMap,
        geometricNTorsionTransitionAddHom, geometricNTorsionIntTopRep,
        geometricNTorsionGaloisMonoidHom,
        geometricNTorsionGaloisContinuousLinearMap,
        geometricNTorsionGaloisAddHom]
      change a • geometricPointGaloisMap source sigma point.1 =
        geometricPointGaloisMap source sigma (a • point.1)
      exact (AddMonoidHom.map_nsmul
        (geometricPointGaloisMap source sigma) a point.1).symm
  ⟩

/-- The torsion transition and full-point multiplication use the same actual points. -/
theorem geometricNTorsionTransition_coefficient_commutes
    (source : RationalEllipticCurveSource) (a n : ℕ) :
    geometricNTorsionTransitionTopRepHom source a n ≫
        geometricNTorsionToGeometricPointTopRepHom source n =
      geometricNTorsionToGeometricPointTopRepHom source (a * n) ≫
        geometricPointNsmulTopRepHom source a := by
  ext point
  change a • point.1 = a • point.1
  rfl

end

end UniversalBSDGeometricNTorsion
end SaturationMonoid
