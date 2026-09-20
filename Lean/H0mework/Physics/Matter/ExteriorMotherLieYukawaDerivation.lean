import H0mework.Physics.Exterior.ExteriorMotherLieWedgeDerivation

/-!
# Stage-9 exterior mother Lie Yukawa derivation

The infinitesimal exterior-wedge Leibniz law lifts through the actual
Stage-7 internal direct sum, the pointwise Dirac carrier, and the derived
cross-chiral Yukawa action.

The chiral proof commutes the mother Lie action through the actual Dirac
projectors and `gamma^0` using only their independently proved tensor-factor
commutation law.  No finite SU(7) equivariance theorem, Ward identity,
source datum, receipt, residual equation, or target equality is accepted at
a theorem mouth.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieYukawaDerivation

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open StageNineExteriorMotherLieWedgeDerivation
open StageNineHolonomicField
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterRepresentation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false

/-- The actual internal Yukawa map obeys the infinitesimal mother-action
Leibniz law on the degree-six, degree-two, degree-four direct sum. -/
theorem exteriorYukawaInternalAction_motherLieAction
    (matrix : SU7MotherLieMatrix)
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : SU7ExteriorSpinorMatterCarrier) :
    exteriorSpinorMotherLieAction matrix
        (exteriorYukawaInternalAction scalar matter) =
      exteriorYukawaInternalAction
          (exteriorMotherLieAction 4 matrix scalar) matter +
        exteriorYukawaInternalAction scalar
          (exteriorSpinorMotherLieAction matrix matter) := by
  apply Prod.ext
  · change
      exteriorMotherLieAction 6 matrix
          (exteriorYukawaMassMap scalar matter.2.1) =
        exteriorYukawaMassMap
            (exteriorMotherLieAction 4 matrix scalar) matter.2.1 +
          exteriorYukawaMassMap scalar
            (exteriorMotherLieAction 2 matrix matter.2.1)
    rw [exteriorYukawaMassMap_motherLieAction]
    ac_rfl
  · apply Prod.ext <;> simp [exteriorYukawaInternalAction,
      exteriorSpinorMotherLieAction]

/-- Applying the actual internal Leibniz law independently at each Dirac
index gives the Dirac-carrier law. -/
theorem diracExteriorYukawaInternalAction_motherLieAction
    (matrix : SU7MotherLieMatrix)
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction matrix
        (diracExteriorYukawaInternalAction scalar matter) =
      diracExteriorYukawaInternalAction
          (exteriorMotherLieAction 4 matrix scalar) matter +
        diracExteriorYukawaInternalAction scalar
          (diracExteriorMotherLieAction matrix matter) := by
  funext spin
  exact exteriorYukawaInternalAction_motherLieAction
    matrix scalar (matter spin)

/-- The internal mother action commutes with every actual Dirac-matrix
action because the two maps act on independent tensor factors. -/
private theorem diracExteriorMotherLieAction_commutes_diracMatrix
    (motherMatrix : SU7MotherLieMatrix)
    (diracMatrix : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction motherMatrix
        (diracMatrixMatterAction diracMatrix matter) =
      diracMatrixMatterAction diracMatrix
        (diracExteriorMotherLieAction motherMatrix matter) := by
  simpa only [diracExteriorMotherLieAction, LinearMap.comp_apply] using
    (LinearMap.congr_fun
      (diracMatrixMatterAction_commutes_internal diracMatrix
        (exteriorSpinorMotherLieAction motherMatrix))
      matter).symm

/-- Infinitesimal equivariance of the actual cross-chiral Yukawa action:
the mother response of `P_L gamma^0 Y_H P_R psi` is the sum of the scalar
response and the matter response. -/
theorem chiralExteriorYukawaAction_motherLieAction
    (matrix : SU7MotherLieMatrix)
    (scalar : ExteriorBreakingScalarCarrier)
    (matter : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction matrix
        (chiralExteriorYukawaAction scalar matter) =
      chiralExteriorYukawaAction
          (exteriorMotherLieAction 4 matrix scalar) matter +
        chiralExteriorYukawaAction scalar
          (diracExteriorMotherLieAction matrix matter) := by
  unfold chiralExteriorYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracExteriorMotherLieAction_commutes_diracMatrix,
    diracExteriorMotherLieAction_commutes_diracMatrix,
    diracExteriorYukawaInternalAction_motherLieAction,
    map_add, map_add,
    diracExteriorMotherLieAction_commutes_diracMatrix]

end

end
  SaturationMonoid.PhysicsCore.StageNineExteriorMotherLieYukawaDerivation
