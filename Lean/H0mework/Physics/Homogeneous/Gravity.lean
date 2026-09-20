import H0mework.Physics.Homogeneous.Cartan
import H0mework.Physics.Material.CoframeTrace

/-! Holonomic curvature and all sixteen original coframe reaction coordinates
for the constant-lapse, isotropic Cartan connection. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous

open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction
open StageNineHolonomicField StageNineLorentzConnectionVariation StageNineBlockwiseConstitutive
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineCartanTangentSimplicityResponse StageNineTopologicalFourFormPairing

noncomputable section

def homogeneousCurvature (spin : ℝ) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let a := pairFirst internalPair
    let b := pairSecond internalPair
    let μ := pairFirst spacetimePair
    let ν := pairSecond spacetimePair
    minkowskiInternalSign a * ∑ c : LorentzianIndex,
      (homogeneousConnection spin μ a c * homogeneousConnection spin ν c b -
        homogeneousConnection spin ν a c * homogeneousConnection spin μ c b)

theorem homogeneousCurvature_actual
    (current : StageNineHolonomicConfiguration) (spin : ℝ)
    (connection : current.gravityConnection = fun _ => homogeneousConnection spin)
    (point : BasePoint) :
    holonomicGravityCurvature current point = homogeneousCurvature spin := by
  funext internalPair spacetimePair
  simp only [holonomicGravityCurvature, gravityConnectionDerivative, connection]
  simp [homogeneousCurvature, Finset.sum_sub_distrib]

theorem homogeneousCurvature_components (spin : ℝ) (internalPair spacetimePair : Fin 6) :
    homogeneousCurvature spin internalPair spacetimePair =
      if internalPair = spacetimePair ∧ 3 ≤ internalPair.val then -spin^2 else 0 := by
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [homogeneousCurvature, homogeneousConnection, homogeneousContorsion,
      lorentzSkewConnectionOfBivectorOneForm, loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient, minkowskiInternalSign,
      pairFirst, pairSecond, Fin.sum_univ_six] <;> ring

def homogeneousGravityReaction (lapse spin : ℝ) : PhysicalBivector :=
  gravityInternalDualEquiv (physicalIIPlusBivector (homogeneousCoframe lapse)) -
    gravityInternalPairVarianceNormalization (homogeneousCurvature spin)

theorem homogeneousGravityReaction_coordinates
    (lapse spin : ℝ) (row column : LorentzianIndex) :
    gravityTopologicalWedgeCoefficient (homogeneousGravityReaction lapse spin)
      (physicalIIPlusCoframeTangent (homogeneousCoframe lapse) (Matrix.single row column 1)) =
      if row = column then
        if row = 0 then 3 - 3*spin^2 else lapse * (3 - spin^2)
      else 0 := by
  fin_cases row <;> fin_cases column <;>
    simp [homogeneousGravityReaction, gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit, physicalIIPlusCoframeTangent,
      physicalIIPlusBivector, coframeWedgeTangent, coframeWedge,
      gravityInternalDualEquiv, gravityInternalDualLinear, internalBivectorDual,
      lorentzianCoframeHodge, gravityInternalPairVarianceNormalization,
      lorentzianTwoFormSign, minkowskiInternalSign, pairFirst, pairSecond,
      Fin.sum_univ_six, homogeneousCoframe, Matrix.single_apply,
      homogeneousCurvature_components] <;> ring

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.Homogeneous
