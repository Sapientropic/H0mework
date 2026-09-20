import H0mework.Physics.PlaneWave.Coframe
import H0mework.Physics.Cartan.CartanAffineConnectionActualization
import H0mework.Physics.Exterior.GravityMultiplierAuxiliaryIntegratedVariation

/-! Global logarithmic AdS geometry. The primitive exponential coframe generates
its true first jet, Levi–Civita spin connection and holonomic curvature. The
action's intrinsic reaction vanishes with the repository's exact index signs;
this is the geometric background consumed by the null-wave construction. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave

open ProofFreeRicherAnholonomicSource
open PointwiseLorentzianCoframeJet
open StageNineCoframeFirstJet
open StageNineHolonomicField
open StageNineGlobalIntegratedAction
open StageNineBlockwiseConstitutive
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineLorentzConnectionVariation
open scoped Matrix

noncomputable section

def adsCoframeJet (q : ℝ) : PointwiseLorentzianCoframeJet where
  coframe := adsCoframeScale q
  derivative := fun μ a ν => if μ = 2 ∧ a ≠ 2 ∧ a = ν then -q else 0

def adsConnectionScale (q : ℝ) : PointwiseLorentzSpinConnection :=
  fun μ a b =>
    (if a = μ ∧ a ≠ 2 ∧ b = 2 then -q else 0) +
    (if a = 2 ∧ b = μ ∧ b ≠ 2 then minkowskiInternalSign b * q else 0)

private theorem adsMetric_inverse (q : ℝ) (hq : q ≠ 0) :
    (lorentzianMetricOfCoframe (adsCoframeScale q))⁻¹ =
      lorentzianMetricOfCoframe (adsCoframeScale q⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [adsCoframeScale_metric, adsCoframeScale_metric]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

private theorem adsMetric_derivative (q : ℝ) (μ ν ρ : LorentzianIndex) :
    (adsCoframeJet q).metricDerivative μ ν ρ =
      if μ = 2 ∧ ν = ρ ∧ ν ≠ 2 then -2 * minkowskiInternalSign ν * q ^ 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;>
    simp [metricDerivative, adsCoframeJet, adsCoframeScale, minkowskiInternalSign,
      Fin.sum_univ_four] <;> ring

private def adsAffineConnectionScale (q : ℝ) : PointwiseAffineConnection :=
  fun a μ ν =>
    (if a = 2 ∧ μ = ν ∧ μ ≠ 2 then minkowskiInternalSign μ * q ^ 2 else 0) +
    (if a = μ ∧ ν = 2 ∧ a ≠ 2 then -1 else 0) +
    (if a = ν ∧ μ = 2 ∧ a ≠ 2 then -1 else 0)

private theorem adsCoframeJet_affineConnection (q : ℝ) (hq : q ≠ 0) :
    (adsCoframeJet q).leviCivitaConnection = adsAffineConnectionScale q := by
  funext a μ ν
  change ((lorentzianMetricOfCoframe (adsCoframeScale q))⁻¹ *ᵥ
    (adsCoframeJet q).loweredLeviCivitaVector μ ν) a = _
  rw [adsMetric_inverse q hq, adsCoframeScale_metric]
  fin_cases a <;> fin_cases μ <;> fin_cases ν <;>
    simp [adsAffineConnectionScale, Matrix.mulVec, dotProduct,
      loweredLeviCivitaVector, loweredLeviCivitaConnection, adsMetric_derivative, minkowskiInternalSign,
      Fin.sum_univ_four] <;> field_simp

theorem adsCoframeJet_spinConnection (q : ℝ) (hq : q ≠ 0) :
    (adsCoframeJet q).lorentzSpinConnection = adsConnectionScale q := by
  funext μ a b
  simp only [PointwiseLorentzianCoframeJet.lorentzSpinConnection,
    lorentzSpinConnectionMatrix, coordinateConnectionMatrix, affineConnectionMatrix,
    adsCoframeJet_affineConnection q hq]
  rw [show (adsCoframeJet q).coframe = adsCoframeScale q by rfl,
    adsCoframeScale_inv q hq]
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    simp [adsConnectionScale, coframeDerivativeMatrix, adsAffineConnectionScale, adsCoframeJet,
      adsCoframeScale, Matrix.mul_apply,
      minkowskiInternalSign, Fin.sum_univ_four] <;>
    field_simp

def adsCurvatureScale (q : ℝ) : PhysicalBivector :=
  fun internalPair spacetimePair =>
    let a := pairFirst internalPair
    let b := pairSecond internalPair
    let μ := pairFirst spacetimePair
    let ν := pairSecond spacetimePair
    minkowskiInternalSign a *
      ((if μ = 2 then -adsConnectionScale q ν a b else 0) -
        (if ν = 2 then -adsConnectionScale q μ a b else 0) +
        ∑ c : LorentzianIndex,
          (adsConnectionScale q μ a c * adsConnectionScale q ν c b -
            adsConnectionScale q ν a c * adsConnectionScale q μ c b))

theorem adsCurvatureScale_constantCurvature (q : ℝ) :
    gravityInternalPairVarianceNormalization (adsCurvatureScale q) =
      gravityInternalDualEquiv (physicalIIPlusBivector (adsCoframeScale q)) := by
  funext internalPair spacetimePair
  fin_cases internalPair <;> fin_cases spacetimePair <;>
    simp [gravityInternalPairVarianceNormalization, adsCurvatureScale,
      adsConnectionScale, gravityInternalDualEquiv, gravityInternalDualLinear,
      physicalIIPlusBivector, internalBivectorDual, lorentzianCoframeHodge,
      lorentzianTwoFormSign, minkowskiInternalSign, adsCoframeScale,
      coframeWedge, pairFirst, pairSecond, Fin.sum_univ_four]

theorem adsScale_hasFDerivAt (point : BasePoint) :
    HasFDerivAt adsScale ((-adsScale point) • coframeBaseCoordinate 2) point := by
  change HasFDerivAt (fun x : BasePoint => Real.exp (-x 2))
    ((-Real.exp (-point 2)) • coframeBaseCoordinate 2) point
  have derivative : HasFDerivAt (fun x : BasePoint => Real.exp (-x 2))
      (Real.exp (-point 2) • (-coframeBaseCoordinate 2)) point :=
    ((coframeBaseCoordinate 2).hasFDerivAt (x := point)).neg.exp
  have coefficients : Real.exp (-point 2) • (-coframeBaseCoordinate 2) =
      (-Real.exp (-point 2)) • coframeBaseCoordinate 2 := by
    ext vector
    change Real.exp (-point 2) * (-vector 2) = (-Real.exp (-point 2)) * vector 2
    ring
  rw [coefficients] at derivative
  exact derivative

theorem adsScale_directionalDerivative (point : BasePoint) (μ : LorentzianIndex) :
    fderiv ℝ adsScale point (coordinateDirection μ) =
      if μ = 2 then -adsScale point else 0 := by
  rw [(adsScale_hasFDerivAt point).fderiv]
  change (-adsScale point) * coframeBaseCoordinate 2 (coordinateDirection μ) = _
  rw [coframeBaseCoordinate_coordinateDirection]
  split_ifs <;> simp_all

def adsCoframeField (point : BasePoint) : LorentzianCoframe :=
  adsCoframeScale (adsScale point)

theorem adsCoframeField_firstJet (point : BasePoint) :
    holonomicCoframeFirstJetAt adsCoframeField point = adsCoframeJet (adsScale point) := by
  refine coframeJet_eq_of_fields_eq (holonomicCoframeFirstJetAt adsCoframeField point)
    (adsCoframeJet (adsScale point)) rfl ?_
  funext μ a ν
  fin_cases a <;> fin_cases ν <;>
    simp [holonomicCoframeFirstJetAt, adsCoframeField, adsCoframeScale, adsCoframeJet,
      adsScale_directionalDerivative]

def adsConnectionField (point : BasePoint) : PointwiseLorentzSpinConnection :=
  adsConnectionScale (adsScale point)

theorem adsConnectionField_eq_generatedLC (point : BasePoint) :
    adsConnectionField point =
      (holonomicCoframeFirstJetAt adsCoframeField point).lorentzSpinConnection := by
  rw [adsCoframeField_firstJet, adsCoframeJet_spinConnection]
  · rfl
  · exact Real.exp_ne_zero _

theorem adsConnectionField_directionalDerivative
    (point : BasePoint) (δ μ a b : LorentzianIndex) :
    fderiv ℝ (fun x => adsConnectionField x μ a b) point (coordinateDirection δ) =
      if δ = 2 then -adsConnectionField point μ a b else 0 := by
  fin_cases μ <;> fin_cases a <;> fin_cases b <;>
    by_cases hd : δ = 2 <;>
    simp [adsConnectionField, adsConnectionScale, minkowskiInternalSign,
      adsScale_directionalDerivative, hd]

def adsGravityWrite (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    coframe := adsCoframeField
    gravityConnection := adsConnectionField
    gravityAuxiliary := fun point => physicalIIPlusBivector (adsCoframeField point)
    gravitySimplicityMultiplier := 0 }

theorem adsGravityWrite_curvature (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    holonomicGravityCurvature (adsGravityWrite current) point =
      adsCurvatureScale (adsScale point) := by
  funext internalPair spacetimePair
  simp only [holonomicGravityCurvature, gravityConnectionDerivative, adsGravityWrite,
    adsConnectionField_directionalDerivative]
  rfl

theorem adsGravityWrite_reaction_zero (current : StageNineHolonomicConfiguration) :
    formNativeGravityReactionField (adsGravityWrite current) = 0 := by
  funext point
  unfold formNativeGravityReactionField holonomicContravariantGravityCurvature
  rw [adsGravityWrite_curvature, adsCurvatureScale_constantCurvature]
  exact sub_self _

end
end SaturationMonoid.PhysicsCore.Stage9C.Dynamics.PlaneWave
