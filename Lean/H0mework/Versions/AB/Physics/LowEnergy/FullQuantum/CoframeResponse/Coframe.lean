import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Principal
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.StateGreen.Flow
import H0mework.Physics.Coframe.CoframeLocalDifferentiability

/-! All sixteen actual coframe directions generate differentiable principal
and lower symbols from the original inverse-coframe gamma expression. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator ContDiff
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeLocalDifferentiability
open StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
open StateGreen
noncomputable section
local instance coframeIndexDecidable : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : NormedAddCommGroup DiracMatrix := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup DiracMatrix := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℂ DiracMatrix := Matrix.normedSpace
local instance : NormedSpace ℝ DiracMatrix := Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

def spinCoordinates : DiracMatrix →ₗ[ℂ] SourceMatrix where
  toFun M := Quantum.operatorMatrix (diracMatrixMatterAction M)
  map_add' A B := by
    have same : diracMatrixMatterAction (A+B)=diracMatrixMatterAction A+diracMatrixMatterAction B := by
      apply LinearMap.ext
      intro v
      exact coframeDiracMatrixMatterAction_add_matrix A B v
    rw [same,map_add]
  map_smul' a M := by
    have same : diracMatrixMatterAction (a • M)=a • diracMatrixMatterAction M := by
      apply LinearMap.ext
      intro v
      exact coframeDiracMatrixMatterAction_smul_matrix a M v
    rw [same,map_smul]
    rfl

def coframeConfiguration (e : LorentzianCoframe) : StageNineHolonomicConfiguration :=
  { actual with coframe := fun _ => e }

def principalMatrix (e : LorentzianCoframe) : SourceMatrix :=
  Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipal e)

def lowerMatrix (point : BasePoint) (k : Fin 3 → ℝ) (e : LorentzianCoframe) : SourceMatrix :=
  Quantum.operatorMatrix (lowerSymbol (coframeConfiguration e) point k)

def coefficientMatrix (mu : LorentzianIndex) (e : LorentzianCoframe) : SourceMatrix :=
  Complex.I • spinCoordinates (inverseCoframeDiracGamma { coframe := e, derivative := 0 } mu)

theorem principalMatrix_coefficient (e : LorentzianCoframe) :
    principalMatrix e=coefficientMatrix 0 e := by
  simp only [principalMatrix,currentCoframeMatterTemporalPrincipal,map_smul,coefficientMatrix]
  rfl

theorem lowerMatrix_coefficients (point : BasePoint) (k : Fin 3 → ℝ) (e : LorentzianCoframe) :
    lowerMatrix point k e=
      (∑ j : Fin 3, coefficientMatrix j.succ e*
        ((Complex.I*(k j : ℂ)) • (1 : SourceMatrix)+Quantum.operatorMatrix (connection actual point j.succ)))+
      Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar point)))+
      coefficientMatrix 0 e*Quantum.operatorMatrix (connection actual point 0) := by
  simp only [lowerMatrix,lowerSymbol,knownSymbol,coframeConfiguration,connection,
    map_add,map_smul,map_sum,map_one,Quantum.matrix_composition]
  simp only [currentCoframeMatterTemporalPrincipal,map_smul,coefficientMatrix,spinCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
    Matrix.smul_mul,← Finset.smul_sum]

theorem coefficientMatrix_smooth (mu : LorentzianIndex) (e : LorentzianCoframe)
    (nondegenerate : e.det≠0) : ContDiffAt ℝ ∞ (coefficientMatrix mu) e := by
  have spinSmooth : ContDiffAt ℝ ∞
      (fun x : LorentzianCoframe => spinCoordinates (inverseCoframeDiracGamma
        { coframe := x, derivative := 0 } mu)) e :=
    (spinCoordinates.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp e
      (inverseCoframeDiracGamma_contDiffAt e nondegenerate mu)
  exact (contDiffAt_const (c := Complex.I)).smul spinSmooth

theorem principalMatrix_smooth (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    ContDiffAt ℝ ∞ principalMatrix e := by
  have same : principalMatrix=coefficientMatrix 0 := funext principalMatrix_coefficient
  rw [same]
  exact coefficientMatrix_smooth 0 e nondegenerate

theorem lowerMatrix_smooth (point : BasePoint) (k : Fin 3 → ℝ)
    (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    ContDiffAt ℝ ∞ (lowerMatrix point k) e := by
  have same := funext (lowerMatrix_coefficients point k)
  rw [same]
  apply ContDiffAt.add
  · apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro j _
      exact (coefficientMatrix_smooth j.succ e nondegenerate).mul contDiffAt_const
    · exact contDiffAt_const
  · exact (coefficientMatrix_smooth 0 e nondegenerate).mul contDiffAt_const

theorem principalMatrix_regular (e : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar e≠0) : IsUnit (principalMatrix e) := by
  let inverse := Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipalInverse e)
  have left : inverse*principalMatrix e=1 := by
    rw [principalMatrix,← Quantum.matrix_composition]
    have same : (currentCoframeMatterTemporalPrincipalInverse e).comp
        (currentCoframeMatterTemporalPrincipal e)=1 := by
      apply LinearMap.ext
      intro v
      exact currentCoframeMatterTemporalPrincipalInverse_left e noncharacteristic v
    rw [same,map_one]
  have right : principalMatrix e*inverse=1 := by
    rw [principalMatrix,← Quantum.matrix_composition]
    have same : (currentCoframeMatterTemporalPrincipal e).comp
        (currentCoframeMatterTemporalPrincipalInverse e)=1 := by
      apply LinearMap.ext
      intro v
      exact currentCoframeMatterTemporalPrincipalInverse_right e noncharacteristic v
    rw [same,map_one]
  exact ⟨⟨principalMatrix e,inverse,right,left⟩,rfl⟩

def coframeHamiltonian (point : BasePoint) (k : Fin 3 → ℝ) (e : LorentzianCoframe) : SourceMatrix :=
  timeSymbol (principalMatrix e) (lowerMatrix point k e)

def coframePath (point : BasePoint) (direction : LorentzianCoframe) (epsilon : ℝ) : LorentzianCoframe :=
  actual.coframe point+epsilon • direction

theorem coframePath_derivative (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (coframePath point direction) direction 0 := by
  convert! ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add (actual.coframe point) using 1
  simp

theorem coframePath_zero (point : BasePoint) (direction : LorentzianCoframe) :
    coframePath point direction 0=actual.coframe point := by simp [coframePath]

theorem actual_coframe_nondegenerate (point : BasePoint) : (actual.coframe point).det≠0 := by
  rw [actual_coframe,Stage9C.Dynamics.Homogeneous.homogeneousCoframe_det]
  exact lapse_pos.ne'

def principalDirection (point : BasePoint) (direction : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ principalMatrix (actual.coframe point) direction

def lowerDirection (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ (lowerMatrix point k) (actual.coframe point) direction

theorem principal_parameter (point : BasePoint) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => principalMatrix (coframePath point direction epsilon))
      (principalDirection point direction) 0 := by
  have smooth := (principalMatrix_smooth (actual.coframe point)
    (actual_coframe_nondegenerate point)).differentiableAt (by simp)
  exact smooth.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative point direction)
    (coframePath_zero point direction).symm

theorem lower_parameter (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => lowerMatrix point k (coframePath point direction epsilon))
      (lowerDirection point k direction) 0 := by
  have smooth := (lowerMatrix_smooth point k (actual.coframe point)
    (actual_coframe_nondegenerate point)).differentiableAt (by simp)
  exact smooth.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative point direction)
    (coframePath_zero point direction).symm

def hamiltonianDirection (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) : SourceMatrix :=
  -(Ring.inverse (principalMatrix (actual.coframe point))*principalDirection point direction*
      coframeHamiltonian point k (actual.coframe point))-
    Complex.I • (Ring.inverse (principalMatrix (actual.coframe point))*lowerDirection point k direction)

theorem temporalScalar_path_continuous (point : BasePoint) (direction : LorentzianCoframe) :
    ContinuousAt (fun epsilon => coframeTemporalPrincipalScalar (coframePath point direction epsilon)) 0 := by
  have smooth := StageNineCoframeVariation.coframe_inv_contDiffAt (actual.coframe point)
    (actual_coframe_nondegenerate point)
  have atPath : ContinuousAt (fun e : LorentzianCoframe => e⁻¹) (coframePath point direction 0) := by
    rw [coframePath_zero]
    exact smooth.continuousAt
  have inverse := atPath.comp (coframePath_derivative point direction).continuousAt
  have entry (a : LorentzianIndex) : ContinuousAt
      (fun epsilon => (coframePath point direction epsilon)⁻¹ 0 a) 0 :=
    (continuous_apply a).continuousAt.comp ((continuous_apply 0).continuousAt.comp inverse)
  unfold coframeTemporalPrincipalScalar
  apply ContinuousAt.neg
  apply tendsto_finsetSum
  intro a _
  exact continuousAt_const.mul ((entry a).pow 2)

theorem coframePath_eventually_noncharacteristic (point : BasePoint) (direction : LorentzianCoframe) :
    ∀ᶠ epsilon in nhds (0 : ℝ), coframeTemporalPrincipalScalar (coframePath point direction epsilon)≠0 := by
  have nonzero : coframeTemporalPrincipalScalar (coframePath point direction 0)≠0 := by
    rw [coframePath_zero]
    exact actual_noncharacteristic point
  exact (temporalScalar_path_continuous point direction).eventually_ne nonzero

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeResponse
