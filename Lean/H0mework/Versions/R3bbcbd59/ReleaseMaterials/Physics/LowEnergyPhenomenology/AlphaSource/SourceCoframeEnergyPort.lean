import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalCoframe

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open DiracExteriorMatterAction DiracCliffordRepresentation
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open Stage10
open scoped Matrix Matrix.Norms.L2Operator BigOperators ContDiff Topology
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- The source Clifford coefficient is linear in the original inverse coframe. -/
def sourceCoframeCoefficientLinear (mu : Fin 4) : LorentzianCoframe→L[ℝ] SourceMatrix :=
  ∑a : Fin 4,((ContinuousLinearMap.proj a).comp
    (ContinuousLinearMap.proj mu : LorentzianCoframe→L[ℝ](Fin 4→ℝ))).smulRight
      (Complex.I • spinCoordinates (diracGamma a))

theorem sourceCoframeCoefficientLinear_original (e : LorentzianCoframe) (mu : Fin 4) :
    coefficientMatrix mu e=sourceCoframeCoefficientLinear mu e⁻¹ := by
  simp only [coefficientMatrix,inverseCoframeDiracGamma,map_sum,map_smul,
    sourceCoframeCoefficientLinear,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul,mul_comm]
  rfl

/-- The original inverse coframe generates its own variation; the inverse is never held fixed. -/
theorem sourceCoframeInverse_derivative (e h : LorentzianCoframe) (nondegenerate : e.det≠0) :
    HasDerivAt (fun t : ℝ=>(e+t • h)⁻¹) (-(e⁻¹*h*e⁻¹)) 0 := by
  let D : LorentzianCoframe:=fderiv ℝ (fun a : LorentzianCoframe=>a⁻¹) e h
  have path : HasDerivAt (fun t : ℝ=>e+t • h) h 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add e
  have inverse : HasDerivAt (fun t : ℝ=>(e+t • h)⁻¹) D 0 :=
    ((StageNineCoframeVariation.coframe_inv_contDiffAt e nondegenerate).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 path (by simp)
  have product : HasDerivAt (fun t : ℝ=>(e+t • h)⁻¹*(e+t • h)) (D*e+e⁻¹*h) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    have terms:=HasDerivAt.sum (fun k (_ : k∈(Finset.univ : Finset (Fin 4)))=>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp inverse i) k).mul
        (hasDerivAt_pi.mp (hasDerivAt_pi.mp path k) j))
    convert! terms using 1
    simp only [Matrix.mul_apply,Matrix.add_apply,Finset.sum_add_distrib,zero_smul,add_zero,Matrix.zero_apply]
  have near : ∀ᶠt in 𝓝 (0:ℝ),(e+t • h).det≠0 := by
    have continuous:=(StageNineCoframeVariation.coframe_det_contDiff.continuous.continuousAt.comp
      path.continuousAt).eventually_ne (by simpa using nondegenerate)
    exact continuous
  have constant : (fun t : ℝ=>(e+t • h)⁻¹*(e+t • h))=ᶠ[𝓝 (0:ℝ)] (fun _=>1) :=
    near.mono (fun t ht=>Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht))
  have equation : D*e+e⁻¹*h=0 :=
    product.unique ((hasDerivAt_const (0:ℝ) (1:LorentzianCoframe)).congr_of_eventuallyEq constant)
  have multiply:=congrArg (fun a : LorentzianCoframe=>a*e⁻¹) equation
  rw [add_mul,mul_assoc,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr nondegenerate),mul_one,zero_mul] at multiply
  have value : D= -(e⁻¹*h*e⁻¹):=eq_neg_of_add_eq_zero_left multiply
  rw [value] at inverse
  exact inverse

def sourceCoframeCoefficientJet (e h : LorentzianCoframe) (mu : Fin 4) : SourceMatrix :=
  sourceCoframeCoefficientLinear mu (-(e⁻¹*h*e⁻¹))

theorem sourceCoframeCoefficient_derivative (e h : LorentzianCoframe)
    (nondegenerate : e.det≠0) (mu : Fin 4) :
    HasDerivAt (fun t : ℝ=>coefficientMatrix mu (e+t • h))
      (sourceCoframeCoefficientJet e h mu) 0 := by
  have result:=(sourceCoframeCoefficientLinear mu).hasFDerivAt.comp_hasDerivAt 0
    (sourceCoframeInverse_derivative e h nondegenerate)
  convert! result using 1
  funext t
  exact sourceCoframeCoefficientLinear_original (e+t • h) mu

end LowEnergy.PreparationPhysicalNormalizedFullField
