import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.History
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Source

/-! A primitive lapse coframe variation is differentiated from the original
coframe-dependent operator, with all spatial momentum retained. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
open DiracExteriorMatterAction DiracCliffordRepresentation FullQuantum
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeLocalDifferentiability
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariationDensity StageNineLorentzConnectionVariationDensity SU7MotherGaugeTheory
open PointwiseDiracSpinConnectionLift Stage9C.Dynamics.Homogeneous
noncomputable section
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

def lapseDirection : LorentzianCoframe := Matrix.diagonal ![1,0,0,0]

theorem lapsePath (point : BasePoint) (epsilon : ℝ) :
    CoframeResponse.coframePath point lapseDirection epsilon=homogeneousCoframe (lapse+epsilon) := by
  rw [CoframeResponse.coframePath,actual_coframe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lapseDirection,homogeneousCoframe]

theorem lapse_temporal_inverse (value : ℝ) (nonzero : value≠0) :
    currentCoframeMatterTemporalPrincipalInverse (homogeneousCoframe value)=
      (Complex.I*(value : ℂ)) • diracMatrixMatterAction diracGammaZero := by
  have q : coframeTemporalPrincipalScalar (homogeneousCoframe value)=(value⁻¹)^2 := by
    rw [coframeTemporalPrincipalScalar,homogeneousCoframe_inv value nonzero]
    simp [homogeneousCoframe,minkowskiInternalSign,Fin.sum_univ_four]
  apply LinearMap.ext
  intro v
  simp only [currentCoframeMatterTemporalPrincipalInverse,q,currentCoframeMatterTemporalPrincipal,
    LinearMap.smul_apply,homogeneousInverseGamma value nonzero,diracMatrixMatterAction_smul_matrix,smul_smul]
  congr 1
  push_cast
  field_simp [nonzero]

theorem source_connection_time_zero (point : BasePoint) : connection actual point 0=0 := by
  have spin : diracSpinConnectionLift (actual.gravityConnection point) 0=0 := by
    rw [actual_gravityConnection]
    simp only [diracSpinConnectionLift,homogeneousConnection,
      StageNineLorentzConnectionVariation.loweredLorentzConnectionCoefficient_ofBivectorOneForm]
    simp [homogeneousContorsion,Fin.sum_univ_six]
  apply LinearMap.ext
  intro v
  simp [connection,spin,actual_gaugeConnection,gaugePotential,diracMatrixMatterAction_zero_matrix,
    p286LieBlockEmbed_zero,diracExteriorMotherLieAction_zero_matrix]

theorem lapse_known (point : BasePoint) (momentum : Fin 3 → ℝ) (value : ℝ) (nonzero : value≠0) :
    knownSymbol (CoframeResponse.coframeConfiguration (homogeneousCoframe value)) point momentum=
      knownSymbol actual point momentum := by
  simp only [knownSymbol,CoframeResponse.coframeConfiguration,connection,actual_coframe,
    homogeneousInverseGamma value nonzero,homogeneousInverseGamma lapse lapse_pos.ne',
    Fin.succ_ne_zero,↓reduceIte,one_smul]

theorem lapse_hamiltonian (point : BasePoint) (momentum : Fin 3 → ℝ) (value : ℝ) (nonzero : value≠0) :
    hamiltonian (CoframeResponse.coframeConfiguration (homogeneousCoframe value)) point momentum=
      ((value : ℂ)/(lapse : ℂ)) • hamiltonian actual point momentum := by
  have connectionSame : connection (CoframeResponse.coframeConfiguration (homogeneousCoframe value)) point 0=
      connection actual point 0 := rfl
  unfold hamiltonian drift
  rw [lapse_known point momentum value nonzero,connectionSame]
  change Complex.I • (-(currentCoframeMatterTemporalPrincipalInverse (homogeneousCoframe value)).comp
      (knownSymbol actual point momentum)-connection actual point 0)=_
  rw [source_connection_time_zero]
  apply LinearMap.ext
  intro v
  simp only [actual_coframe,lapse_temporal_inverse value nonzero,lapse_temporal_inverse lapse lapse_pos.ne',
    LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.zero_apply,
    sub_zero,smul_neg,smul_smul]
  congr 2
  field_simp [Complex.ofReal_ne_zero.mpr lapse_pos.ne']

theorem lapse_force (point : BasePoint) (momentum : Fin 3 → ℝ) :
    CoframeCurrent.currentForce point momentum lapseDirection (actual.coframe point)=
      (lapse : ℂ)⁻¹ • Quantum.operatorMatrix (hamiltonian actual point momentum) := by
  rw [CoframeCurrent.currentForce_actual]
  have derivative := CoframeResponse.original_hamiltonian_parameter point momentum lapseDirection
  have path : (fun epsilon : ℝ => Quantum.operatorMatrix
      (hamiltonian (CoframeResponse.coframeConfiguration (CoframeResponse.coframePath point lapseDirection epsilon)) point momentum))
      =ᶠ[nhds 0] (fun epsilon : ℝ => (((lapse+epsilon : ℝ) : ℂ)/(lapse : ℂ)) •
        Quantum.operatorMatrix (hamiltonian actual point momentum)) := by
    have nz : ∀ᶠ epsilon : ℝ in nhds 0,lapse+epsilon≠0 :=
      (continuous_const.add continuous_id).continuousAt.eventually_ne (by simpa using lapse_pos.ne')
    filter_upwards [nz] with epsilon regular
    rw [lapsePath,lapse_hamiltonian point momentum (lapse+epsilon) regular,map_smul]
  have linear : HasDerivAt (fun epsilon : ℝ => (((lapse+epsilon : ℝ) : ℂ)/(lapse : ℂ)))
      ((lapse : ℂ)⁻¹) 0 := by
    have generated := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id (0 : ℝ)).const_add lapse)).div_const (lapse : ℂ)
    simpa only [Function.comp_apply,Complex.ofRealCLM_apply,Complex.ofReal_one,one_div,id_eq] using generated
  exact derivative.unique ((linear.smul_const _).congr_of_eventuallyEq path)

end
end SaturationMonoid.PhysicsCore.LowEnergy.InducedQuantum
