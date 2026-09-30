import H0mework.Physics.LowEnergy.FullQuantum.FullSpace.Principal
import H0mework.Physics.LowEnergyMatterSpace.Connection
import H0mework.Physics.YangMillsSourceQuantum.InsertionSkew

/-! The full 252-dimensional free Hamiltonian is read from the original
physical-time connection. Its positive Hilbert adjoint is proved from source coefficients. -/
set_option autoImplicit false
open scoped Matrix Kronecker InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open PointwiseDiracSpinConnectionLift Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity SU7MotherLieAlgebra
open Triangular SU7ExteriorBreakingYukawa StageNineLorentzConnectionVariationDensity
noncomputable section
local instance : DecidableEq Sector := Classical.decEq _

private theorem temporal_inverse (point : BasePoint) :
    currentCoframeMatterTemporalPrincipalInverse (actual.coframe point) =
      (lapse : ℂ) • (Complex.I • diracMatrixMatterAction diracGammaZero) := by
  rw [actual_coframe]
  have q : coframeTemporalPrincipalScalar (homogeneousCoframe lapse) = (lapse⁻¹)^2 := by
    rw [coframeTemporalPrincipalScalar, homogeneousCoframe_inv lapse lapse_pos.ne']
    simp [homogeneousCoframe, minkowskiInternalSign, Fin.sum_univ_four]
  apply LinearMap.ext
  intro v
  simp only [currentCoframeMatterTemporalPrincipalInverse, q,
    currentCoframeMatterTemporalPrincipal, LinearMap.smul_apply,
    homogeneousInverseGamma lapse lapse_pos.ne',
    diracMatrixMatterAction_smul_matrix, smul_smul]
  congr 1
  push_cast
  field_simp [lapse_pos.ne']

private theorem actual_spatial_gamma (point : BasePoint) (j : Fin 3) :
    inverseCoframeDiracGamma {coframe := actual.coframe point, derivative := 0} j.succ =
      diracGamma j.succ := by
  rw [actual_coframe,homogeneousInverseGamma lapse lapse_pos.ne']
  simp

private theorem time_spin_zero (point : BasePoint) :
    diracSpinConnectionLift (actual.gravityConnection point) 0=0 := by
  rw [actual_gravityConnection]
  simp only [diracSpinConnectionLift,homogeneousConnection,
    StageNineLorentzConnectionVariation.loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  simp [homogeneousContorsion,Fin.sum_univ_six]

def sourceGaugeCoordinates (point : BasePoint) : P286GaugeOneForm :=
  fun mu => p286CoordinateEquiv (actual.gaugeConnection point mu)

theorem sourceGaugeCoordinates_original (point : BasePoint) (mu : LorentzianIndex) :
    p286GaugeConnectionMotherVariation sourceGaugeCoordinates point mu =
      p286LieBlockEmbed (actual.gaugeConnection point mu) := by
  simp [p286GaugeConnectionMotherVariation,sourceGaugeCoordinates]

def principalMother (momentum : Fin 3 → ℝ) : Mother :=
  ∑ j, (-(lapse : ℂ)*(momentum j : ℂ)) • diracMatrixMatterAction (diracGammaZero*diracGamma j.succ)

def spinMother : Mother :=
  (3*(lapse : ℂ)*(spinScale : ℂ)/2) • diracMatrixMatterAction diracGammaFive

def spinRaw (point : BasePoint) : Mother :=
  ((lapse : ℂ)*Complex.I) • ∑ j : Fin 3,
    (diracMatrixMatterAction (diracGammaZero*diracGamma j.succ)).comp
      (diracMatrixMatterAction (diracSpinConnectionLift (actual.gravityConnection point) j.succ))

theorem source_split_raw (point : BasePoint) (momentum : Fin 3 → ℝ) :
    freeHamiltonian actual point momentum = principalMother momentum + spinRaw point +
      Complex.I • YangMills.Response.Forcing.insertion actual sourceGaugeCoordinates point := by
  apply LinearMap.ext
  intro v
  simp only [freeHamiltonian,freeDrift,freeKnown,temporal_inverse,actual_spatial_gamma,
    principalMother,spinRaw,connection,YangMills.Response.Forcing.insertion,
    YangMills.Response.Forcing.spatialInsertion,sourceGaugeCoordinates_original,
    LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,
    LinearMap.sum_apply,LinearMap.comp_apply,Module.End.mul_apply,Module.End.one_apply,
    map_add,map_smul,map_sum,diracMatrixMatterAction_mul,time_spin_zero,
    diracMatrixMatterAction_zero_matrix,zero_add]
  simp only [Finset.sum_add_distrib,Finset.smul_sum,smul_smul]
  simp only [smul_add,smul_sub,smul_neg,Finset.smul_sum,smul_smul]
  have square (z : ℂ) : Complex.I*(Complex.I*z) = -z := by
    rw [← mul_assoc,Complex.I_mul_I,neg_one_mul]
  have paired (z : ℂ) : Complex.I*z*((lapse : ℂ)*Complex.I) = -(lapse : ℂ)*z := by
    calc
      _ = (lapse : ℂ)*z*(Complex.I*Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have minus (z : ℂ) (w : DiracExteriorMatterCarrier) : (-z) • w = -(z • w) := neg_smul z w
  simp only [square,paired,minus,neg_neg,Finset.sum_neg_distrib]
  abel

theorem spinRaw_original (point : BasePoint) : spinRaw point=spinMother := by
  apply LinearMap.ext
  intro v
  have spin := congrArg (fun M : DiracMatrix => diracMatrixMatterAction M v)
    MatterSpace.spin_connection_sum
  have matrix_sum (A : Fin 3 → DiracMatrix) :
      diracMatrixMatterAction (∑ j, A j) v = ∑ j, diracMatrixMatterAction (A j) v := by
    funext index
    simp only [diracMatrixMatterAction,LinearMap.coe_mk,AddHom.coe_mk,
      Matrix.sum_apply,Finset.sum_smul,Finset.sum_apply]
    exact Finset.sum_comm
  simp only [diracMatrixMatterAction_smul_matrix,matrix_sum,
    diracMatrixMatterAction_mul,LinearMap.comp_apply] at spin
  simp only [spinRaw,spinMother,actual_gravityConnection,homogeneousSpinLift,
    LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    diracMatrixMatterAction_smul_matrix,diracMatrixMatterAction_mul,LinearMap.comp_apply,
    map_smul,← Finset.smul_sum,smul_smul]
  have scaled := congrArg (fun w : DiracExteriorMatterCarrier =>
    ((lapse : ℂ)*(spinScale : ℂ)/2) • w) spin
  simp only [smul_smul] at scaled
  convert scaled using 1 <;> congr 1 <;> ring

theorem source_gauge_fixed (point : BasePoint) :
    YangMills.Response.Forcing.insertion actual sourceGaugeCoordinates point =
      YangMills.Response.Forcing.insertion actual sourceGaugeCoordinates 0 := by
  simp only [YangMills.Response.Forcing.insertion,YangMills.Response.Forcing.spatialInsertion,
    sourceGaugeCoordinates_original,actual_coframe,actual_gaugeConnection]

def gaugeMother : Mother :=
  Complex.I • YangMills.Response.Forcing.insertion actual sourceGaugeCoordinates 0

theorem source_free_original (point : BasePoint) (momentum : Fin 3 → ℝ) :
    freeHamiltonian actual point momentum=principalMother momentum+spinMother+gaugeMother := by
  rw [source_split_raw,spinRaw_original,source_gauge_fixed]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
