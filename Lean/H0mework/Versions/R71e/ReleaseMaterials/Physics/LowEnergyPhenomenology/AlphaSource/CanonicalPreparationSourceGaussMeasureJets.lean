import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGeometryCurrentReturn
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussHalfDensity
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumGaussMeasureReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumSpinGaussContraction PreparationVacuumSpinCarReturn
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussHistoryHilbert GaussCoreDifferential
open scoped Topology BigOperators Matrix

theorem sourceDensity_direction (N : ℕ) (z : physicalChart) (j : Fin 6) :
    fderiv ℝ (GaussDensityCore.density N) z.val (GaussCoframeCore.coframeDirection j)=
      2*(N+2:ℝ)*sourceNumberConnection z.val.1 j*GaussDensityCore.density N z.val:=by
  have actual := ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have line := actual.hasLineDerivAt (GaussCoframeCore.coframeDirection j)
  exact line.unique (sourceNumberConnection_density N z j)

theorem sourceComplexDensity_direction (N : ℕ) (z : physicalChart) (j : Fin 6) :
    fderiv ℝ (GaussDensityCore.complexDensity N) z.val (GaussCoframeCore.coframeDirection j)=
      ((2*(N+2:ℝ)*sourceNumberConnection z.val.1 j):ℂ)*GaussDensityCore.complexDensity N z.val:=by
  have density := ((GaussDensityCore.density_smooth N z).differentiableAt (by simp)).hasFDerivAt
  have actual := Complex.ofRealCLM.hasFDerivAt.comp z.val density
  change HasFDerivAt (GaussDensityCore.complexDensity N) _ z.val at actual
  rw [actual.fderiv]
  change (fderiv ℝ (GaussDensityCore.density N) z.val (GaussCoframeCore.coframeDirection j):ℂ)=_
  rw [sourceDensity_direction]
  simp only [GaussDensityCore.complexDensity,Complex.ofReal_mul,Complex.ofReal_ofNat]

-- This ambient function restricts to the original positive source half density.
def sourceHalfDensity (N : ℕ) (z : SourceCoordinateSlice) : ℝ:=
  Real.sqrt (GaussDensityCore.density N z)

theorem sourceHalfDensity_original (N : ℕ) (z : physicalChart) :
    sourceHalfDensity N z.val=GaussHalfDensity.halfDensity N z:=rfl

theorem sourceHalfDensity_generated (N : ℕ) (z : physicalChart) (j : Fin 6) :
    HasDerivAt (fun r : ℝ=>sourceHalfDensity N (sourceCoframeRay z j r))
      ((N+2:ℝ)*sourceNumberConnection z.val.1 j*sourceHalfDensity N z.val) 0:=by
  have densityNonzero : GaussDensityCore.density N (sourceCoframeRay z j 0)≠0:=by
    simpa only [sourceCoframeRay,zero_smul,add_zero] using (GaussDensityCore.density_pos N z).ne'
  have actual := (sourceNumberConnection_density N z j).sqrt densityNonzero
  convert! actual using 1
  simp only [sourceCoframeRay,zero_smul,add_zero,sourceHalfDensity]
  have square := Real.sq_sqrt (GaussDensityCore.density_pos N z).le
  have positive := Real.sqrt_pos.mpr (GaussDensityCore.density_pos N z)
  apply (eq_div_iff (mul_ne_zero (by norm_num) positive.ne')).mpr
  calc
    _=2*(N+2:ℝ)*sourceNumberConnection z.val.1 j*
        (Real.sqrt (GaussDensityCore.density N z.val))^2:=by ring
    _= _:=by rw [square]

theorem sourceWeightedTranspose_generated (N : ℕ) (j : Fin 6)
    (f : GaussDensityCore.ScalarTest) (z : physicalChart) :
    GaussDensityCore.weightedTranspose N (GaussCoframeCore.coframeDirection j) f z.val=
      -fderiv ℝ f z.val (GaussCoframeCore.coframeDirection j)-
        ((2*(N+2:ℝ)*sourceNumberConnection z.val.1 j):ℂ)*f z.val:=by
  have density := (GaussDensityCore.complexDensity_smooth N z).differentiableAt (by simp)
  have test := (f.contDiff.differentiable (by simp)).differentiableAt (x:=z.val)
  rw [GaussDensityCore.weightedTranspose_apply,fderiv_fun_mul density test]
  simp only [add_apply,smul_apply,smul_eq_mul,
    sourceComplexDensity_direction]
  have nonzero : GaussDensityCore.complexDensity N z.val≠0:=by
    change (GaussDensityCore.density N z.val:ℂ)≠0
    exact Complex.ofReal_ne_zero.mpr (GaussDensityCore.density_pos N z).ne'
  field_simp
  ring

end LowEnergy.PreparationVacuumGaussMeasureReturn
