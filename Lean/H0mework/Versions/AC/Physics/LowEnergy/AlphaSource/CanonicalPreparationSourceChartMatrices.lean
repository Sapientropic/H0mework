import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockGuard

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceChartBudget
open SaturationMonoid.PhysicsCore
open PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard PreparationPhaseScalar
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumNativeDimensions
open SourceQuantumResidualFlow SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open GaussLiveMomentum GaussHistoryHilbert
open scoped BigOperators Matrix RealInnerProductSpace

def sourceStabilizer (j : Fin 3) : stabilizer :=
  colorStabilizer (![![0,2,0],![2,0,0],![0,0,-2]] j)

theorem sourceStabilizer_raw (j : Fin 3) :
    rawCoordinates (sourceStabilizer j).val=
      ![Pi.single 0 1,Pi.single 1 1,-Pi.single 6 1+Pi.single 7 1] j := by
  change rawRead (colorCombination (![![0,2,0],![2,0,0],![0,0,-2]] j))=_
  unfold rawRead
  rw [colorCombination_coordinates]
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [Pi.single_apply,Fin.ext_iff]
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

def sourceOrbitMinor (z : SourceCoordinateSlice) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => orbitRows (gaugeAction (sourceStabilizer j) z.2.2.val) (![2,1,0] i)

theorem sourceOrbitMinor_native (z : SourceCoordinateSlice) :
    sourceOrbitMinor z=!![0,-(nativeCoordinates (gaugeCoordinates z.2.2.val 0)).1 7,
        2*firstGauge z.2.2.val;
      2*firstGauge z.2.2.val,0,0;
      2*(nativeCoordinates (gaugeCoordinates z.2.2.val 1)).1 1,-2*secondGauge z.2.2.val,0] := by
  ext i j
  unfold sourceOrbitMinor sourceStabilizer
  rw [variable_rows]
  fin_cases i <;> fin_cases j <;> norm_num
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

theorem sourceOrbitMinor_det (z : SourceCoordinateSlice) :
    (sourceOrbitMinor z).det=-8*(firstGauge z.2.2.val)^2*secondGauge z.2.2.val := by
  rw [sourceOrbitMinor_native,Matrix.det_fin_three]
  simp
  ring

theorem sourceOrbitMinor_j15 (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) :
    (1/15 : ℝ) ≤ -(sourceOrbitMinor (fullCoordinates.symm z)).det := by
  have original := actual_minor_lower z zbox
  have firstPositive : 0 ≤ firstGauge (fullCoordinates.symm z).2.2.val := by linarith [original.1]
  have square := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1/4) original.1
  have firstSquare : 0 ≤ firstGauge (fullCoordinates.symm z).2.2.val*
      firstGauge (fullCoordinates.symm z).2.2.val := mul_nonneg firstPositive firstPositive
  have product := mul_le_mul square original.2 (by norm_num : (0 : ℝ) ≤ 1/4)
    firstSquare
  rw [sourceOrbitMinor_det]
  nlinarith

theorem sourceOrbitMinor_inverse_zero (z : FlatConfiguration)
    (zbox : ∀ i, |z i-flatSource i| ≤ sourceRadius) :
    |((sourceOrbitMinor (fullCoordinates.symm z)).det)⁻¹| ≤ 15 := by
  have guard := sourceOrbitMinor_j15 z zbox
  have negative : (sourceOrbitMinor (fullCoordinates.symm z)).det < 0 := by linarith
  rw [abs_of_neg (inv_lt_zero.mpr negative),←inv_neg]
  have bound := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/15) guard
  norm_num [one_div] at bound
  simpa only [inv_neg] using bound

def sourceNormal (i : Fin 9) : NormalCoordinates := WithLp.toLp 2 (Pi.single i 1)
def sourceBroken (i : Fin 9) : broken :=
  broken.orthogonalProjectionOnto (normalBuild (sourceNormal i))

theorem sourceBroken_orbit (i : Fin 9) : orbit (sourceBroken i).val=orbit (normalBuild (sourceNormal i)) := by
  have difference : normalBuild (sourceNormal i)-(sourceBroken i).val ∈ stabilizer := by
    have orth := broken.sub_starProjection_mem_orthogonal (normalBuild (sourceNormal i))
    simpa only [sourceBroken,broken,Submodule.coe_orthogonalProjectionOnto_apply,
      Submodule.orthogonal_orthogonal] using orth
  have zero : orbit (normalBuild (sourceNormal i)-(sourceBroken i).val)=0 := difference
  rw [map_sub,sub_eq_zero] at zero
  exact zero.symm

def sourceD9 (phi : Scalar) : Matrix (Fin 9) (Fin 9) ℝ :=
  fun i j => inner ℝ (orbit (normalBuild (sourceNormal i))) (action phi (sourceBroken j).val)

theorem sourceD9_consistency (phi : Scalar) (i j : Fin 9) :
    sourceD9 phi i j=inner ℝ (sourceBroken i).val (consistency phi (sourceBroken j)).val := by
  change sourceD9 phi i j=inner ℝ (sourceBroken i) (consistency phi (sourceBroken j))
  rw [consistency_pairing]
  change inner ℝ (orbit (normalBuild (sourceNormal i))) (action phi (sourceBroken j).val)=
    inner ℝ (orbit (sourceBroken i).val) (action phi (sourceBroken j).val)
  rw [sourceBroken_orbit]

theorem sourceD9_zero (i j : Fin 9) : sourceD9 (0 : Scalar) i j=0 := by
  change inner ℝ (orbit (normalBuild (sourceNormal i)))
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (sourceBroken j).val 0)=0
  rw [map_zero,inner_zero_right]

theorem sourceD9_add (phi psi : Scalar) : sourceD9 (phi+psi)=sourceD9 phi+sourceD9 psi := by
  ext i j
  change inner ℝ (orbit (normalBuild (sourceNormal i)))
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (sourceBroken j).val (phi+psi))=_
  rw [map_add,inner_add_right]
  rfl

theorem sourceD9_smul (r : ℝ) (phi : Scalar) : sourceD9 (r • phi)=r • sourceD9 phi := by
  ext i j
  change inner ℝ (orbit (normalBuild (sourceNormal i)))
    (StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (sourceBroken j).val (r • phi))=_
  rw [map_smul,real_inner_smul_right]
  rfl

end LowEnergy.PreparationVacuumSourceChartBudget
