import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationLowerNativeLeaves
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDensityTrace
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumResidualFlow
open GaussHistoryHilbert PreparationCoordinates PreparationChartGuard
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open scoped BigOperators

def originalOrbitBasis : Module.Basis (Fin 3) ℝ stabilizer :=
  (Pi.basisFun ℝ (Fin 3)).map colorStabilizerEquiv
def originalSliceBasis : Module.Basis (Fin 33) ℝ coordinateSlice :=
  (Pi.basisFun ℝ (Fin 33)).map gaugeFree.symm
def originalSplitBasis : Module.Basis ((Fin 3) ⊕ (Fin 33)) ℝ (stabilizer × coordinateSlice) :=
  originalOrbitBasis.prod originalSliceBasis

private theorem originalOrbit_repr (a : stabilizer) (i : Fin 3) :
    originalOrbitBasis.repr a i=colorStabilizerEquiv.symm a i := by
  change (Pi.basisFun ℝ (Fin 3)).repr (colorStabilizerEquiv.symm a) i=_
  exact Pi.basisFun_repr (R:=ℝ) (η:=Fin 3) (colorStabilizerEquiv.symm a) i

private theorem originalSlice_repr (v : coordinateSlice) (i : Fin 33) :
    originalSliceBasis.repr v i=gaugeFree v i := by
  change (Pi.basisFun ℝ (Fin 33)).repr (gaugeFree v) i=_
  exact Pi.basisFun_repr (R:=ℝ) (η:=Fin 33) (gaugeFree v) i

private theorem originalSplit_repr_left (av : stabilizer × coordinateSlice) (i : Fin 3) :
    originalSplitBasis.repr av (Sum.inl i)=colorStabilizerEquiv.symm av.1 i :=
  originalOrbit_repr _ _

private theorem originalSplit_repr_right (av : stabilizer × coordinateSlice) (i : Fin 33) :
    originalSplitBasis.repr av (Sum.inr i)=gaugeFree av.2 i :=
  originalSlice_repr _ _

private theorem originalSplit_left (i : Fin 3) :
    originalSplitBasis (Sum.inl i)=(colorStabilizer (Pi.single i 1),0) := by
  simp only [originalSplitBasis,Module.Basis.prod_apply,Sum.elim_inl,Function.comp_apply,
    LinearMap.inl_apply,originalOrbitBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  rfl

private theorem originalSplit_right (i : Fin 33) :
    originalSplitBasis (Sum.inr i)=(0,gaugeFree.symm (Pi.single i 1)) := by
  simp only [originalSplitBasis,Module.Basis.prod_apply,Sum.elim_inr,Function.comp_apply,
    LinearMap.inr_apply,originalSliceBasis,Module.Basis.map_apply,Pi.basisFun_apply]

theorem relative_slice_identity (A : Gauge) (v : coordinateSlice) : relative A (0,v)=(0,v) := by
  unfold relative combined
  change sourceSplitEquiv.symm (gaugeAction 0 A+(v : Gauge))=(0,v)
  simp only [map_zero,LinearMap.zero_apply,zero_add]
  have forward : sourceSplitEquiv (0,v)=(v : Gauge) := by
    change residualOrbit 0+(v : Gauge)=(v : Gauge)
    simp
  rw [←forward]
  exact sourceSplitEquiv.symm_apply_apply (0,v)

def relativeUpper (A : coordinateSlice) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  colorStabilizerEquiv.symm (relative A.val (colorStabilizer x,0)).1

theorem relativeUpper_generated (A : coordinateSlice) (x : Fin 3 → ℝ) :
    relativeUpper A x=
      ![2*secondGauge A.val/gaugeScale*x 0-
          2*(nativeCoordinates (gaugeCoordinates A.val 1)).1 1/gaugeScale*x 1,
        2*firstGauge A.val/gaugeScale*x 1,
        (nativeCoordinates (gaugeCoordinates A.val 0)).1 7/gaugeScale*x 0+
          2*firstGauge A.val/gaugeScale*x 2] := by
  have equation : orbitRows (residualOrbit (colorStabilizer (relativeUpper A x)))=
      orbitRows (gaugeAction (colorStabilizer x) A.val) := by
    change rowOrbitEquiv (colorStabilizerEquiv (relativeUpper A x))=_
    unfold relativeUpper
    rw [colorStabilizerEquiv.apply_symm_apply]
    change rowOrbitEquiv (rowOrbitEquiv.symm
      (orbitRows (gaugeAction (colorStabilizer x) A.val+(0 : coordinateSlice))))=_
    simp
  rw [residualOrbit_minor_action,variable_rows] at equation
  have e0:=congrFun equation 0
  have e1:=congrFun equation 1
  have e2:=congrFun equation 2
  have nonzero:=gaugeScale_pos.ne'
  ext i
  fin_cases i
  · dsimp at e0 ⊢
    field_simp
    linarith
  · dsimp at e1 ⊢
    field_simp
    linarith
  · dsimp at e2 ⊢
    field_simp
    linarith

def upperMatrix (A : coordinateSlice) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*secondGauge A.val/gaugeScale,-2*(nativeCoordinates (gaugeCoordinates A.val 1)).1 1/gaugeScale,0;
     0,2*firstGauge A.val/gaugeScale,0;
     (nativeCoordinates (gaugeCoordinates A.val 0)).1 7/gaugeScale,0,2*firstGauge A.val/gaugeScale]

def lowerMatrix (A : coordinateSlice) : Matrix (Fin 33) (Fin 3) ℝ := fun i j =>
  gaugeFree (relative A.val (colorStabilizer (Pi.single j 1),0)).2 i

theorem originalRelative_block (A : coordinateSlice) :
    LinearMap.toMatrix originalSplitBasis originalSplitBasis (relative A.val)=
      Matrix.fromBlocks (upperMatrix A) 0 (lowerMatrix A) 1 := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · simp only [LinearMap.toMatrix_apply,originalSplit_left,originalSplit_repr_left,
      Matrix.fromBlocks_apply₁₁]
    change relativeUpper A (Pi.single j 1) i=upperMatrix A i j
    rw [relativeUpper_generated]
    fin_cases i <;> fin_cases j <;> simp [upperMatrix,neg_div]
  · simp only [LinearMap.toMatrix_apply,originalSplit_right,originalSplit_repr_left,
      Matrix.fromBlocks_apply₁₂,Matrix.zero_apply]
    rw [relative_slice_identity]
    simp
  · simp only [LinearMap.toMatrix_apply,originalSplit_left,originalSplit_repr_right,
      Matrix.fromBlocks_apply₂₁,lowerMatrix]
  · simp only [LinearMap.toMatrix_apply,originalSplit_right,originalSplit_repr_right,
      Matrix.fromBlocks_apply₂₂,Matrix.one_apply]
    rw [relative_slice_identity]
    simp [Pi.single_apply]

theorem originalRelative_determinant (A : coordinateSlice) :
    (relativeMatrix A.val).det=8*(firstGauge A.val)^2*secondGauge A.val/gaugeScale^3 := by
  rw [relativeMatrix,LinearMap.det_toMatrix,
    ←LinearMap.det_toMatrix originalSplitBasis,originalRelative_block,
    Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,mul_one]
  rw [upperMatrix,Matrix.det_fin_three]
  simp
  ring

def originalRho3 (A : Gauge) : ℝ := 8*(gaugeRaw A 1)^2*gaugeRaw A 12

theorem originalRho3_native (A : Gauge) :
    originalRho3 A=8*(firstGauge A)^2*secondGauge A := rfl

theorem originalRho3_source :
    originalRho3 SourceQuantumConfigurationHilbert.sourceGauge=gaugeScale^3 := by
  rw [originalRho3_native]
  change 8*(firstGauge SourceQuantumResidualGaugeSlice.sourceGauge)^2*
    secondGauge SourceQuantumResidualGaugeSlice.sourceGauge=_
  change 8*((nativeCoordinates (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge 0)).1 1)^2*
    (nativeCoordinates (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge 1)).1 0=_
  rw [sourceGauge_apply,sourceGauge_apply,map_smul,map_smul,
    colorGenerator_coordinates,colorGenerator_coordinates]
  simp
  ring

theorem originalJacobian_density (A : coordinateSlice) (first : 0<firstGauge A.val)
    (second : 0<secondGauge A.val) :
    jacobian A.val=sourceJacobian*originalRho3 A.val/
      originalRho3 SourceQuantumConfigurationHilbert.sourceGauge := by
  have positive : 0<8*(firstGauge A.val)^2*secondGauge A.val/gaugeScale^3 :=
    div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos first)) second)
      (pow_pos gaugeScale_pos _)
  rw [jacobian,originalRelative_determinant,abs_of_pos positive,
    originalRho3_native,originalRho3_source]
  ring

end LowEnergy.PreparationVacuumDensityTrace
