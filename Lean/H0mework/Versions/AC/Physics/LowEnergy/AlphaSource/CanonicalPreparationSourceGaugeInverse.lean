import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceScalarInverse

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceMatrixInverse
open PreparationVacuumSourceChartBudget PreparationChartGuard PreparationPhaseScalar
open PreparationScalarCoordinates PreparationCoordinates SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice SourceQuantumResidualFlow
open GaussLiveMomentum
open CanonicalPreparationCutoff
open scoped BigOperators Matrix RealInnerProductSpace

def sourceStabilizerCoordinates (a : stabilizer) : Fin 3 → ℝ :=
  let v:=colorStabilizerEquiv.symm a
  ![v 1/2,v 0/2,-v 2/2]

theorem sourceStabilizer_expansion (a : stabilizer) :
    a=∑ j : Fin 3,sourceStabilizerCoordinates a j • sourceStabilizer j := by
  obtain ⟨v,rfl⟩:=colorStabilizerEquiv.surjective a
  simp only [sourceStabilizerCoordinates,LinearEquiv.symm_apply_apply]
  change colorStabilizer v=∑ j : Fin 3,
    (![v 1/2,v 0/2,-v 2/2] j) • colorStabilizer (![![0,2,0],![2,0,0],![0,0,-2]] j)
  simp_rw [←map_smul]
  rw [←map_sum]
  apply congrArg colorStabilizer
  ext i
  fin_cases i <;> simp only [Fin.sum_univ_three,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals ring

def stabilizerResidual (a : NativeLie) : stabilizer :=
  ⟨a-(brokenPart a).val,brokenPart_residual a⟩

theorem actual_lie_split (a : NativeLie) :
    a=(brokenPart a).val+(stabilizerResidual a).val := by
  change a=(brokenPart a).val+(a-(brokenPart a).val)
  abel

theorem actual_lie_decomposition (a : NativeLie) :
    a=(brokenPart a).val+
      ∑ j : Fin 3,sourceStabilizerCoordinates (stabilizerResidual a) j •
        (sourceStabilizer j).val := by
  have expanded:=congrArg Subtype.val (sourceStabilizer_expansion (stabilizerResidual a))
  simp only [Submodule.coe_sum,Submodule.coe_smul] at expanded
  rw [←expanded]
  exact actual_lie_split a

def lockedRows (eta : Gauge) : Fin 3 → ℝ :=
  fun i=>orbitRows eta (![2,1,0] i)

theorem sourceMinor_stabilizer_action (z : SourceCoordinateSlice) (a : stabilizer) :
    (PreparationVacuumSourceChartBudget.sourceOrbitMinor z).mulVec
      (sourceStabilizerCoordinates a)=lockedRows (gaugeAction a z.2.2.val) := by
  ext i
  conv_rhs => rw [sourceStabilizer_expansion a]
  simp only [lockedRows,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (∑ j : Fin 3,
    orbitRows (gaugeAction (sourceStabilizer j) z.2.2.val) (![2,1,0] i)*
      sourceStabilizerCoordinates a j)=_
  apply Finset.sum_congr rfl
  intro j _
  ring

def inverseStabilizerCoordinates (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) : Fin 3 → ℝ :=
  sourceStabilizerCoordinates (stabilizerResidual (ambientInverseLie z.val xi eta))

def gaugeRight (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) : Fin 3 → ℝ :=
  lockedRows (eta-nativeGauge (brokenPart (ambientInverseLie z.val xi eta)).val z.val.2.2.val)

theorem actual_M3_equation (z : GaussHistoryHilbert.physicalChart) (xi : Scalar) (eta : Gauge) :
    (PreparationVacuumSourceChartBudget.sourceOrbitMinor z.val).mulVec
      (inverseStabilizerCoordinates z xi eta)=gaugeRight z xi eta := by
  have equation:=congrArg orbitRows (ambient_gauge_inverse_equation z xi eta)
  have tangent : orbitRows (ambientInverseGauge z.val xi eta).val=0 :=
    (ambientInverseGauge z.val xi eta).property
  rw [map_add,tangent,add_zero] at equation
  nth_rw 1 [actual_lie_split (ambientInverseLie z.val xi eta)] at equation
  rw [map_add,LinearMap.add_apply,map_add] at equation
  have residual :
      orbitRows (nativeGauge ((stabilizerResidual (ambientInverseLie z.val xi eta)).val)
        z.val.2.2.val)=
      orbitRows eta-orbitRows (nativeGauge (brokenPart (ambientInverseLie z.val xi eta)).val
        z.val.2.2.val) := by
    change orbitRows (nativeGauge (brokenPart (ambientInverseLie z.val xi eta)).val z.val.2.2.val)+
      orbitRows (nativeGauge ((stabilizerResidual (ambientInverseLie z.val xi eta)).val)
        z.val.2.2.val)=orbitRows eta at equation
    exact eq_sub_of_add_eq' equation
  rw [inverseStabilizerCoordinates,sourceMinor_stabilizer_action]
  ext i
  simpa only [lockedRows,gaugeRight,map_sub,Pi.sub_apply,nativeGauge_stabilizer]
    using congrFun residual (![2,1,0] i)

theorem actual_M3_inverse_coefficients (z : FlatConfiguration)
    (box : ∀ i,|z i-CanonicalPreparationCutoff.flatSource i| ≤ CanonicalPreparationCutoff.sourceRadius)
    (xi : Scalar) (eta : Gauge) :
    inverseStabilizerCoordinates (phaseChart z box) xi eta=
      ((PreparationVacuumSourceChartBudget.sourceOrbitMinor (fullCoordinates.symm z))⁻¹).mulVec
        (gaugeRight (phaseChart z box) xi eta) := by
  let M:=PreparationVacuumSourceChartBudget.sourceOrbitMinor (fullCoordinates.symm z)
  have negative : M.det<0 := by
    have guard:=PreparationVacuumSourceChartBudget.sourceOrbitMinor_j15 z box
    change (1/15 : ℝ)≤-M.det at guard
    linarith
  have regular : IsUnit M.det:=isUnit_iff_ne_zero.mpr negative.ne
  have equation:=actual_M3_equation (phaseChart z box) xi eta
  change M.mulVec (inverseStabilizerCoordinates (phaseChart z box) xi eta)=
    gaugeRight (phaseChart z box) xi eta at equation
  rw [←equation,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ regular,Matrix.one_mulVec]

theorem actual_inverse_lie_reconstruction (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) :
    ambientInverseLie z.val xi eta=
      (∑ i : Fin 9,inverseBrokenCoordinates z xi eta i • (sourceBroken i).val)+
      ∑ j : Fin 3,inverseStabilizerCoordinates z xi eta j • (sourceStabilizer j).val := by
  calc
    _=(brokenPart (ambientInverseLie z.val xi eta)).val+
        ∑ j : Fin 3,inverseStabilizerCoordinates z xi eta j • (sourceStabilizer j).val :=
      actual_lie_decomposition _
    _=_ := by
      have expanded:=congrArg Subtype.val (sourceBroken_expansion
        (brokenPart (ambientInverseLie z.val xi eta)))
      simp only [Submodule.coe_sum,Submodule.coe_smul] at expanded
      rw [expanded]
      rfl

theorem actual_inverse_slice_reconstruction (z : GaussHistoryHilbert.physicalChart)
    (xi : Scalar) (eta : Gauge) :
    (ambientInverseScalar z.val xi eta : Scalar)=
      xi-action (vacuum+(z.val.2.1 : Scalar)) (ambientInverseLie z.val xi eta) ∧
    (ambientInverseGauge z.val xi eta : Gauge)=
      eta-nativeGauge (ambientInverseLie z.val xi eta) z.val.2.2.val := by
  constructor
  · exact eq_sub_of_add_eq' (ambient_scalar_inverse_equation z xi eta)
  · exact eq_sub_of_add_eq' (ambient_gauge_inverse_equation z xi eta)

def matrixBroken (z : FlatConfiguration) (xi : Scalar) : broken :=
  ∑ i : Fin 9,
    (((sourceD9 (vacuum+((fullCoordinates.symm z).2.1 : Scalar)))⁻¹).mulVec
      (orbitPairing xi)) i • sourceBroken i

def matrixGaugeRight (z : FlatConfiguration) (xi : Scalar) (eta : Gauge) : Fin 3 → ℝ :=
  lockedRows (eta-nativeGauge (matrixBroken z xi).val (fullCoordinates.symm z).2.2.val)

def matrixLie (z : FlatConfiguration) (xi : Scalar) (eta : Gauge) : NativeLie :=
  (matrixBroken z xi).val+
    ∑ j : Fin 3,
      (((PreparationVacuumSourceChartBudget.sourceOrbitMinor (fullCoordinates.symm z))⁻¹).mulVec
        (matrixGaugeRight z xi eta)) j • (sourceStabilizer j).val

theorem actual_inverse_broken_matrix (z : FlatConfiguration)
    (box : ∀ i,|z i-CanonicalPreparationCutoff.flatSource i| ≤ CanonicalPreparationCutoff.sourceRadius)
    (xi : Scalar) (eta : Gauge) :
    brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta)=matrixBroken z xi := by
  rw [sourceBroken_expansion (brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta))]
  change (∑ i : Fin 9,inverseBrokenCoordinates (phaseChart z box) xi eta i • sourceBroken i)=_
  rw [actual_D9_inverse_coefficients z box xi eta]
  rfl

theorem actual_inverse_lie_matrix (z : FlatConfiguration)
    (box : ∀ i,|z i-CanonicalPreparationCutoff.flatSource i| ≤ CanonicalPreparationCutoff.sourceRadius)
    (xi : Scalar) (eta : Gauge) :
    ambientInverseLie (fullCoordinates.symm z) xi eta=matrixLie z xi eta := by
  rw [actual_lie_decomposition (ambientInverseLie (fullCoordinates.symm z) xi eta)]
  change (brokenPart (ambientInverseLie (fullCoordinates.symm z) xi eta)).val+
    ∑ j : Fin 3,inverseStabilizerCoordinates (phaseChart z box) xi eta j •
      (sourceStabilizer j).val=matrixLie z xi eta
  rw [actual_M3_inverse_coefficients z box xi eta,actual_inverse_broken_matrix z box xi eta]
  have right : gaugeRight (phaseChart z box) xi eta=matrixGaugeRight z xi eta := by
    unfold gaugeRight matrixGaugeRight
    change lockedRows (eta-nativeGauge (brokenPart (ambientInverseLie (fullCoordinates.symm z)
      xi eta)).val (fullCoordinates.symm z).2.2.val)=_
    rw [actual_inverse_broken_matrix z box xi eta]
  rw [right]
  rfl

/-- All three components of the original Gauss inverse are generated by the two source matrices. -/
theorem actual_inverseL_matrix_formula (z : FlatConfiguration)
    (box : ∀ i,|z i-CanonicalPreparationCutoff.flatSource i| ≤ CanonicalPreparationCutoff.sourceRadius)
    (xi : Scalar) (eta : Gauge) :
    ((inverseL (fullCoordinates.symm z) (xi,eta)).1,
      ((inverseL (fullCoordinates.symm z) (xi,eta)).2.1.val,
       (inverseL (fullCoordinates.symm z) (xi,eta)).2.2.val))=
    (matrixLie z xi eta,
      (xi-action (vacuum+((fullCoordinates.symm z).2.1 : Scalar)) (matrixLie z xi eta),
       eta-nativeGauge (matrixLie z xi eta) (fullCoordinates.symm z).2.2.val)) := by
  have lie:=actual_inverse_lie_matrix z box xi eta
  have slices:=actual_inverse_slice_reconstruction (phaseChart z box) xi eta
  change ambientInverseLie (fullCoordinates.symm z) xi eta=matrixLie z xi eta at lie
  change (ambientInverseScalar (fullCoordinates.symm z) xi eta : Scalar)=
    xi-action (vacuum+((fullCoordinates.symm z).2.1 : Scalar))
      (ambientInverseLie (fullCoordinates.symm z) xi eta) ∧
    (ambientInverseGauge (fullCoordinates.symm z) xi eta : Gauge)=
    eta-nativeGauge (ambientInverseLie (fullCoordinates.symm z) xi eta)
      (fullCoordinates.symm z).2.2.val at slices
  change (ambientInverseLie (fullCoordinates.symm z) xi eta,
    ((ambientInverseScalar (fullCoordinates.symm z) xi eta : Scalar),
     (ambientInverseGauge (fullCoordinates.symm z) xi eta : Gauge)))=_
  rw [slices.1,slices.2,lie]

end LowEnergy.PreparationVacuumSourceMatrixInverse
