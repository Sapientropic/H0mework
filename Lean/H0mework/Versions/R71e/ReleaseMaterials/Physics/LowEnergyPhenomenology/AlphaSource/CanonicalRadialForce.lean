import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalRadialSource

/-! Literal full-CAR current and nonlinear magnetic feedback for the same
radial momentum. All Gauss kinetic and weighted-transpose terms remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualRadial
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussLiveMomentum GaussCoreDifferential
open GaussNativePotential GaussNativeEnergy GaussCoreHilbert GaussFockPair
open CanonicalGradedFullForce GaussQuantumMultiplier
open scoped ContDiff Topology RealInnerProductSpace

private theorem test_derivative (f : QuantumTest) (z : SourceCoordinateSlice) :
    HasDerivAt (fun r : ℝ => f (translate z r)) (fderiv ℝ f z shift) 0 := by
  have h := ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt
    0 (translate_derivative z)
  simp only [translate, zero_smul, add_zero, Function.comp_def] at h
  convert! h using 1

theorem multiplier_force (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (z : physicalChart) (slope : FockFiber →L[ℂ] FockFiber)
    (derivative : HasDerivAt (fun r : ℝ => A (translate z.val r)) slope 0)
    (f : QuantumTest) :
    actionForce (localMultiplier A smooth) P f z.val = -slope (f z.val) := by
  let R := ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have ha := R.hasFDerivAt.comp_hasDerivAt 0 derivative
  have hp := ha.clm_apply (test_derivative f z.val)
  have hm := test_derivative (localMultiplier A smooth f) z.val
  have hd : fderiv ℝ (localMultiplier A smooth f) z.val shift =
      slope (f z.val)+A z.val (fderiv ℝ f z.val shift) := by
    have h := hm.unique hp
    simpa only [translate, zero_smul, add_zero, Function.comp_def, R,
      ContinuousLinearMap.coe_restrictScalars] using! h
  change Complex.I • (A z.val (P f z.val)-P (localMultiplier A smooth f) z.val)=_
  rw [P_original, P_original, hd, map_smul]
  simp only [smul_add, smul_sub, smul_smul]
  simp [Complex.I_mul_I]

theorem scalar_force (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val)
    (z : physicalChart) (slope : ℝ)
    (derivative : HasDerivAt (fun r : ℝ => c (translate z.val r)) slope 0)
    (f : QuantumTest) :
    actionForce (GaussNativeForm.multiply c smooth) P f z.val = -(slope : ℂ) • f z.val := by
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 derivative
  have h := multiplier_force (fun w => (c w : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun w => (Complex.ofRealCLM.contDiff.contDiffAt.comp w.val (smooth w)).smul contDiffAt_const)
    z ((slope : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (hc.smul_const (ContinuousLinearMap.id ℂ FockFiber)) f
  simp only [smul_apply, ContinuousLinearMap.id_apply] at h
  convert! h using 1
  rw [neg_smul]

def currentMatrix (i b : Fin 3) (z : SourceCoordinateSlice) : Matrix Mode Mode ℂ :=
  (GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.matrixTerm b (B i)

theorem current_smooth (i b : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => quantized (currentMatrix i b w)) z.val := by
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    (GaussMatterCore.coefficient_smooth i b z)
  have h := hc.smul (contDiffAt_const (c := GaussMatterCore.quantumTerm b (B i)))
  convert h using 1
  funext w
  exact map_smul quantizer _ _

def matterCurrent : CoreEnd := ∑ i : Fin 3, ∑ b : Fin 3,
  action (currentMatrix i b) (current_smooth i b)

theorem current_full504 (z : SourceCoordinateSlice) (f : QuantumTest) :
    matterCurrent f z=∑ i : Fin 3, ∑ b : Fin 3,
      (GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.quantumTerm b (B i) (f z) := by
  simp only [matterCurrent, LinearMap.sum_apply]
  change (∑ i : Fin 3, ∑ b : Fin 3,
    GaussCoreDifferential.localMultiplier
      (fun w => quantized (currentMatrix i b w)) (current_smooth i b) f) z = _
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  change quantizer ((GaussMatterCore.coefficient i b z : ℂ) •
      GaussMatterCore.matrixTerm b (B i)) (f z)=_
  rw [map_smul]
  rfl

theorem matter_local_translate (i b : Fin 3) (z : SourceCoordinateSlice) (r : ℝ) :
    quantized (GaussMatterCore.localMatrix i b (translate z r)) =
      quantized (GaussMatterCore.localMatrix i b z)+r • quantized (currentMatrix i b z) := by
  change quantizer (GaussMatterCore.localMatrix i b (translate z r)) =
    quantizer (GaussMatterCore.localMatrix i b z)+r • quantizer (currentMatrix i b z)
  simp only [GaussMatterCore.localMatrix, GaussMatterCore.coefficient, currentMatrix, translate_coframe,
    connection_translate, map_add, map_smul, smul_add]
  rw [smul_comm]
  have hr : quantizer (r • GaussMatterCore.matrixTerm b (B i)) =
      r • quantizer (GaussMatterCore.matrixTerm b (B i)) :=
    (quantizer.restrictScalars ℝ).map_smul r _
  rw [hr]

theorem matter_force (f : QuantumTest) (z : physicalChart) :
    actionForce GaussMatterCore.matterAction P f z.val = -matterCurrent f z.val := by
  have h (i b : Fin 3) : actionForce (action (GaussMatterCore.localMatrix i b)
      (GaussMatterCore.local_smooth i b)) P f z.val =
      -action (currentMatrix i b) (current_smooth i b) f z.val := by
    apply multiplier_force
    simp only [matter_local_translate]
    simpa only [one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const
      (quantized (currentMatrix i b z.val))).const_add _
  simp only [actionForce, GaussMatterCore.matterAction, matterCurrent, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, sum_apply, smul_apply, sub_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun b _ => h i b))

theorem potential_force (f : QuantumTest) (z : physicalChart) :
    actionForce (GaussNativeForm.multiply potential potential_smooth) P f z.val =
      -(scalarSlopePotential z.val+magneticSlopePotential z.val : ℂ) • f z.val := by
  simpa only [Complex.ofReal_add] using scalar_force potential potential_smooth z _
    ((scalarPotential_derivative z.val).add (magneticPotential_derivative z.val)) f

theorem originalY_force (f : QuantumTest) (z : physicalChart) :
    actionForce GaussYukawaOperator.originalAction P f z.val=0 := by
  have h := multiplier_force (fun w => GaussYukawaCoefficient.sourceMap (scalarField w))
    (fun _ => (GaussYukawaCoefficient.sourceMap.contDiff.comp scalarField_smooth).contDiffAt)
    z 0 (by simpa only [scalarField, translate_scalar] using
      hasDerivAt_const (0 : ℝ) (GaussYukawaCoefficient.sourceMap (scalarField z.val))) f
  simp only [zero_apply, neg_zero] at h
  convert! h using 1

theorem full_force_original : actionForce GaussFullHamiltonian.fullAction P =
    CanonicalGradedFullForce.force ambientDirection := by
  have hY : actionForce GaussYukawaOperator.originalAction P=0 := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    by_cases hz : z ∈ physicalChart
    · exact originalY_force f ⟨z,hz⟩
    · exact image_eq_zero_of_notMem_tsupport (fun h => hz
        ((actionForce GaussYukawaOperator.originalAction P f).tsupport_subset h))
  have split : actionForce GaussFullHamiltonian.fullAction P=
      actionForce GaussDiagonalHistory.diagonalAction P+actionForce GaussYukawaOperator.originalAction P := by
    ext f
    simp only [actionForce, GaussFullHamiltonian.fullAction, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add, smul_add, smul_sub]
    abel
  rw [split,hY,add_zero]
  rfl

theorem full_force_generated (f : QuantumTest) (z : physicalChart) :
    actionForce GaussFullHamiltonian.fullAction P f z.val =
      actionForce (GaussNativeForm.scalarKinetic+GaussNativeForm.gaugeKinetic) P f z.val +
      actionForce GaussCoframeForm.coframeAction P f z.val - matterCurrent f z.val -
      (scalarSlopePotential z.val+magneticSlopePotential z.val : ℂ) • f z.val := by
  rw [full_force_original, CanonicalGradedFullForce.force_complete]
  change actionForce GaussNativeForm.nativeAction P f z.val+
    actionForce GaussCoframeForm.coframeAction P f z.val+
    actionForce GaussMatterCore.matterAction P f z.val=_
  rw [matter_force]
  have h : actionForce GaussNativeForm.nativeAction P=
      actionForce (GaussNativeForm.scalarKinetic+GaussNativeForm.gaugeKinetic) P+
      actionForce (GaussNativeForm.multiply potential potential_smooth) P := by
    ext f
    simp only [actionForce, GaussNativeForm.nativeAction, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add, smul_add, smul_sub]
    abel
  rw [h]
  change (actionForce (GaussNativeForm.scalarKinetic+GaussNativeForm.gaugeKinetic) P f z.val+
      actionForce (GaussNativeForm.multiply potential potential_smooth) P f z.val)+
      actionForce GaussCoframeForm.coframeAction P f z.val+-matterCurrent f z.val=_
  rw [potential_force]
  simp only [neg_smul]
  abel

end LowEnergy.ActualRadial
