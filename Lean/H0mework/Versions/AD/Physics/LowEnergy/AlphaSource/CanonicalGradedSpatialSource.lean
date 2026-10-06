import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalGradedLocalCurrent
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Source

/-! Physical Fourier momentum is read from the original temporal inverse and
spatial Dirac principals at the same live Gauss coframe. The independent real
CAR branches retain their opposite Fourier momenta. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedSpatialSource
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussNativeEnergy GaussQuantumMultiplier GaussFockLabel
open DiracCliffordRepresentation DiracExteriorMatterAction
open SU7ExteriorBreakingYukawa
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineHolonomicField
open StageNineP286GaugeConnectionVariationDensity
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
open GaussHistoryHilbert (physicalChart)
open scoped Matrix ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

abbrev PhysicalMomentum := Fin 3 → ℝ

def sourceCoframe (z : SourceCoordinateSlice) : LorentzianCoframe := coframe sourceTime z.1

theorem temporal_gamma (z : physicalChart) :
    inverseCoframeDiracGamma {coframe := sourceCoframe z.val, derivative := 0} 0 =
      ((lapse : ℂ)⁻¹) • diracGammaZero := by
  rw [inverseCoframeDiracGamma, sourceCoframe, coframe_inverse z]
  simp [coframeInverse, source_time_generated, Fin.sum_univ_four, diracGamma]
  ext i j
  change lapse⁻¹ • diracGammaZero i j = ((lapse : ℂ)⁻¹) * diracGammaZero i j
  rw [Complex.real_smul, Complex.ofReal_inv]

theorem spatial_gamma (z : physicalChart) (i : Fin 3) :
    inverseCoframeDiracGamma {coframe := sourceCoframe z.val, derivative := 0} i.succ =
      ∑ b : Fin 3, (triadInverse z.val.1 i b : ℂ) • diracGamma b.succ := by
  rw [inverseCoframeDiracGamma, sourceCoframe, coframe_inverse z]
  fin_cases i <;> simp [coframeInverse, Fin.sum_univ_four, Fin.sum_univ_three]

theorem temporal_square (z : physicalChart) :
    coframeTemporalPrincipalScalar (sourceCoframe z.val) = lapse⁻¹^2 := by
  rw [coframeTemporalPrincipalScalar, sourceCoframe, coframe_inverse z]
  simp [coframeInverse, source_time_generated, Fin.sum_univ_four, minkowskiInternalSign]

theorem temporal_noncharacteristic (z : physicalChart) :
    coframeTemporalPrincipalScalar (sourceCoframe z.val) ≠ 0 := by
  rw [temporal_square]
  exact pow_ne_zero 2 (inv_ne_zero lapse_pos.ne')

theorem temporal_inverse (z : physicalChart) :
    currentCoframeMatterTemporalPrincipalInverse (sourceCoframe z.val) =
      ((lapse : ℂ)*Complex.I) • diracMatrixMatterAction diracGammaZero := by
  apply LinearMap.ext
  intro v
  simp only [currentCoframeMatterTemporalPrincipalInverse, temporal_square,
    currentCoframeMatterTemporalPrincipal, temporal_gamma, LinearMap.smul_apply,
    diracMatrixMatterAction_smul_matrix, smul_smul]
  congr 1
  push_cast
  field_simp [lapse_pos.ne']

def principalMother (z : SourceCoordinateSlice) (p : PhysicalMomentum) : FullQuantum.Mother :=
  -∑ i : Fin 3, ∑ b : Fin 3, ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ) •
    diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b))

theorem source_boost (b : Fin 3) : GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b) =
    (1/2 : ℂ) • (diracGammaZero*diracGamma b.succ) := by
  fin_cases b <;> rfl

theorem principalMother_formula (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    principalMother z p = ∑ i : Fin 3, ∑ b : Fin 3,
      (-(lapse : ℂ)*(p i : ℂ)*(triadInverse z.1 i b : ℂ)) •
        diracMatrixMatterAction (diracGammaZero*diracGamma b.succ) := by
  apply LinearMap.ext
  intro v
  simp only [principalMother, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    source_boost, diracMatrixMatterAction_smul_matrix, smul_smul,
    GaussMatterCore.coefficient, source_time_generated, Complex.ofReal_mul,
    Complex.ofReal_ofNat, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  change -(((p i : ℂ)*(2*(lapse : ℂ)*(triadInverse z.1 i b : ℂ))*(1/2)) •
    diracMatrixMatterAction (diracGammaZero*diracGamma b.succ) v) = _
  calc
    _ = (-((p i : ℂ)*(2*(lapse : ℂ)*(triadInverse z.1 i b : ℂ))*(1/2))) •
        diracMatrixMatterAction (diracGammaZero*diracGamma b.succ) v := (neg_smul _ _).symm
    _ = _ := by congr 1; ring

private theorem double_neg_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a : Fin 3 → ℂ) (v : Fin 3 → E) :
    -(∑ x, (-(a x)) • v x) = ∑ x, a x • v x := by
  simp only [neg_smul, Finset.sum_neg_distrib, neg_neg]

private theorem linear_double_sum {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (L : E →ₗ[ℂ] F)
    (a : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → E) :
    L (-∑ i, ∑ b, a i b • v b) = -∑ i, ∑ b, a i b • L (v b) := by
  simp only [map_neg, map_sum, map_smul]

theorem hamiltonian_momentum_difference (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (p : PhysicalMomentum) :
    FullQuantum.hamiltonian C point p-FullQuantum.hamiltonian C point 0 =
      Complex.I • (currentCoframeMatterTemporalPrincipalInverse (C.coframe point)).comp
        (∑ i : Fin 3, (p i : ℂ) • diracMatrixMatterAction
          (inverseCoframeDiracGamma {coframe := C.coframe point, derivative := 0} i.succ)) := by
  apply LinearMap.ext
  intro v
  simp only [FullQuantum.hamiltonian, FullQuantum.drift, FullQuantum.knownSymbol,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, Module.End.one_apply, Pi.zero_apply,
    Complex.ofReal_zero, mul_zero, zero_smul, zero_add, map_add, map_smul, map_sum,
    Finset.sum_add_distrib, smul_add, smul_sub, smul_neg, Finset.smul_sum, smul_smul]
  have ii (c : ℂ) : Complex.I*(Complex.I*c) = -c := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  simp only [ii, mul_neg]
  abel_nf
  simp only [neg_smul, one_smul]
  exact double_neg_sum (fun x => Complex.I*(p x : ℂ)) (fun x =>
    (currentCoframeMatterTemporalPrincipalInverse (C.coframe point))
      (diracMatrixMatterAction (inverseCoframeDiracGamma
        {coframe := C.coframe point, derivative := 0} x.succ) v))

private theorem action_sum (M : Fin 3 → DiracMatrix) (v : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (∑ i, M i) v = ∑ i, diracMatrixMatterAction (M i) v := by
  funext index
  simp only [diracMatrixMatterAction, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Finset.sum_smul, Finset.sum_apply]
  exact Finset.sum_comm

theorem hamiltonian_source_principal (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (z : physicalChart) (coframe_read : C.coframe point=sourceCoframe z.val) (p : PhysicalMomentum) :
    FullQuantum.hamiltonian C point p-FullQuantum.hamiltonian C point 0 = principalMother z.val p := by
  rw [hamiltonian_momentum_difference, coframe_read, temporal_inverse, principalMother_formula]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    spatial_gamma, action_sum, diracMatrixMatterAction_smul_matrix,
    map_sum, map_smul, Finset.smul_sum, smul_smul, diracMatrixMatterAction_mul,
    LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring_nf
  simp [Complex.I_sq]

def momentumMatrix (z : SourceCoordinateSlice) (p : PhysicalMomentum) : Matrix Mode Mode ℂ :=
  -∑ i : Fin 3, ∑ b : Fin 3, ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ) •
    GaussCoframeSpin.full (Fin.castAdd 4 b)

theorem momentumMatrix_zero (z : SourceCoordinateSlice) : momentumMatrix z 0=0 := by
  simp [momentumMatrix]

theorem momentumMatrix_add (z : SourceCoordinateSlice) (p k : PhysicalMomentum) :
    momentumMatrix z (p+k)=momentumMatrix z p+momentumMatrix z k := by
  simp only [momentumMatrix, Pi.add_apply, add_mul, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib, neg_add]

theorem momentumMatrix_smul (z : SourceCoordinateSlice) (r : ℝ) (p : PhysicalMomentum) :
    momentumMatrix z (r • p)=(r : ℂ) • momentumMatrix z p := by
  simp only [momentumMatrix, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    smul_neg, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_assoc]

theorem momentumMatrix_hermitian (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    (momentumMatrix z p).conjTranspose=momentumMatrix z p := by
  simp only [momentumMatrix, Matrix.conjTranspose_neg, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, GaussCoframeSpin.full_hermitian, Complex.star_def, Complex.conj_ofReal]

theorem momentumMatrix_preserves (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    Preserves (momentumMatrix z p) := by
  intro u v
  simp only [momentumMatrix, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_neg, Finset.mul_sum]
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro b _
  have h := spin_preserves (Fin.castAdd 4 b) u v
  rw [mul_left_comm, h, mul_zero]

def primalMatrix (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ :=
  LowEnergy.Quantum.operatorMatrix (principalMother z p)

theorem primalMatrix_formula (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    primalMatrix z p = -∑ i : Fin 3, ∑ b : Fin 3,
      ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ) • GaussCoframeSpin.primal (Fin.castAdd 4 b) := by
  have generated := linear_double_sum Quantum.operatorMatrix.toLinearMap
    (fun i b => ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ))
    (fun b => diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b)))
  change Quantum.operatorMatrix (-∑ i : Fin 3, ∑ b : Fin 3,
    ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ) •
      diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b))) =
      -∑ i : Fin 3, ∑ b : Fin 3, ((p i*GaussMatterCore.coefficient i b z : ℝ) : ℂ) •
        Quantum.operatorMatrix (diracMatrixMatterAction (GaussCoframeSpin.sourceSpin (Fin.castAdd 4 b))) at generated
  simp only [GaussCoframeSpin.spinLift_source] at generated
  exact generated

private theorem full_boost (b : Fin 3) : GaussCoframeSpin.full (Fin.castAdd 4 b) =
    Matrix.fromBlocks (GaussCoframeSpin.primal (Fin.castAdd 4 b)) 0 0
      ((GaussCoframeSpin.primal (Fin.castAdd 4 b)).map star) := by
  simp only [GaussCoframeSpin.full, Fin.val_castAdd, b.isLt, if_true]
  rfl

theorem momentumMatrix_branches (z : SourceCoordinateSlice) (p : PhysicalMomentum) :
    momentumMatrix z p=Matrix.fromBlocks (primalMatrix z p) 0 0
      (-(primalMatrix z (-p)).map star) := by
  ext u v
  cases u <;> cases v <;>
    simp [momentumMatrix, primalMatrix_formula, full_boost, Matrix.neg_apply,
      Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply]

#print axioms hamiltonian_source_principal
#print axioms momentumMatrix_branches
#print axioms momentumMatrix_preserves
end LowEnergy.CanonicalGradedSpatialSource
