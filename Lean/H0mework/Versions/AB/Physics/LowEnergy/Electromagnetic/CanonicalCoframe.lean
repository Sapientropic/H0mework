import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.CanonicalPacket
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.Native
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeCurrent.Primitive

/-! Source Clifford control turns the actual differentiated coframe symbols
and their two-sided Green compositions into physical-space bounded operators. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open MeasureTheory
open scoped Matrix Kronecker InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace Retarded DiracCliffordRepresentation
open Stage9C.Material.SpinPair YangMills.FullPairing ProofFreeRicherAnholonomicSource
open FullQuantum.Triangular
noncomputable section
local instance : DecidableEq Sector := Classical.decEq _

def spinPrincipal (k : Fin 3 → ℝ) : DiracMatrix :=
  ∑ j, (-(lapse : ℂ)*(k j : ℂ)) • (diracGammaZero*diracGamma j.succ)

theorem spinPrincipal_square (k : Fin 3 → ℝ) :
    spinPrincipal k*spinPrincipal k = (((lapse^2*∑ j, (k j)^2 : ℝ) : ℂ)) • (1 : DiracMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinPrincipal,Fin.sum_univ_three,diracGamma,diracGammaZero,diracGammaOne,
      diracGammaTwo,diracGammaThree,Matrix.mul_apply,Fin.sum_univ_four] <;>
    ring_nf <;> simp [Complex.I_sq]

theorem principalMatrix_spin (k : Fin 3 → ℝ) :
    principalMatrix k = spinMatrix (spinPrincipal k) := by
  simp only [principalMatrix, spinPrincipal, Fin.sum_univ_three, spinMatrix,
    Matrix.add_kronecker, Matrix.smul_kronecker]

theorem principalMatrix_square (k : Fin 3 → ℝ) :
    principalMatrix k*principalMatrix k = (((lapse^2*∑ j, (k j)^2 : ℝ) : ℂ)) •
      (1 : Matrix Index Index ℂ) := by
  rw [principalMatrix_spin, spinMatrix, ← Matrix.mul_kronecker_mul,
    spinPrincipal_square, Matrix.one_mul, Matrix.smul_kronecker, Matrix.one_kronecker_one]

def principalOperator (k : Fin 3 → ℝ) : FiberOperators := operator (principalMother k)

theorem principalOperator_selfAdjoint (k : Fin 3 → ℝ) :
    (principalOperator k).adjoint = principalOperator k := by
  rw [principalOperator, principal_operator]
  change star ((Matrix.toEuclideanCLM (n := Index) (𝕜 := ℂ)) (principalMatrix k)) = _
  rw [← map_star]
  congr 1
  exact principalMatrix_hermitian k

theorem principalOperator_square (k : Fin 3 → ℝ) :
    principalOperator k*principalOperator k = (((lapse^2*∑ j, (k j)^2 : ℝ) : ℂ)) •
      (1 : FiberOperators) := by
  rw [principalOperator, principal_operator, ← map_mul, principalMatrix_square, map_smul, map_one]

theorem principal_norm_square (k : Fin 3 → ℝ) (v : Hilbert) :
    ‖principalOperator k v‖^2 = (lapse^2*∑ j, (k j)^2)*‖v‖^2 := by
  have pairing : inner ℂ (principalOperator k v) (principalOperator k v) =
      (((lapse^2*∑ j, (k j)^2 : ℝ) : ℂ))*inner ℂ v v := by
    rw [← ContinuousLinearMap.adjoint_inner_right, principalOperator_selfAdjoint]
    change inner ℂ v ((principalOperator k*principalOperator k) v) = _
    rw [principalOperator_square]
    change inner ℂ v ((((lapse^2*∑ j, (k j)^2 : ℝ) : ℂ)) • v) = _
    rw [inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at pairing
  apply Complex.ofReal_injective
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow, Complex.ofReal_mul] using pairing

theorem momentum_component_bound (k : Fin 3 → ℝ) (v : Hilbert) (j : Fin 3) :
    lapse * |k j| * ‖v‖ ≤ ‖principalOperator k v‖ := by
  have coordinate : (k j)^2 ≤ ∑ i, (k i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (k i)) (Finset.mem_univ j)
  have square : (lapse * |k j| * ‖v‖)^2 ≤ ‖principalOperator k v‖^2 := by
    rw [principal_norm_square]
    calc
      _ = lapse^2*(k j)^2*‖v‖^2 := by rw [mul_pow, mul_pow, sq_abs]
      _ ≤ _ := by gcongr
  exact (sq_le_sq₀ (mul_nonneg (mul_nonneg lapse_pos.le (abs_nonneg _)) (norm_nonneg _))
    (norm_nonneg _)).mp square

def sourceConstant : FiberOperators :=
  operator spinMother+operator gaugeMother+operator (Triangular.interactionHamiltonian actual 0)

theorem fullHamiltonian_split (k : Fin 3 → ℝ) :
    operator (hamiltonian actual 0 k) = principalOperator k+sourceConstant := by
  rw [Triangular.hamiltonian_split, source_free_original]
  simp only [operator_add, principalOperator, sourceConstant]
  abel

def sourceFilter (k : Fin 3 → ℝ) : FiberOperators := value 0 k 0 1
def filterBound : ℝ := 1+couplingNorm 0
def derivativeBound : ℝ := (1+(1+‖sourceConstant‖)*filterBound)/lapse

theorem filterBound_nonnegative : 0 ≤ filterBound := by unfold filterBound couplingNorm; positivity
theorem derivativeBound_nonnegative : 0 ≤ derivativeBound := by
  unfold derivativeBound
  have := filterBound_nonnegative
  have := lapse_pos
  positivity

theorem sourceFilter_bound (k : Fin 3 → ℝ) : ‖sourceFilter k‖ ≤ filterBound := by
  simpa [sourceFilter,filterBound] using value_bound 0 k 0 1 (by norm_num)

theorem sourceFilter_principal (k : Fin 3 → ℝ) :
    principalOperator k*sourceFilter k =
      Complex.I • sourceFilter k-Complex.I • (1 : FiberOperators)-sourceConstant*sourceFilter k := by
  have source := value_kernel_left 0 k 0 1 (by norm_num)
  rw [kernel_original, fullHamiltonian_split] at source
  simp only [spectralParameter, Complex.ofReal_zero, Complex.ofReal_one,
    mul_one, zero_add, sub_mul, add_mul, smul_mul_assoc, one_mul] at source
  dsimp only [sourceFilter]
  rw [(sub_eq_iff_eq_add).mp source]
  abel

theorem sourceFilter_principal_bound (k : Fin 3 → ℝ) :
    ‖principalOperator k*sourceFilter k‖ ≤ 1+(1+‖sourceConstant‖)*filterBound := by
  rw [sourceFilter_principal]
  calc
    _ ≤ ‖Complex.I • sourceFilter k-Complex.I • (1 : FiberOperators)‖+
        ‖sourceConstant*sourceFilter k‖ := norm_sub_le _ _
    _ ≤ (‖Complex.I • sourceFilter k‖+‖Complex.I • (1 : FiberOperators)‖)+
        ‖sourceConstant‖*‖sourceFilter k‖ := add_le_add (norm_sub_le _ _) (norm_mul_le _ _)
    _ ≤ 1+(1+‖sourceConstant‖)*‖sourceFilter k‖ := by
      have identity : ‖(1 : FiberOperators)‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        intro v
        simp
      simp only [norm_smul, Complex.norm_I, one_mul]
      nlinarith
    _ ≤ _ := by gcongr; exact sourceFilter_bound k

theorem sourceFilter_derivative_bound (k : Fin 3 → ℝ) (j : Fin 3) :
    ‖(k j : ℂ) • sourceFilter k‖ ≤ derivativeBound := by
  apply ContinuousLinearMap.opNorm_le_bound _ derivativeBound_nonnegative
  intro v
  have generated := momentum_component_bound k (sourceFilter k v) j
  have upper := (principalOperator k*sourceFilter k).le_opNorm v
  have paid := mul_le_mul_of_nonneg_right (sourceFilter_principal_bound k) (norm_nonneg v)
  have complete := generated.trans (upper.trans paid)
  change ‖(k j : ℂ) • sourceFilter k v‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [derivativeBound, div_mul_eq_mul_div, le_div_iff₀ lapse_pos]
  nlinarith [complete]

def affine (A : Fin 4 → FiberOperators) (k : Fin 3 → ℝ) : FiberOperators :=
  A 0+∑ j, (k j : ℂ) • A j.succ

def affineBound (A : Fin 4 → FiberOperators) : ℝ :=
  ‖A 0‖*filterBound+(∑ j : Fin 3, ‖A j.succ‖)*derivativeBound

theorem affineBound_nonnegative (A : Fin 4 → FiberOperators) : 0 ≤ affineBound A := by
  unfold affineBound
  have := filterBound_nonnegative
  have := derivativeBound_nonnegative
  positivity

theorem affine_filter_bound (A : Fin 4 → FiberOperators) (k : Fin 3 → ℝ) :
    ‖affine A k*sourceFilter k‖ ≤ affineBound A := by
  have same : affine A k*sourceFilter k = A 0*sourceFilter k+
      ∑ j : Fin 3, A j.succ*((k j : ℂ) • sourceFilter k) := by
    simp only [affine, add_mul, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
  rw [same]
  calc
    _ ≤ ‖A 0*sourceFilter k‖+‖∑ j : Fin 3, A j.succ*((k j : ℂ) • sourceFilter k)‖ := norm_add_le _ _
    _ ≤ ‖A 0‖*filterBound+∑ j : Fin 3, ‖A j.succ‖*derivativeBound := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (sourceFilter_bound k) (norm_nonneg _))
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left (sourceFilter_derivative_bound k j) (norm_nonneg _))
    _ = _ := by rw [affineBound, Finset.sum_mul]

def filteredCoefficients (A : Fin 4 → FiberOperators) (x : Position) : FiberOperators :=
  affine A (physicalMomentum x)*sourceFilter (physicalMomentum x)

theorem filteredCoefficients_continuous (A : Fin 4 → FiberOperators) :
    Continuous (filteredCoefficients A) := by
  have first : Continuous (fun k : Fin 3 → ℝ => affine A k) := by unfold affine; fun_prop
  exact (first.mul (value_continuous 0 0 1 (by norm_num))).comp physicalMomentum_continuous

def momentumLeg (A : Fin 4 → FiberOperators) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (filteredCoefficients A) (filteredCoefficients_continuous A) (affineBound A)
    (fun x => affine_filter_bound A (physicalMomentum x)) (affineBound_nonnegative A)

def spatialLeg (A : Fin 4 → FiberOperators) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumLeg A).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem spatialLeg_norm (A : Fin 4 → FiberOperators) : ‖spatialLeg A‖ ≤ affineBound A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (affineBound_nonnegative A)
  intro field
  change ‖fourier.symm (momentumLeg A (fourier field))‖ ≤ _
  rw [fourier.symm.norm_map]
  calc
    _ ≤ ‖momentumLeg A‖*‖fourier field‖ := (momentumLeg A).le_opNorm _
    _ ≤ affineBound A*‖field‖ := by
      rw [fourier.norm_map]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact multiplier_norm (filteredCoefficients A) (filteredCoefficients_continuous A)
        (affineBound A) (fun x => affine_filter_bound A (physicalMomentum x)) (affineBound_nonnegative A)

theorem spatialLeg_fourier (A : Fin 4 → FiberOperators) (field : FullMatterL2) :
    fourier (spatialLeg A field) =ᵐ[volume]
      fun x => affine A (physicalMomentum x) (sourceFilter (physicalMomentum x) (fourier field x)) := by
  change fourier (fourier.symm (momentumLeg A (fourier field))) =ᵐ[volume] _
  rw [fourier.apply_symm_apply]
  exact multiplierValue_ae (filteredCoefficients A) (filteredCoefficients_continuous A)
    (affineBound A) (fun x => affine_filter_bound A (physicalMomentum x)) (fourier field)

section Coframe
open StageNineHolonomicField CoframeResponse StateGreen
open scoped Matrix.Norms.L2Operator ContDiff
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

theorem lowerMatrix_affine (k : Fin 3 → ℝ) (e : LorentzianCoframe) :
    lowerMatrix 0 k e = lowerMatrix 0 0 e+
      ∑ j : Fin 3, (Complex.I*(k j : ℂ)) • coefficientMatrix j.succ e := by
  rw [lowerMatrix_coefficients, lowerMatrix_coefficients]
  simp only [Pi.zero_apply, Complex.ofReal_zero, mul_zero, zero_smul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Finset.sum_add_distrib]
  abel

def coefficientJet (h : LorentzianCoframe) (mu : Fin 4) : SourceMatrix :=
  fderiv ℝ (coefficientMatrix mu) (actual.coframe 0) h

theorem coefficientJet_parameter (h : LorentzianCoframe) (mu : Fin 4) :
    HasDerivAt (fun t => coefficientMatrix mu (coframePath 0 h t)) (coefficientJet h mu) 0 := by
  have smooth := (coefficientMatrix_smooth mu (actual.coframe 0)
    (actual_coframe_nondegenerate 0)).differentiableAt (by simp)
  exact smooth.hasFDerivAt.comp_hasDerivAt_of_eq 0 (coframePath_derivative 0 h)
    (coframePath_zero 0 h).symm

theorem lowerDirection_affine (h : LorentzianCoframe) (k : Fin 3 → ℝ) :
    lowerDirection 0 k h = lowerDirection 0 0 h+
      ∑ j : Fin 3, (Complex.I*(k j : ℂ)) • coefficientJet h j.succ := by
  have generated := (lower_parameter 0 0 h).add
    (HasDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      (coefficientJet_parameter h j.succ).const_smul (Complex.I*(k j : ℂ))))
  have same : (fun t => lowerMatrix 0 0 (coframePath 0 h t)+
      ∑ j : Fin 3, (Complex.I*(k j : ℂ)) • coefficientMatrix j.succ (coframePath 0 h t)) =
      (fun t => lowerMatrix 0 k (coframePath 0 h t)) := by
    funext t
    exact (lowerMatrix_affine k (coframePath 0 h t)).symm
  have generated' : HasDerivAt
      (fun t => lowerMatrix 0 0 (coframePath 0 h t)+
        ∑ j : Fin 3, (Complex.I*(k j : ℂ)) • coefficientMatrix j.succ (coframePath 0 h t))
      (lowerDirection 0 0 h+∑ j : Fin 3, (Complex.I*(k j : ℂ)) • coefficientJet h j.succ) 0 := by
    convert! generated using 1
  rw [same] at generated'
  exact (lower_parameter 0 k h).unique generated'

def densitySpatialJet (h : LorentzianCoframe) (j : Fin 3) : SourceMatrix :=
  Complex.I • (((|(actual.coframe 0).det| : ℝ) : ℂ) • coefficientJet h j.succ+
    (volumeDirection 0 h : ℂ) • coefficientMatrix j.succ (actual.coframe 0))

theorem densitizedLower_affine (h : LorentzianCoframe) (k : Fin 3 → ℝ) :
    densitizedLowerDirection 0 k h = densitizedLowerDirection 0 0 h+
      ∑ j : Fin 3, (k j : ℂ) • densitySpatialJet h j := by
  rw [densitizedLowerDirection, lowerDirection_affine, lowerMatrix_affine]
  simp only [densitizedLowerDirection, densitySpatialJet, smul_add, Finset.smul_sum,
    smul_smul, Finset.sum_add_distrib]
  have coeff (a : ℂ) (j : Fin 3) : a*(Complex.I*(k j : ℂ)) = (k j : ℂ)*(Complex.I*a) := by ring
  simp only [coeff]
  abel

def hamiltonianSpatial (j : Fin 3) : SourceMatrix :=
  Ring.inverse (CoframeResponse.principalMatrix (actual.coframe 0))*
    coefficientMatrix j.succ (actual.coframe 0)

theorem coframeHamiltonian_affine (k : Fin 3 → ℝ) :
    coframeHamiltonian 0 k (actual.coframe 0) =
      coframeHamiltonian 0 0 (actual.coframe 0)+∑ j : Fin 3, (k j : ℂ) • hamiltonianSpatial j := by
  unfold coframeHamiltonian timeSymbol
  conv_lhs => rw [lowerMatrix_affine]
  simp only [Matrix.mul_add,
    Matrix.mul_sum, Matrix.mul_smul, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold hamiltonianSpatial
  have scalar : -Complex.I*(Complex.I*(k j : ℂ)) = (k j : ℂ) := by
    rw [← mul_assoc]
    simp
  rw [scalar]

def coframeDensityCoefficients (h : LorentzianCoframe) : Fin 4 → SourceMatrix :=
  Fin.cases
    (densitizedLowerDirection 0 0 h-Complex.I •
      (densitizedPrincipalDirection 0 h*coframeHamiltonian 0 0 (actual.coframe 0)))
    (fun j => densitySpatialJet h j-Complex.I •
      (densitizedPrincipalDirection 0 h*hamiltonianSpatial j))

theorem coframeDensityCoefficients_original (h : LorentzianCoframe) (k : Fin 3 → ℝ) :
    coframeDensityCoefficients h 0+∑ j : Fin 3, (k j : ℂ) • coframeDensityCoefficients h j.succ =
      onShellVertex (densitizedPrincipalDirection 0 h) (densitizedLowerDirection 0 k h)
        (coframeHamiltonian 0 k (actual.coframe 0)) := by
  unfold onShellVertex
  conv_rhs => rw [densitizedLower_affine h k, coframeHamiltonian_affine k]
  simp only [coframeDensityCoefficients, Fin.cases_zero, Fin.cases_succ, Matrix.mul_add, Matrix.mul_sum,
    Matrix.mul_smul, smul_add, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
  have commute (j : Fin 3) : (k j : ℂ)*Complex.I = Complex.I*(k j : ℂ) := mul_comm _ _
  simp only [commute]
  abel

def canonicalMatrixRead : SourceMatrix →ₗ[ℂ] FiberOperators where
  toFun M := operator (Stage10.CanonicalMatter.phaseInverse*
    Quantum.operatorMatrix.toLinearEquiv.symm M)
  map_add' A B := by simp only [map_add, mul_add, operator_add]
  map_smul' a A := by simp only [map_smul, mul_smul_comm, operator_smul]; rfl

def coframeCoefficients (h : LorentzianCoframe) : Fin 4 → FiberOperators :=
  fun i => canonicalMatrixRead (coframeDensityCoefficients h i)

theorem coframeCoefficients_original (h : LorentzianCoframe) (k : Fin 3 → ℝ) :
    affine (coframeCoefficients h) k = canonicalMatrixRead
      (onShellVertex (densitizedPrincipalDirection 0 h) (densitizedLowerDirection 0 k h)
        (coframeHamiltonian 0 k (actual.coframe 0))) := by
  rw [← coframeDensityCoefficients_original]
  simp only [map_add, map_sum, map_smul, coframeCoefficients, affine]

/-- No boundedness premise is supplied: the original coframe density and the
source Clifford/Green estimates construct the physical-space operator. -/
def coframeLeg (h : LorentzianCoframe) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  spatialLeg (coframeCoefficients h)

theorem coframeLeg_original (h : LorentzianCoframe) (field : FullMatterL2) :
    fourier (coframeLeg h field) =ᵐ[volume] fun x =>
      canonicalMatrixRead
        (onShellVertex (densitizedPrincipalDirection 0 h)
          (densitizedLowerDirection 0 (physicalMomentum x) h)
          (coframeHamiltonian 0 (physicalMomentum x) (actual.coframe 0)))
        (sourceFilter (physicalMomentum x) (fourier field x)) := by
  simpa only [coframeLeg, coframeCoefficients_original] using spatialLeg_fourier (coframeCoefficients h) field

open DiracExteriorMatterAction StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction SU7MotherLieAlgebra
open PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation

/-- Physical field directions, before applying the original spin/gauge actions. -/
structure FieldDirection where
  coframe : LorentzianCoframe
  lorentz : LorentzBivectorOneForm
  gauge : Fin 4 → P286LieBlockData
  scalar : ScalarCoordinateCarrier

def connectionDirection (d : FieldDirection) (mu : Fin 4) : SourceMatrix :=
  Quantum.operatorMatrix
    (diracMatrixMatterAction (diracSpinConnectionLift
      (lorentzSkewConnectionOfBivectorOneForm d.lorentz) mu)+
      diracExteriorMotherLieAction (p286LieBlockEmbed (d.gauge mu)))

def scalarDirection (d : FieldDirection) : SourceMatrix :=
  Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm d.scalar))

def sourceVolume : ℂ := (|(actual.coframe 0).det| : ℝ)
def sourceConnection (mu : Fin 4) : SourceMatrix := Quantum.operatorMatrix (connection actual 0 mu)
def sourceScalar : SourceMatrix :=
  Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar 0)))

def fieldDensityCoefficients (d : FieldDirection) (i : Fin 4) : SourceMatrix :=
  coframeDensityCoefficients d.coframe i +
    if i=0 then sourceVolume • ((∑ mu : Fin 4,
      coefficientMatrix mu (actual.coframe 0)*connectionDirection d mu)+scalarDirection d) else 0

def fieldCoefficients (d : FieldDirection) : Fin 4 → FiberOperators :=
  fun i => canonicalMatrixRead (fieldDensityCoefficients d i)

def fieldLeg (d : FieldDirection) : FullMatterL2 →L[ℂ] FullMatterL2 := spatialLeg (fieldCoefficients d)

theorem fieldLeg_original (d : FieldDirection) (field : FullMatterL2) :
    fourier (fieldLeg d field) =ᵐ[volume] fun x =>
      affine (fieldCoefficients d) (physicalMomentum x)
        (sourceFilter (physicalMomentum x) (fourier field x)) :=
  spatialLeg_fourier (fieldCoefficients d) field

def coefficientJetAt (h : LorentzianCoframe) (mu : Fin 4) (e : LorentzianCoframe) : SourceMatrix :=
  fderiv ℝ (coefficientMatrix mu) e h

def coefficientSecond (reader force : LorentzianCoframe) (mu : Fin 4) : SourceMatrix :=
  fderiv ℝ (coefficientJetAt reader mu) (actual.coframe 0) force

theorem coefficientSecond_parameter (reader force : LorentzianCoframe) (mu : Fin 4) :
    HasDerivAt (fun t => coefficientJetAt reader mu (coframePath 0 force t))
      (coefficientSecond reader force mu) 0 := by
  have smooth := (coefficientMatrix_smooth mu (actual.coframe 0)
    (actual_coframe_nondegenerate 0)).fderiv_right (m := ∞) (by simp)
  have applied := smooth.clm_apply (contDiffAt_const (c := reader))
  exact (applied.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (coframePath_derivative 0 force) (coframePath_zero 0 force).symm

def volumeJetAt (h : LorentzianCoframe) (e : LorentzianCoframe) : ℝ :=
  fderiv ℝ (fun e : LorentzianCoframe => |e.det|) e h

def volumeSecond (reader force : LorentzianCoframe) : ℝ :=
  fderiv ℝ (volumeJetAt reader) (actual.coframe 0) force

theorem volumeSecond_parameter (reader force : LorentzianCoframe) :
    HasDerivAt (fun t => volumeJetAt reader (coframePath 0 force t))
      (volumeSecond reader force) 0 := by
  have smooth := (StageNineCoframeVariation.coframe_volume_contDiffAt (actual.coframe 0)
    (actual_coframe_nondegenerate 0)).fderiv_right (m := ∞) (by simp)
  have applied := smooth.clm_apply (contDiffAt_const (c := reader))
  exact (applied.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (coframePath_derivative 0 force) (coframePath_zero 0 force).symm

def densityPrincipalJet (d : FieldDirection) (mu : Fin 4) : SourceMatrix :=
  sourceVolume • coefficientJet d.coframe mu+
    (volumeDirection 0 d.coframe : ℂ) • coefficientMatrix mu (actual.coframe 0)

def densityPrincipalSecond (reader force : FieldDirection) (mu : Fin 4) : SourceMatrix :=
  sourceVolume • coefficientSecond reader.coframe force.coframe mu+
    (volumeDirection 0 reader.coframe : ℂ) • coefficientJet force.coframe mu+
    (volumeDirection 0 force.coframe : ℂ) • coefficientJet reader.coframe mu+
    (volumeSecond reader.coframe force.coframe : ℂ) • coefficientMatrix mu (actual.coframe 0)

def fieldHamiltonianCoefficients (d : FieldDirection) (i : Fin 4) : SourceMatrix :=
  (-Complex.I*sourceVolume⁻¹) •
    (Ring.inverse (CoframeResponse.principalMatrix (actual.coframe 0))*fieldDensityCoefficients d i)

def sourceHamiltonianCoefficients : Fin 4 → SourceMatrix :=
  Fin.cases (coframeHamiltonian 0 0 (actual.coframe 0)) hamiltonianSpatial

def mixedLowerZero (reader force : FieldDirection) : SourceMatrix :=
  (∑ mu : Fin 4,
    (densityPrincipalSecond reader force mu*sourceConnection mu+
      densityPrincipalJet reader mu*connectionDirection force mu+
      densityPrincipalJet force mu*connectionDirection reader mu))+
    (volumeSecond reader.coframe force.coframe : ℂ) • sourceScalar+
    (volumeDirection 0 reader.coframe : ℂ) • scalarDirection force+
    (volumeDirection 0 force.coframe : ℂ) • scalarDirection reader

def mixedDensityCoefficients (reader force : FieldDirection) (i : Fin 4) : SourceMatrix :=
  (Fin.cases (mixedLowerZero reader force)
    (fun j => Complex.I • densityPrincipalSecond reader force j.succ) i)-
    Complex.I • (densityPrincipalSecond reader force 0*sourceHamiltonianCoefficients i)

def shellContactCoefficients (reader force : FieldDirection) (i : Fin 4) : SourceMatrix :=
  (-Complex.I) • (densityPrincipalJet reader 0*fieldHamiltonianCoefficients force i)

def mixedCoefficients (reader force : FieldDirection) : Fin 4 → FiberOperators :=
  fun i => canonicalMatrixRead
    (mixedDensityCoefficients reader force i+shellContactCoefficients reader force i)

def mixedLeg (reader force : FieldDirection) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  spatialLeg (mixedCoefficients reader force)

theorem mixedLeg_original (reader force : FieldDirection) (field : FullMatterL2) :
    fourier (mixedLeg reader force field) =ᵐ[volume] fun x =>
      affine (mixedCoefficients reader force) (physicalMomentum x)
        (sourceFilter (physicalMomentum x) (fourier field x)) :=
  spatialLeg_fourier (mixedCoefficients reader force) field

end Coframe

theorem sourceFilter_original (k : Fin 3 → ℝ) :
    diracValue 0 k 0 1*
      operator (StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipal (actual.coframe 0)) =
      sourceFilter k := by
  rw [diracValue_side 0 k 0 1 (by norm_num), mul_assoc, ← operator_mul]
  have identity : StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipalInverse
        (actual.coframe 0)*
      StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipal (actual.coframe 0) = 1 := by
    apply LinearMap.ext
    intro v
    exact StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipalInverse_left
      _ (actual_noncharacteristic 0) v
  rw [identity]
  have one : operator (1 : YangMills.FullPairing.Mother) = (1 : FiberOperators) := by ext v; simp [operator]
  rw [one, mul_one]
  rfl

theorem canonicalRawFilter_fourier (field : FullMatterL2) :
    fourier (CanonicalPacket.rawFilter 0 1 (by norm_num) field) =ᵐ[volume]
      fun x => sourceFilter (physicalMomentum x) (fourier field x) := by
  have generated := SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (principal 0 field)
  rw [GaugeGreen.principal_fourier] at generated
  filter_upwards [generated, GaugeGreen.principal_ae 0 (fourier field)] with x greenValue principalValue
  change fourier (SpatialGreen.green 0 0 1 (by norm_num) (principal 0 field)) x = _
  rw [greenValue, principalValue]
  change (diracValue 0 (physicalMomentum x) 0 1*
    operator (StageNineCurrentCoframeMatterTemporalPrincipal.currentCoframeMatterTemporalPrincipal (actual.coframe 0)))
    (fourier field x) = _
  rw [sourceFilter_original]

def coordinateCoefficients (i : Fin 4) : Fin 4 → FiberOperators := fun j => if j=i then 1 else 0
def coordinateLeg (i : Fin 4) : FullMatterL2 →L[ℂ] FullMatterL2 := spatialLeg (coordinateCoefficients i)

theorem coordinateLeg_zero : coordinateLeg 0 = CanonicalPacket.rawFilter 0 1 (by norm_num) := by
  apply ContinuousLinearMap.ext
  intro field
  apply fourier.injective
  apply Lp.ext
  filter_upwards [spatialLeg_fourier (coordinateCoefficients 0) field,
    canonicalRawFilter_fourier field] with x first second
  change fourier (spatialLeg (coordinateCoefficients 0) field) x = _
  rw [first, second]
  simp [affine, coordinateCoefficients]

def shiftCoefficients (A : Fin 4 → FiberOperators) (shift : Fin 3 → ℝ) : Fin 4 → FiberOperators :=
  Fin.cases (A 0+∑ j : Fin 3, (shift j : ℂ) • A j.succ) (fun j => A j.succ)

def adjointCoefficients (A : Fin 4 → FiberOperators) : Fin 4 → FiberOperators := fun i => (A i).adjoint

local instance : NormedAlgebra ℚ FiberOperators := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : DecidableEq Quantum.Index := Classical.decEq _

def shiftMatrices (shift : Fin 3 → ℝ) (time : ℝ) (x : Position) : FiberOperators :=
  evolution actual 0 (fun j => physicalMomentum x j+shift j) time

theorem shiftMatrices_continuous (shift : Fin 3 → ℝ) (time : ℝ) :
    Continuous (shiftMatrices shift time) := by
  have momentum : Continuous (fun x : Position => fun j => physicalMomentum x j+shift j) := by
    exact physicalMomentum_continuous.add continuous_const
  have drift := (original_drift_continuous 0).comp momentum
  exact NormedSpace.exp_continuous.comp ((continuous_const (y := time)).smul drift)

theorem shiftMatrices_bound (shift : Fin 3 → ℝ) (time : ℝ) (x : Position) :
    ‖shiftMatrices shift time x‖ ≤ 1+|time| * sourceRate 0 :=
  complete_evolution_bound actual 0 (fun j => physicalMomentum x j+shift j)
    (original_freeHamiltonian_selfAdjoint 0 _) time

def momentumShiftFlow (shift : Fin 3 → ℝ) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (shiftMatrices shift time) (shiftMatrices_continuous shift time)
    (1+|time| * sourceRate 0) (shiftMatrices_bound shift time) (by unfold sourceRate; positivity)

def shiftFlow (shift : Fin 3 → ℝ) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumShiftFlow shift time).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem shiftFlow_fourier (shift : Fin 3 → ℝ) (time : ℝ) (field : FullMatterL2) :
    fourier (shiftFlow shift time field) =ᵐ[volume] fun x =>
      evolution actual 0 (fun j => physicalMomentum x j+shift j) time (fourier field x) := by
  change fourier (fourier.symm (momentumShiftFlow shift time (fourier field))) =ᵐ[volume] _
  rw [fourier.apply_symm_apply]
  exact multiplierValue_ae (shiftMatrices shift time) (shiftMatrices_continuous shift time)
    (1+|time| * sourceRate 0) (shiftMatrices_bound shift time) (fourier field)

def orderedLeft (A : Fin 4 → FiberOperators) (shift : Fin 3 → ℝ) (time age : ℝ) (i : Fin 4) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
    (coordinateLeg i).adjoint*spatialFlow 0 (-time)*
      ((shiftCoefficients A shift i).compLpL 2 volume)*shiftFlow shift (time-age)

def orderedRight (B : Fin 4 → FiberOperators) (age : ℝ) (j : Fin 4) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  ((B j).compLpL 2 volume)*spatialFlow 0 age*coordinateLeg j

/-- The finite coordinate expansion keeps both unbounded affine insertions
inside the two original source filters. No graph-domain product is assumed. -/
def orderedWord (A B : Fin 4 → FiberOperators) (shift : Fin 3 → ℝ) (time age : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  ∑ i : Fin 4, ∑ j : Fin 4, orderedLeft A shift time age i*orderedRight B age j

open MatterSpace.SpatialCAR

def orderedTests (momentum : Fin 3 → ℝ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) (i j : Fin 4) : Fin 2 → FullMatterL2 :=
  ![(orderedLeft A shift time age i).adjoint (CanonicalPacket.packet momentum),
    orderedRight B age j (CanonicalPacket.packet momentum)]

def orderedCARRead (momentum : Fin 3 → ℝ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) (i j : Fin 4) : ℂ :=
  Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
    (Stage9DEF.Compatibility.responseMatrix (CanonicalPacket.mother momentum
      (wordObservable (CanonicalPacket.packet momentum) (orderedTests momentum A B shift time age i j)
        [.create none, .annihilate (some 0), .create (some 1), .annihilate none])))

theorem orderedCARRead_original (momentum : Fin 3 → ℝ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) (i j : Fin 4) :
    orderedCARRead momentum A B shift time age i j =
      inner ℂ (CanonicalPacket.packet momentum)
        (orderedLeft A shift time age i (orderedRight B age j (CanonicalPacket.packet momentum))) := by
  rw [orderedCARRead, CanonicalPacket.mother_fullWord, spatialMoment_fourPoint]
  simp only [family, orderedTests, Matrix.cons_val_zero, Matrix.cons_val_one,
    inner_self_eq_norm_sq_to_K, CanonicalPacket.packet_unit, ContinuousLinearMap.adjoint_inner_left]
  norm_num

theorem orderedWord_fullCAR (momentum : Fin 3 → ℝ) (A B : Fin 4 → FiberOperators)
    (shift : Fin 3 → ℝ) (time age : ℝ) :
    inner ℂ (CanonicalPacket.packet momentum) (orderedWord A B shift time age (CanonicalPacket.packet momentum)) =
      ∑ i : Fin 4, ∑ j : Fin 4, orderedCARRead momentum A B shift time age i j := by
  simp only [orderedWord, sum_apply, inner_sum, orderedCARRead_original,
    mul_apply_eq_comp]

def contactWord (C : Fin 4 → FiberOperators) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  ∑ j : Fin 4, (coordinateLeg 0).adjoint*spatialFlow 0 (-time)*
    ((C j).compLpL 2 volume)*spatialFlow 0 time*coordinateLeg j

structure ComplexDirection where
  realPart : FieldDirection
  imaginaryPart : FieldDirection

structure TransferPair where
  positive : ComplexDirection
  negative : ComplexDirection

def complexCoefficients (d : ComplexDirection) : Fin 4 → FiberOperators :=
  fun i => fieldCoefficients d.realPart i+Complex.I • fieldCoefficients d.imaginaryPart i

def frequencyCoefficients (d : FieldDirection) : Fin 4 → FiberOperators :=
  fun i => operator (Quantum.operatorMatrix.toLinearEquiv.symm (fieldHamiltonianCoefficients d i))

def complexFrequencyCoefficients (d : ComplexDirection) : Fin 4 → FiberOperators :=
  fun i => frequencyCoefficients d.realPart i+Complex.I • frequencyCoefficients d.imaginaryPart i

def complexMixedCoefficients (A B : ComplexDirection) : Fin 4 → FiberOperators :=
  fun i => mixedCoefficients A.realPart B.realPart i-mixedCoefficients A.imaginaryPart B.imaginaryPart i+
    Complex.I • (mixedCoefficients A.realPart B.imaginaryPart i+mixedCoefficients A.imaginaryPart B.realPart i)

def realReaderCoefficients (A : TransferPair) (shift : Fin 3 → ℝ) : Fin 4 → FiberOperators :=
  fun i => (2 : ℂ)⁻¹ • (complexCoefficients A.negative i+
    adjointCoefficients (shiftCoefficients (complexCoefficients A.positive) (-shift)) i)

def realMixedCoefficients (A B : TransferPair) : Fin 4 → FiberOperators :=
  fun i => (2 : ℂ)⁻¹ • (complexMixedCoefficients A.negative B.positive i+
    (complexMixedCoefficients A.positive B.negative i).adjoint)

def fieldTwoTimeKernel (A B : TransferPair) (shift : Fin 3 → ℝ) (time age : ℝ) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  let J := realReaderCoefficients A shift
  let backward := shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) shift
  Complex.I • (orderedWord backward J (-shift) age time-
    orderedWord J (complexFrequencyCoefficients B.positive) shift time age)

def fieldMixedContact (A B : TransferPair) (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  contactWord (realMixedCoefficients A B) time

def packetNormalization (momentum : Fin 3 → ℝ) : ℂ :=
  ((‖CanonicalPacket.rawPacket momentum 0 1 (by norm_num)‖⁻¹ : ℝ) : ℂ)^2

def fieldMother (momentum : Fin 3 → ℝ) (A B : TransferPair) (shift : Fin 3 → ℝ)
    (time age : ℝ) : YangMills.FullPairing.Mother :=
  CanonicalPacket.mother momentum
    (packetNormalization momentum • fieldTwoTimeKernel A B shift time age)

theorem fieldMother_read (momentum : Fin 3 → ℝ) (A B : TransferPair) (shift : Fin 3 → ℝ)
    (time age : ℝ) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Stage9DEF.Compatibility.responseMatrix (fieldMother momentum A B shift time age)) =
      packetNormalization momentum *
        inner ℂ (CanonicalPacket.packet momentum)
          (fieldTwoTimeKernel A B shift time age (CanonicalPacket.packet momentum)) := by
  rw [fieldMother, CanonicalPacket.mother_read]
  simp only [smul_apply, inner_smul_right]

theorem fieldMother_fullCAR (momentum : Fin 3 → ℝ) (A B : TransferPair) (shift : Fin 3 → ℝ)
    (time age : ℝ) :
    let J := realReaderCoefficients A shift
    let backward := shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients B.negative)) shift
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Stage9DEF.Compatibility.responseMatrix (fieldMother momentum A B shift time age)) =
      packetNormalization momentum * Complex.I *
        ((∑ i : Fin 4, ∑ j : Fin 4, orderedCARRead momentum backward J (-shift) age time i j)-
          ∑ i : Fin 4, ∑ j : Fin 4,
            orderedCARRead momentum J (complexFrequencyCoefficients B.positive) shift time age i j) := by
  dsimp only
  rw [fieldMother_read]
  simp only [fieldTwoTimeKernel, smul_apply, sub_apply, inner_smul_right, inner_sub_right,
    orderedWord_fullCAR]
  ring

/-- The direct contact is outside the Duhamel age integral. -/
def fieldContactMother (momentum : Fin 3 → ℝ) (A B : TransferPair) (time : ℝ) :
    YangMills.FullPairing.Mother :=
  CanonicalPacket.mother momentum
    (packetNormalization momentum • fieldMixedContact A B time)

theorem fieldContactMother_read (momentum : Fin 3 → ℝ) (A B : TransferPair) (time : ℝ) :
    Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
      (Stage9DEF.Compatibility.responseMatrix (fieldContactMother momentum A B time)) =
      packetNormalization momentum *
        inner ℂ (CanonicalPacket.packet momentum)
          (fieldMixedContact A B time (CanonicalPacket.packet momentum)) := by
  rw [fieldContactMother, CanonicalPacket.mother_read]
  simp only [smul_apply, inner_smul_right]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalCoframe
