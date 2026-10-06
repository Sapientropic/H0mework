import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrincipalMatrixJets
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPrincipalBudget
open PreparationVacuumCentralBudget PreparationVacuumClockBudget PreparationVacuumEngineBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumClockJacobian PreparationVacuumEngineSmooth
open PreparationVacuumMoyalSymmetry PreparationVacuumMoyalBudget PreparationVacuumReciprocalBudget
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates PreparationPhaseScalar PreparationMeasure
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice SourceQuantumNativeDimensions GaussLiveMomentum
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential PreparationPhaseGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology Matrix RealInnerProductSpace

private def series (B : ArrayBound) : PowerSeries ℝ := PowerSeries.mk (fun n => B n/(n.factorial : ℝ))

private theorem series_product (B D : ArrayBound) : series (productArray B D)=series B*series D := by
  ext n
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [series,PowerSeries.coeff_mk,productArray,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have fact : (n.choose k : ℝ)*(k.factorial : ℝ)*((n-k).factorial : ℝ)=(n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have nz (r : ℕ) : (r.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero r
  have ratio : (n.choose k : ℝ)/(n.factorial : ℝ)=1/((k.factorial : ℝ)*((n-k).factorial : ℝ)) := by
    apply (div_eq_div_iff (nz n) (mul_ne_zero (nz k) (nz (n-k)))).mpr
    simpa only [one_mul,mul_assoc] using fact
  calc
    _ = ((n.choose k : ℝ)/(n.factorial : ℝ))*(B k*D (n-k)) := by ring
    _ = (1/((k.factorial : ℝ)*((n-k).factorial : ℝ)))*(B k*D (n-k)) := by rw [ratio]
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring

private theorem series_injective : Function.Injective series := by
  intro B D same
  funext n
  have coeff := congrArg (PowerSeries.coeff n) same
  simp only [series,PowerSeries.coeff_mk] at coeff
  exact (div_left_inj' (show (n.factorial : ℝ)≠0 by exact_mod_cast Nat.factorial_ne_zero n)).mp coeff

theorem productArray_assoc (A B D : ArrayBound) :
    productArray (productArray A B) D=productArray A (productArray B D) := by
  apply series_injective
  simp only [series_product,mul_assoc]

theorem productArray_comm (B D : ArrayBound) : productArray B D=productArray D B := by
  apply series_injective
  simp only [series_product,mul_comm]

theorem productArray_one (B : ArrayBound) : productArray (constantArray 1) B=B := by
  funext n
  simp [productArray,constantArray]

theorem powerArray_two (B : ArrayBound) : powerArray B 2=productArray B B := by
  change productArray (productArray (constantArray 1) B) B=_
  rw [productArray_one]

theorem productArray_scale_left (c : ℝ) (B D : ArrayBound) :
    productArray (fun n => c*B n) D=(fun n => c*productArray B D n) := by
  funext n
  unfold productArray
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem coordinate_expansion {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : V ≃ₗ[ℝ] (Fin n → ℝ)) (v : V) : v=∑ a,e v a • e.symm (Pi.single a 1) := by
  apply e.injective
  simp only [map_sum,map_smul,LinearEquiv.apply_symm_apply]
  ext j
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

private theorem functional_coordinates {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : V ≃ₗ[ℝ] (Fin n → ℝ)) (f : V →ₗ[ℝ] ℝ) (v : V) :
    f v=∑ a,e v a*f (e.symm (Pi.single a 1)) := by
  conv_lhs => rw [coordinate_expansion e v]
  simp only [map_sum,map_smul,smul_eq_mul]

def scalarDual (a : Fin 70) : Scalar := scalarRealify.symm (Pi.single a 1)

private theorem scalar_pair (phi psi : Scalar) :
    inner ℝ phi psi=∑ a : Fin 70,scalarRealify phi a*scalarRealify psi a := by
  rw [scalar_inner_lex,Fin.sum_univ_add (a:=35) (b:=35)]
  simp only [Finset.sum_add_distrib]
  congr 1

private theorem scalarDual_pair (a : Fin 70) (v : Scalar) : inner ℝ (scalarDual a) v=scalarRealify v a := by
  rw [scalar_pair]
  simp [scalarDual,Pi.single_apply]

def rawGramInverse : Matrix (Fin 12) (Fin 12) ℝ := fun a b =>
  if a=b then (if a=11 then 1 else if a=6 ∨ a=7 then 2/3 else 1/2)
  else if (a=6 ∧ b=7) ∨ (a=7 ∧ b=6) then -1/3 else 0

def lieDual (a : Fin 12) : NativeLie := rawCoordinates.symm (fun b => rawGramInverse b a)

theorem lieDual_pair (a : Fin 12) (v : NativeLie) : inner ℝ (lieDual a) v=rawCoordinates v a := by
  conv_lhs => rhs; rw [←rawCoordinates.symm_apply_apply v]
  rw [lieDual,original_raw_inner]
  fin_cases a
  all_goals norm_num [rawGramInverse,Fin.ext_iff]
  all_goals ring_nf
  all_goals rfl

theorem rawGramInverse_bound : RectBound rawGramInverse 2 := by
  have point (i j : Fin 12) : |rawGramInverse i j| ≤
      (if j=i then (1 : ℝ) else 0)+(if j=(if i=6 then 7 else 6) then (1 : ℝ) else 0) := by
    unfold rawGramInverse
    split_ifs <;> norm_num [Fin.ext_iff] at * <;> omega
  have row (i : Fin 12) : (∑ j,|rawGramInverse i j|) ≤ 2 := by
    calc
      _ ≤ ∑ j : Fin 12,((if j=i then (1 : ℝ) else 0)+
          (if j=(if i=6 then 7 else 6) then (1 : ℝ) else 0)) := Finset.sum_le_sum (fun j _ => point i j)
      _ = 2 := by rw [Finset.sum_add_distrib]; norm_num
  refine ⟨row,?_⟩
  intro j
  have symmetry (i j : Fin 12) : rawGramInverse i j=rawGramInverse j i := by
    by_cases h : i=j
    · subst j; rfl
    · simp [rawGramInverse,h,Ne.symm h,and_comm,or_comm]
  simpa only [symmetry] using row j

def scalarFunctional (x : Phase) : Scalar →ₗ[ℝ] ℝ :=
  (ambientMomentum (fullCoordinates.symm x.1) (nativeCovector x.2)).comp (LinearMap.inl ℝ _ _)
def gaugeInsertion (i : Fin 3) : NativeLie →ₗ[ℝ] SourceQuantumConfigurationHilbert.Gauge :=
  gaugeCoordinates.symm.toLinearMap.comp (LinearMap.single ℝ (fun _ : Fin 3 => NativeLie) i)
def gaugeFunctional (x : Phase) (i : Fin 3) : NativeLie →ₗ[ℝ] ℝ :=
  ((ambientMomentum (fullCoordinates.symm x.1) (nativeCovector x.2)).comp
    (LinearMap.inr ℝ _ _)).comp (gaugeInsertion i)

theorem gaugeInsertion_raw (i : Fin 3) (a : Fin 12) :
    gaugeInsertion i (rawCoordinates.symm (Pi.single a 1))=gaugeRaw.symm (Pi.single (combinedRow i a) 1) := by
  have same (j : Fin 3) (b : Fin 12) : combinedRow j b=combinedRow i a ↔ j=i ∧ b=a := by
    constructor
    · intro h
      exact ⟨by simpa only [spatial_combined] using congrArg spatialRow h,
        by simpa only [native_combined] using congrArg nativeRow h⟩
    · rintro ⟨rfl,rfl⟩; rfl
  dsimp only [gaugeInsertion,LinearMap.comp_apply,LinearMap.single_apply,gaugeRaw,gaugeBuild]
  apply congrArg gaugeCoordinates.symm
  funext j
  apply rawCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  ext b
  by_cases h : j=i
  · subst j
    simp [Pi.single_apply,same,eq_comm]
  · simp [h,same]

def scalarRiesz (x : Phase) : Scalar := ∑ a : Fin 70,rawScalarMomentum a x • scalarDual a
def gaugeRiesz (x : Phase) (i : Fin 3) : NativeLie :=
  ∑ a : Fin 12,rawGaugeMomentum (combinedRow i a) x • lieDual a

private theorem scalarRiesz_pair (x : Phase) (v : Scalar) :
    inner ℝ (scalarRiesz x) v=scalarFunctional x v := by
  rw [functional_coordinates scalarRealify (scalarFunctional x) v]
  simp only [scalarRiesz,sum_inner,real_inner_smul_left,scalarDual_pair]
  apply Finset.sum_congr rfl
  intro a _
  change rawScalarMomentum a x*scalarRealify v a=scalarRealify v a*rawScalarMomentum a x
  ring

private theorem gaugeRiesz_pair (x : Phase) (i : Fin 3) (v : NativeLie) :
    inner ℝ (gaugeRiesz x i) v=gaugeFunctional x i v := by
  rw [functional_coordinates rawCoordinates (gaugeFunctional x i) v]
  simp only [gaugeRiesz,sum_inner,real_inner_smul_left,lieDual_pair]
  apply Finset.sum_congr rfl
  intro a _
  change rawGaugeMomentum (combinedRow i a) x*rawCoordinates v a=
    rawCoordinates v a*ambientMomentum (fullCoordinates.symm x.1) (nativeCovector x.2)
      (0,gaugeInsertion i (rawCoordinates.symm (Pi.single a 1)))
  rw [gaugeInsertion_raw]
  change rawGaugeMomentum (combinedRow i a) x*rawCoordinates v a=rawCoordinates v a*rawGaugeMomentum (combinedRow i a) x
  ring

theorem actual_scalarGram_raw (x : Phase) :
    scalarNormSquare (fullCoordinates.symm x.1) (nativeCovector x.2)=∑ a : Fin 70,(rawScalarMomentum a x)^2 := by
  have read (a : ScalarIndex) : scalarMomentum (fullCoordinates.symm x.1) (nativeCovector x.2) a=
      inner ℝ (scalarRiesz x) (scalarBasis a) := (scalarRiesz_pair x (scalarBasis a)).symm
  unfold scalarNormSquare
  simp_rw [read,pow_two]
  have parseval := scalarBasis.sum_inner_mul_inner (scalarRiesz x) (scalarRiesz x)
  simp_rw [show ∀ a : ScalarIndex,inner ℝ (scalarBasis a) (scalarRiesz x)=inner ℝ (scalarRiesz x) (scalarBasis a) from fun a => real_inner_comm _ _] at parseval
  rw [parseval,scalar_pair]
  have coordinates : scalarRealify (scalarRiesz x)=fun a => rawScalarMomentum a x := by
    ext a
    simp [scalarRiesz,scalarDual,map_sum,map_smul,Pi.single_apply,Finset.sum_apply]
  simp only [coordinates]

def electricRawMatrix : RectSymbol 3 12 := fun x i a => rawGaugeMomentum (combinedRow i a) x

theorem actual_electricGram_raw (x : Phase) :
    electricGram (fullCoordinates.symm x.1) (nativeCovector x.2)=
      electricRawMatrix x*rawGramInverse*(electricRawMatrix x)ᵀ := by
  ext i j
  have read (k : Fin 3) (a : LieIndex) : electricMomentum (fullCoordinates.symm x.1) (nativeCovector x.2) k a=
      inner ℝ (gaugeRiesz x k) (lieBasis a) := (gaugeRiesz_pair x k (lieBasis a)).symm
  change (∑ a : LieIndex,electricMomentum _ _ i a*electricMomentum _ _ j a)=_
  simp_rw [read]
  have parseval := lieBasis.sum_inner_mul_inner (gaugeRiesz x i) (gaugeRiesz x j)
  simp_rw [show ∀ a : LieIndex,inner ℝ (lieBasis a) (gaugeRiesz x j)=inner ℝ (gaugeRiesz x j) (lieBasis a) from fun a => real_inner_comm _ _] at parseval
  rw [parseval]
  rw [show gaugeRiesz x i=∑ a : Fin 12,rawGaugeMomentum (combinedRow i a) x • lieDual a from rfl,sum_inner]
  simp only [real_inner_smul_left]
  simp_rw [gaugeRiesz,inner_sum,real_inner_smul_right,lieDual_pair]
  simp only [lieDual,LinearEquiv.apply_symm_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [electricRawMatrix]
  ring


private theorem series_constant (c : ℝ) : series (constantArray c)=PowerSeries.C c := by
  ext n
  cases n <;> simp [series,constantArray,PowerSeries.coeff_C]

private theorem series_scale (c : ℝ) (B : ArrayBound) :
    series (fun n => c*B n)=PowerSeries.C c*series B := by
  ext n
  simp [series,PowerSeries.coeff_C_mul]
  ring

theorem finite_matrix_constant {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) (c : ℝ)
    (bound : RectBound M c) (N : ℕ) (x : Phase) : MatrixBound (fun _ => M) N (constantArray c) x := by
  intro m _ w
  cases m with
  | zero => simpa [jet,constantArray] using bound
  | succ m => constructor <;> intro i <;> simp [jet,constantArray,iteratedFDeriv_succ_const]

theorem finite_matrix_scale {a b : ℕ} (c : ℝ) (M : RectSymbol a b) (ms : RectSmooth M)
    (N : ℕ) (B : ArrayBound) (x : Phase) (hx : x∈poleDomain) (bound : MatrixBound M N B x) :
    MatrixBound (fun y => c • M y) N (fun m => |c| *B m) x := by
  intro m hm w
  have read (i : Fin a) (j : Fin b) : jet m (fun y => (c • M y) i j) w x=c*jet m (fun y => M y i j) w x :=
    jet_scale c _ (ms i j) m w x hx
  constructor
  · intro i
    simp_rw [read,abs_mul,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((bound m hm w).1 i) (abs_nonneg _)
  · intro j
    simp_rw [read,abs_mul,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((bound m hm w).2 j) (abs_nonneg _)

theorem finite_diagonal {a : ℕ} (f : Symbol) (N : ℕ) (B : ArrayBound)
    (_bp : ∀ n,0 ≤ B n) (x : Phase) (bound : FiniteBound f N B x) :
    MatrixBound (fun y => Matrix.diagonal (fun _ : Fin a => f y)) N B x := by
  intro m hm w
  have read (i j : Fin a) : jet m (fun y => Matrix.diagonal (fun _ : Fin a => f y) i j) w x=
      if i=j then jet m f w x else 0 := by
    by_cases h : i=j
    · subst j; simp
    · simp only [Matrix.diagonal_apply_ne _ h]
      cases m <;> simp [jet,h]
  constructor <;> intro i <;>
    simpa only [read,apply_ite,abs_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      using bound m hm w

theorem finite_scalar_matrix {a b : ℕ} (f : Symbol) (M : RectSymbol a b)
    (fs : SmoothSymbol f) (ms : RectSmooth M) (N : ℕ) (B D : ArrayBound)
    (bp : ∀ n,0 ≤ B n) (dp : ∀ n,0 ≤ D n) (x : Phase) (hx : x∈poleDomain)
    (fb : FiniteBound f N B x) (mb : MatrixBound M N D x) :
    MatrixBound (fun y => f y • M y) N (productArray B D) x := by
  have ds : RectSmooth (fun y => Matrix.diagonal (fun _ : Fin a => f y)) := by
    intro i j
    by_cases h : i=j
    · subst j; simpa using fs
    · simp only [Matrix.diagonal_apply_ne _ h]; exact contDiffOn_const
  have same : (fun y => Matrix.diagonal (fun _ : Fin a => f y)*M y)=(fun y => f y • M y) := by
    funext y
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [←same]
  exact finite_matrix_product _ M ds ms N B D bp dp x hx (finite_diagonal f N B bp x fb) mb

private theorem embedded_sum {a b : ℕ} (e : Fin a ↪ Fin b) (f : Fin b → ℝ)
    (positive : ∀ i,0 ≤ f i) : (∑ i,f (e i)) ≤ ∑ i,f i := by
  rw [←Finset.sum_image]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => positive i)
  · exact fun i _ j _ h => e.injective h

theorem electricRaw_budget (x : Phase) (hx : x∈poleDomain)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound electricRawMatrix N gaugeMomentumArray x := by
  intro m hm w
  have total := (actual_rawGauge_budget x hx unit N input m hm w).2 0
  constructor
  · intro i
    let e : Fin 12 ↪ Fin 36 := ⟨combinedRow i,fun a b h => by simpa only [native_combined] using congrArg nativeRow h⟩
    exact (embedded_sum e (fun a => |jet m (rawGaugeMomentum a) w x|) (fun a => abs_nonneg _)).trans total
  · intro a
    let e : Fin 3 ↪ Fin 36 := ⟨fun i => combinedRow i a,fun i j h => by simpa only [spatial_combined] using congrArg spatialRow h⟩
    exact (embedded_sum e (fun a => |jet m (rawGaugeMomentum a) w x|) (fun a => abs_nonneg _)).trans total

def kMatrix : RectSymbol 6 6 := fun x i j => PreparationVacuumCoframeBudget.sourceK i j x
def lMatrix : RectSymbol 3 3 := fun x i j => PreparationVacuumCoframeBudget.sourceLInverse i j x

def kArray (m : ℕ) : ℝ := PreparationVacuumCoframeBudget.K0Array m
def lArray (m : ℕ) : ℝ := PreparationVacuumCoframeBudget.LInverseArray m
def vArray (m : ℕ) : ℝ := PreparationVacuumCoframeBudget.volumeArray m
def viArray (m : ℕ) : ℝ := PreparationVacuumCoframeBudget.inverseVolumeArray m

def aArray (m : ℕ) : ℝ := productArray (productArray pqArray kArray) pqArray m+
  productArray (fun n => (1/2 : ℝ)*viArray n) (powerArray scalarMomentumArray 2) m

def electricArray (m : ℕ) : ℝ := (1/2 : ℝ)*2*powerArray gaugeMomentumArray 2 m
def sArray : ArrayBound := productArray (productArray vArray (powerArray lArray 2)) electricArray
def tArray (m : ℕ) : ℝ := 3*sArray m
def qArray (m : ℕ) : ℝ := tArray m+sArray m

theorem kMatrix_smooth : RectSmooth kMatrix := by
  intro i j x hx
  exact (((GaussCoframeKinetic.coefficient_smooth i j ⟨_,hx.1.1⟩).comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).div_const _).contDiffWithinAt

theorem lMatrix_smooth : RectSmooth lMatrix := by
  intro i j x hx
  exact ((triadInverse_smooth i j ⟨_,hx.1.1⟩).comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem volume_smooth_source : SmoothSymbol PreparationVacuumCoframeBudget.sourceVolume := by
  intro x _
  exact (volume_smooth.contDiffAt.comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).contDiffWithinAt

theorem inverseVolume_smooth_source : SmoothSymbol PreparationVacuumCoframeBudget.sourceVolumeInverse := by
  intro x hx
  exact ((volume_smooth.contDiffAt.comp x
    (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst)).inv (volume_pos ⟨_,hx.1.1⟩).ne').contDiffWithinAt

theorem actual_A_raw (x : Phase) : actualA x=
    (((momentumColumn pqEmbedding x)ᵀ*kMatrix x)*momentumColumn pqEmbedding x) 0 0-
      (1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolumeInverse x*
        ((rawScalarColumn x)ᵀ*rawScalarColumn x) 0 0 := by
  have coframe (i : Fin 6) : coframeMomentum (nativeCovector x.2) i=x.2 (pqEmbedding i) :=
    PreparationPhaseScalar.native_coframe_momentum (WithLp.ofLp x.2) i
  unfold actualA A nativePhase coframeQuadratic
  rw [actual_scalarGram_raw]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  simp_rw [coframe]
  unfold kMatrix PreparationVacuumCoframeBudget.sourceK momentumColumn rawScalarColumn
    PreparationVacuumCoframeBudget.sourceVolumeInverse
  rw [Finset.sum_div]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [pow_two]
    ring

theorem actual_S_raw (x : Phase) : actualS x=
    ((1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolume x) •
      (((lMatrix x)ᵀ*(electricRawMatrix x*rawGramInverse*(electricRawMatrix x)ᵀ))*lMatrix x) := by
  have gram := actual_electricGram_raw x
  ext k l
  change sourceSigma*volume (fullCoordinates.symm x.1)*
    (∑ i : Fin 3,∑ j : Fin 3,triadInverse (fullCoordinates.symm x.1).1 i k*
      electricGram (fullCoordinates.symm x.1) (nativeCovector x.2) i j*
        triadInverse (fullCoordinates.symm x.1).1 j l)=_
  rw [PreparationPhaseBounds.actual_sourceSigma_half]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [show electricGram (fullCoordinates.symm x.1) (nativeCovector x.2) i j=
      (electricRawMatrix x*rawGramInverse*(electricRawMatrix x)ᵀ) i j from congrArg (fun M => M i j) gram]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rfl


private theorem scalarSquare_budget (x : Phase) (hx : x∈poleDomain)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    FiniteBound (fun y => ((rawScalarColumn y)ᵀ*rawScalarColumn y) 0 0) N
      (powerArray scalarMomentumArray 2) x := by
  have positive : ∀ n,0 ≤ scalarMomentumArray n :=
    productArray_nonnegative _ _ scalarFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have smooth : RectSmooth rawScalarColumn := fun i _ => rawScalarMomentum_smooth i
  have bound := actual_rawScalar_budget x hx unit N input
  have result := finite_matrix_product (fun y => (rawScalarColumn y)ᵀ) rawScalarColumn
    (fun i j => smooth j i) smooth N scalarMomentumArray scalarMomentumArray positive positive x hx
    (finite_matrix_transpose _ N _ x bound) bound
  rw [powerArray_two]
  intro m hm w
  exact rect_entry (result m hm w) 0 0

theorem actual_A_budget (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    FiniteBound actualA N aArray x := by
  have kp : ∀ n,0 ≤ kArray n := fun n => Nat.cast_nonneg _
  have pp : ∀ n,0 ≤ pqArray n := affineArray_nonnegative 12 1 (by norm_num) (by norm_num)
  have kb : MatrixBound kMatrix N kArray x := fun m _ w =>
    ⟨PreparationVacuumCoframeBudget.actual_K0_row_budget m w x box,
     PreparationVacuumCoframeBudget.actual_K0_column_budget m w x box⟩
  have pb : MatrixBound (momentumColumn pqEmbedding) N pqArray x := by
    simpa only [pqArray,Nat.cast_ofNat,show (2 : ℝ)*6=12 by norm_num] using momentumColumn_budget pqEmbedding x unit N
  have ps := momentumColumn_smooth pqEmbedding
  have first := finite_matrix_product (fun y => (momentumColumn pqEmbedding y)ᵀ) kMatrix
    (fun i j => ps j i) kMatrix_smooth N pqArray kArray pp kp x hx (finite_matrix_transpose _ N _ x pb) kb
  have second := finite_matrix_product (fun y => (momentumColumn pqEmbedding y)ᵀ*kMatrix y)
    (momentumColumn pqEmbedding) (matrix_product_smooth _ _ (fun i j => ps j i) kMatrix_smooth) ps N
    (productArray pqArray kArray) pqArray (productArray_nonnegative _ _ pp kp) pp x hx first pb
  have cf : FiniteBound (fun y => (((momentumColumn pqEmbedding y)ᵀ*kMatrix y)*momentumColumn pqEmbedding y) 0 0)
      N (productArray (productArray pqArray kArray) pqArray) x := fun m hm w => rect_entry (second m hm w) 0 0
  have css : SmoothSymbol (fun y => (((momentumColumn pqEmbedding y)ᵀ*kMatrix y)*momentumColumn pqEmbedding y) 0 0) :=
    matrix_product_smooth _ _ (matrix_product_smooth _ _ (fun i j => ps j i) kMatrix_smooth) ps 0 0
  have ss : RectSmooth rawScalarColumn := fun i _ => rawScalarMomentum_smooth i
  have sqs := matrix_product_smooth (fun y => (rawScalarColumn y)ᵀ) rawScalarColumn (fun i j => ss j i) ss 0 0
  have vi : FiniteBound PreparationVacuumCoframeBudget.sourceVolumeInverse N viArray x :=
    fun m _ w => PreparationVacuumCoframeBudget.actual_inverseVolume_budget m w x box
  have half := finite_scale (1/2 : ℝ) _ inverseVolume_smooth_source _ N x hx vi
  have scalar := finite_product (fun y => (1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolumeInverse y)
    (fun y => ((rawScalarColumn y)ᵀ*rawScalarColumn y) 0 0) (contDiffOn_const.mul inverseVolume_smooth_source) sqs
    (fun n => (1/2 : ℝ)*viArray n) (powerArray scalarMomentumArray 2) (fun n => mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    N x hx (by simpa using half) (scalarSquare_budget x hx unit N input)
  have result := finite_sub _ _ css ((contDiffOn_const.mul inverseVolume_smooth_source).mul sqs) _ _ N x hx cf scalar
  have identity : actualA=(fun y => (((momentumColumn pqEmbedding y)ᵀ*kMatrix y)*momentumColumn pqEmbedding y) 0 0-
      (1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolumeInverse y*((rawScalarColumn y)ᵀ*rawScalarColumn y) 0 0) :=
    funext actual_A_raw
  rw [identity]
  exact result

theorem actual_S_budget (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound actualS N sArray x := by
  have lp : ∀ n,0 ≤ lArray n := fun n => Nat.cast_nonneg _
  have gp : ∀ n,0 ≤ gaugeMomentumArray n :=
    productArray_nonnegative _ _ gaugeFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have es : RectSmooth electricRawMatrix := fun i a => rawGaugeMomentum_smooth _
  have eb := electricRaw_budget x hx unit N input
  have gram := finite_matrix_product electricRawMatrix (fun _ => rawGramInverse) es (fun _ _ => contDiffOn_const)
    N gaugeMomentumArray (constantArray 2) gp (constantArray_nonnegative 2 (by norm_num)) x hx eb
    (finite_matrix_constant rawGramInverse 2 rawGramInverse_bound N x)
  have eg := finite_matrix_product (fun y => electricRawMatrix y*rawGramInverse)
    (fun y => (electricRawMatrix y)ᵀ) (matrix_product_smooth _ _ es (fun _ _ => contDiffOn_const))
    (fun i j => es j i) N (productArray gaugeMomentumArray (constantArray 2)) gaugeMomentumArray
    (productArray_nonnegative _ _ gp (constantArray_nonnegative 2 (by norm_num))) gp x hx gram
    (finite_matrix_transpose _ N _ x eb)
  let G : RectSymbol 3 3 := fun y => electricRawMatrix y*rawGramInverse*(electricRawMatrix y)ᵀ
  let GB := productArray (productArray gaugeMomentumArray (constantArray 2)) gaugeMomentumArray
  have gs : RectSmooth G := matrix_product_smooth _ _ (matrix_product_smooth _ _ es (fun _ _ => contDiffOn_const)) (fun i j => es j i)
  have ggp : ∀ n,0 ≤ GB n := productArray_nonnegative _ _
    (productArray_nonnegative _ _ gp (constantArray_nonnegative 2 (by norm_num))) gp
  have lb : MatrixBound lMatrix N lArray x := fun m _ w =>
    ⟨PreparationVacuumCoframeBudget.actual_LInverse_row_budget m w x box,
     PreparationVacuumCoframeBudget.actual_LInverse_column_budget m w x box⟩
  have first := finite_matrix_product (fun y => (lMatrix y)ᵀ) G (fun i j => lMatrix_smooth j i) gs
    N lArray GB lp ggp x hx (finite_matrix_transpose _ N _ x lb) eg
  have second := finite_matrix_product (fun y => (lMatrix y)ᵀ*G y) lMatrix
    (matrix_product_smooth _ _ (fun i j => lMatrix_smooth j i) gs) lMatrix_smooth
    N (productArray lArray GB) lArray (productArray_nonnegative _ _ lp ggp) lp x hx first lb
  have vb : FiniteBound PreparationVacuumCoframeBudget.sourceVolume N vArray x :=
    fun m _ w => PreparationVacuumCoframeBudget.actual_volume_budget m w x box
  have half := finite_scale (1/2 : ℝ) _ volume_smooth_source _ N x hx vb
  have result := finite_scalar_matrix (fun y => (1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolume y)
    (fun y => ((lMatrix y)ᵀ*G y)*lMatrix y) (contDiffOn_const.mul volume_smooth_source)
    (matrix_product_smooth _ _ (matrix_product_smooth _ _ (fun i j => lMatrix_smooth j i) gs) lMatrix_smooth)
    N (fun n => (1/2 : ℝ)*vArray n) (productArray (productArray lArray GB) lArray)
    (fun n => mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (productArray_nonnegative _ _ (productArray_nonnegative _ _ lp ggp) lp) x hx (by simpa using half) second
  have arrays : productArray (fun n => (1/2 : ℝ)*vArray n) (productArray (productArray lArray GB) lArray)=sArray := by
    have ec : electricArray=powerArray gaugeMomentumArray 2 := by
      funext n
      unfold electricArray
      ring
    apply series_injective
    rw [sArray,ec]
    simp only [powerArray_two,GB,series_product,series_scale,series_constant]
    have cancel : (PowerSeries.C (1/2 : ℝ) : PowerSeries ℝ)*PowerSeries.C 2=1 := by
      rw [←map_mul]
      norm_num
    calc
      _ = (PowerSeries.C (1/2 : ℝ)*PowerSeries.C 2)*
          (series vArray*series lArray^2*series gaugeMomentumArray^2) := by ring
      _ = _ := by rw [cancel]; ring
  rw [arrays] at result
  have identity : actualS=(fun y => ((1/2 : ℝ)*PreparationVacuumCoframeBudget.sourceVolume y) •
      (((lMatrix y)ᵀ*G y)*lMatrix y)) := funext actual_S_raw
  rw [identity]
  exact result

theorem principal_arrays_nonnegative : (∀ n,0 ≤ aArray n) ∧ (∀ n,0 ≤ tArray n) ∧ (∀ n,0 ≤ qArray n) := by
  have pp := affineArray_nonnegative 12 1 (by norm_num) (by norm_num)
  have scalar := productArray_nonnegative _ _ scalarFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have gauge := productArray_nonnegative _ _ gaugeFactor_nonnegative (affineArray_nonnegative 188 1 (by norm_num) (by norm_num))
  have sp : ∀ n,0 ≤ sArray n := productArray_nonnegative _ _
    (productArray_nonnegative _ _ (fun n => Nat.cast_nonneg _) (powerArray_nonnegative _ (fun n => Nat.cast_nonneg _) 2))
    (fun n => mul_nonneg (by norm_num) (powerArray_nonnegative _ gauge 2 n))
  refine ⟨?_,?_,?_⟩
  · intro n
    exact add_nonneg (productArray_nonnegative _ _ (productArray_nonnegative _ _ pp (fun n => Nat.cast_nonneg _)) pp n)
      (productArray_nonnegative _ _ (fun n => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (powerArray_nonnegative _ scalar 2) n)
  · intro n; exact mul_nonneg (by norm_num) (sp n)
  · intro n; exact add_nonneg (mul_nonneg (by norm_num) (sp n)) (sp n)

theorem actual_T_budget (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    FiniteBound actualT N tArray x := by
  have sb := actual_S_budget x hx box unit N input
  have result := finite_sum Finset.univ (fun i y => actualS y i i)
    (fun i _ y hy => (actualS_smooth y hy.1.1 i i).contDiffWithinAt) (fun _ => sArray) N x hx
    (fun i _ m hm w => rect_entry (sb m hm w) i i)
  rw [show actualT=(fun y => ∑ i : Fin 3,actualS y i i) from rfl]
  intro m hm w
  simpa only [tArray,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using result m hm w

theorem actual_Q_budget (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) :
    MatrixBound sourceM N qArray x := by
  have tb := actual_T_budget x hx box unit N input
  have sb := actual_S_budget x hx box unit N input
  have diagonal := finite_diagonal (a:=3) actualT N tArray principal_arrays_nonnegative.2.1 x tb
  intro m hm w
  have read (i j : Fin 3) : jet m (fun y => sourceM y i j) w x=
      jet m (fun y => Matrix.diagonal (fun _ : Fin 3 => actualT y) i j) w x-
        jet m (fun y => actualS y i j) w x := by
    have original : (fun y => sourceM y i j)=(fun y =>
        Matrix.diagonal (fun _ : Fin 3 => actualT y) i j-actualS y i j) := by
      funext y
      simp [sourceM,Matrix.smul_apply,Matrix.one_apply,Matrix.diagonal_apply,mul_ite]
    rw [original]
    unfold jet
    change iteratedFDeriv ℝ m ((fun y => Matrix.diagonal (fun _ : Fin 3 => actualT y) i j)-(fun y => actualS y i j)) x _=_
    rw [iteratedFDeriv_sub_apply]
    · rfl
    · have smooth : ContDiffAt ℝ ∞ (fun y => Matrix.diagonal (fun _ : Fin 3 => actualT y) i j) x := by
        by_cases h : i=j
        · subst j; simpa using actualT_smooth x hx.1.1
        · simp only [Matrix.diagonal_apply_ne _ h]; exact contDiffAt_const
      exact smooth.of_le (by exact_mod_cast (ENat.natCast_lt_top m).le)
    · exact (actualS_smooth x hx.1.1 i j).of_le (by exact_mod_cast (ENat.natCast_lt_top m).le)
  constructor
  · intro i
    simp_rw [read]
    calc
      _ ≤ ∑ j,(|jet m (fun y => Matrix.diagonal (fun _ : Fin 3 => actualT y) i j) w x|+|jet m (fun y => actualS y i j) w x|) :=
        Finset.sum_le_sum (fun j _ => abs_sub _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add ((diagonal m hm w).1 i) ((sb m hm w).1 i)
  · intro j
    simp_rw [read]
    calc
      _ ≤ ∑ i,(|jet m (fun y => Matrix.diagonal (fun _ : Fin 3 => actualT y) i j) w x|+|jet m (fun y => actualS y i j) w x|) :=
        Finset.sum_le_sum (fun i _ => abs_sub _ _)
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add ((diagonal m hm w).2 j) ((sb m hm w).2 j)

def generatedClockInputs (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) : ATInputs x N where
  A := aArray
  T := tArray
  A_nonnegative := principal_arrays_nonnegative.1
  T_nonnegative := principal_arrays_nonnegative.2.1
  A_bound := actual_A_budget x hx box unit N input
  T_bound := actual_T_budget x hx box unit N input

def generatedQInputs (x : Phase) (hx : x∈poleDomain)
    (box : PreparationVacuumCoframeBudget.sourceBox x)
    (unit : (∑ i : Fin 100,(x.2 i)^2)=1) (N : ℕ) (input : CoefficientInputs x N) : QInputs x N where
  Q := qArray
  nonnegative := principal_arrays_nonnegative.2.2
  bounds := actual_Q_budget x hx box unit N input

end LowEnergy.PreparationVacuumPrincipalBudget
