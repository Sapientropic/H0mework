import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedMixedReturn

/-! Source scalar/gauge grade components on the original weighted completion.
The raw independent-momentum current and its adjoint observation are distinct;
real polarization of a time-dependent word keeps the whole reversed sharp word. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedMixedSource
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier CanonicalGradedCurrent CanonicalGradedMixed
open GaussYukawaCoefficient GaussYukawaGrade
attribute [local irreducible] GaussYukawaGrade.grade
open GaussUnitaryHistory (Index)
open scoped Topology InnerProductSpace BigOperators ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℚ Operator := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Operator := NormedAlgebra.restrictScalars ℝ ℂ _
local instance labelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

/-- All original 70 real scalar directions are covered by this actual Scalar argument. -/
def scalarHamiltonian (phi : Scalar) : Operator := boundedMatrix (fullMatrix phi)

theorem scalarHamiltonian_core (phi : Scalar) (f : QuantumTest) :
    scalarHamiltonian phi (embed f) = embed (localMultiplier (fun _ => sourceMap phi)
      (fun _ => contDiffAt_const) f) := boundedMatrix_core (fullMatrix phi) f

theorem scalarHamiltonian_raises (phi : Scalar) : Homogeneous (scalarHamiltonian phi) 1 := by
  simp only [Homogeneous, Int.cast_one, one_smul]
  apply GaussYukawaGrade.core_ext
  intro f
  change GaussYukawaGrade.grade (scalarHamiltonian phi (embed f)) = scalarHamiltonian phi (GaussYukawaGrade.grade (embed f))+scalarHamiltonian phi (embed f)
  rw [ scalarHamiltonian_core, grade_core, grade_core, scalarHamiltonian_core]
  rw [← embed.map_add]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact fiber_source_grade phi (f z)

theorem grade_selfAdjoint : IsSelfAdjoint GaussYukawaGrade.grade := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (GaussYukawaGrade.grade x) y = inner ℂ x (GaussYukawaGrade.grade y)
  simp only [GaussYukawaGrade.grade, sum_apply, smul_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    map_natCast]
  exact Finset.sum_congr rfl (fun g _ => congrArg (fun z : ℂ => (g.2.val : ℂ)*z)
    (NativeHistoryGrade.projection_symmetric g x y))

theorem homogeneous_adjoint (A : Operator) (g : ℤ) (generated : Homogeneous A g) :
    Homogeneous A.adjoint (-g) := by
  unfold Homogeneous at generated ⊢
  have dual := congrArg (star : Operator → Operator) generated
  rw [star_mul GaussYukawaGrade.grade A,
    star_add (A*GaussYukawaGrade.grade) ((g : ℂ) • A),
    star_mul A GaussYukawaGrade.grade, star_smul (g : ℂ) A, grade_selfAdjoint.star_eq] at dual
  have scalar : star (g : ℂ)=(g : ℂ) := by simp
  rw [scalar] at dual
  simp only [ContinuousLinearMap.star_eq_adjoint] at dual
  have negScale : ((-g : ℤ) : ℂ) • A.adjoint = -((g : ℂ) • A.adjoint) := by
    apply ContinuousLinearMap.ext
    intro v
    change ((-g : ℤ) : ℂ) • A.adjoint v = -((g : ℂ) • A.adjoint v)
    rw [Int.cast_neg]
    exact neg_smul (g : ℂ) (A.adjoint v)
  calc
    _ = A.adjoint*GaussYukawaGrade.grade-(g : ℂ) • A.adjoint := (eq_sub_iff_add_eq).mpr dual.symm
    _ = A.adjoint*GaussYukawaGrade.grade+(-((g : ℂ) • A.adjoint)) := sub_eq_add_neg _ _
    _ = _ := congrArg (fun T : Operator => A.adjoint*GaussYukawaGrade.grade+T) negScale.symm

theorem homogeneous_smul (A : Operator) (g : ℤ) (generated : Homogeneous A g) (c : ℂ) :
    Homogeneous (c • A) g := by
  unfold Homogeneous at generated ⊢
  change GaussYukawaGrade.grade*(c • A)=(c • A)*GaussYukawaGrade.grade+(g : ℂ) • (c • A)
  simp only [mul_smul_comm, smul_mul_assoc, generated, smul_add]
  rw [smul_comm c (g : ℂ)]

/-- Raw source momentum force. No adjoint is inserted into the source Hamiltonian. -/
def rawScalar (phi : Scalar) : Operator := -(scalarHamiltonian phi)

def dualScalar (phi : Scalar) : Operator := (rawScalar phi).adjoint

theorem rawScalar_raises (phi : Scalar) : Homogeneous (rawScalar phi) 1 := by
  have h := scalarHamiltonian_raises phi
  simp only [Homogeneous, Int.cast_one, one_smul] at h ⊢
  rw [rawScalar, mul_neg GaussYukawaGrade.grade (scalarHamiltonian phi),
    neg_mul (scalarHamiltonian phi) GaussYukawaGrade.grade, h]
  abel

theorem dualScalar_lowers (phi : Scalar) : Homogeneous (dualScalar phi) (-1) :=
  homogeneous_adjoint (rawScalar phi) 1 (rawScalar_raises phi)

theorem gauge_zero (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    Homogeneous (gaugeReader z mu a) 0 := by
  simp only [Homogeneous, Int.cast_zero]
  rw [zero_smul ℂ (gaugeReader z mu a), add_zero]
  simp only [GaussYukawaGrade.grade, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  exact Finset.sum_congr rfl (fun g _ => congrArg (fun T : Operator => (g.2.val : ℂ) • T)
    (boundedMatrix_blocks (gaugeMatrix z mu a) (gaugeMatrix_preserves z mu a) g).eq)

/-- This is a Hilbert real-part observation of the source current, not its raw force. -/
def realPartScalar (phi : Scalar) : Operator := (1/2 : ℂ) • (rawScalar phi+dualScalar phi)

theorem realPartScalar_pair (phi : Scalar) (x y : GaussCoreHilbert.H) :
    inner ℂ x (realPartScalar phi y) = (1/2 : ℂ)*
      (inner ℂ x (rawScalar phi y)+(starRingEnd ℂ) (inner ℂ y (rawScalar phi x))) := by
  rw [realPartScalar, smul_apply, add_apply, inner_smul_right, inner_add_right,
    dualScalar, ContinuousLinearMap.adjoint_inner_right]
  congr 2
  exact (inner_conj_symm _ _).symm

theorem realPartScalar_diagonal (phi : Scalar) (x : GaussCoreHilbert.H) :
    inner ℂ x (realPartScalar phi x) = ((inner ℂ x (rawScalar phi x)).re : ℂ) := by
  rw [realPartScalar_pair, Complex.re_eq_add_conj]
  ring

section Primitive
open DiracExteriorMatterAction StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage10.CanonicalMatter YangMills.FullPairing ProofFreeRicherAnholonomicSource

theorem canonical_scalar_density (phi : Scalar) :
    phaseInverse.comp ((lapse : ℂ) • diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi)) =
      -LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi) := by
  apply LinearMap.ext
  intro v
  simp only [phaseInverse, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    LowEnergy.FullQuantum.yukawaHamiltonian, map_smul]
  exact smul_neg _ _

def scalarCoordinate (a : SourceScalarFock.ScalarIndex) : Scalar :=
  scalarCoordinateEquiv (SourceScalarFock.scalarDirection a)

theorem scalarCoordinate_matrix (a : SourceScalarFock.ScalarIndex) :
    fullMatrix (scalarCoordinate a) = SourceRealScalarFock.sourceMatrix a := by
  change SourceRealScalarFock.branches (LowEnergy.Quantum.operatorMatrix
    (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm (scalarCoordinate a)))) = _
  rw [scalarCoordinate, scalarCoordinateEquiv.symm_apply_apply]
  rfl

theorem original_real_CAR (a : SourceScalarFock.ScalarIndex) (point : BasePoint)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) (psi : DiracExteriorMatterCarrier) :
    (∑ i : SourceRealScalarFock.BranchIndex, ∑ j : SourceRealScalarFock.BranchIndex,
      SourceRealScalarFock.normalizedMomentum
        (LowEnergy.Quantum.dualCoordinates (LowEnergy.FullQuantum.normalizedMomentum actual point chi)) i *
      fullMatrix (scalarCoordinate a) i j * SourceRealScalarFock.normalizedPrimal (LowEnergy.Quantum.coordinates psi) j) =
      -((LowEnergy.Exchange.yukawaSource (actual.coframe point) psi chi (scalarCoordinate a) : ℝ) : ℂ) := by
  rw [scalarCoordinate_matrix]
  exact SourceRealScalarFock.original_real_action_branches a point chi psi

end Primitive


def bandGrade : Fin 3 → ℤ := ![-1, 0, 1]

def sourceBand (phi : Scalar) (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) : Fin 3 → Operator :=
  ![(1/2 : ℂ) • dualScalar phi, gaugeReader z mu a, (1/2 : ℂ) • rawScalar phi]

theorem sourceBand_homogeneous (phi : Scalar) (z : SourceCoordinateSlice) (mu : Component)
    (a : NativeLie) (i : Fin 3) : Homogeneous (sourceBand phi z mu a i) (bandGrade i) := by
  fin_cases i
  · exact homogeneous_smul _ _ (dualScalar_lowers phi) _
  · exact gauge_zero z mu a
  · exact homogeneous_smul _ _ (rawScalar_raises phi) _

theorem bandGrade_lower (i : Fin 3) : -1 ≤ bandGrade i := by fin_cases i <;> norm_num [bandGrade]

/-- A specified mixed observable: original gauge current plus the diagonal
Hilbert real-part scalar observation. The raw scalar response has its own mouth. -/
def sourceReader (phi : Scalar) (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) : Operator :=
  ∑ i : Fin 3, sourceBand phi z mu a i

theorem sourceReader_split (phi : Scalar) (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    sourceReader phi z mu a=gaugeReader z mu a+realPartScalar phi := by
  simp only [sourceReader, sourceBand, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, realPartScalar, smul_add]
  abel

private theorem fullWord_bilinear (cut : ℕ) (A B : Fin 3 → Operator) (r s t : ℝ) (F : Index) :
    fullWord cut (∑ i, A i) (∑ j, B j) r s t F=
      ∑ i : Fin 3, ∑ j : Fin 3, fullWord cut (A i) (B j) r s t F := by
  simp only [fullWord, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem source_fullWord_selected (cut : ℕ) (phi psi : Scalar) (z w : SourceCoordinateSlice)
    (mu nu : Component) (a b : NativeLie) (r s t : ℝ) (F : Index) :
    fullWord cut (sourceReader phi z mu a) (sourceReader psi w nu b) r s t F=
      ∑ i : Fin 3, ∑ j : Fin 3,
        selectedWord cut (sourceBand phi z mu a i) (sourceBand psi w nu b j)
          (bandGrade i) (bandGrade j) r s t F := by
  rw [sourceReader, sourceReader, fullWord_bilinear]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact fullWord_selected cut _ _ _ _ (sourceBand_homogeneous phi z mu a i)
    (sourceBand_homogeneous psi w nu b j) (bandGrade_lower i) (bandGrade_lower j) r s t F

theorem source_path_count : (∑ i : Fin 3, ∑ j : Fin 3, (paths (bandGrade i) (bandGrade j)).card)=15 := by decide

theorem rawScalar_gauge_fullWord_zero (cut : ℕ) (phi : Scalar) (z : SourceCoordinateSlice)
    (mu : Component) (a : NativeLie) (r s t : ℝ) (F : Index) :
    fullWord cut (rawScalar phi) (gaugeReader z mu a) r s t F=0 := by
  rw [fullWord_selected cut _ _ 1 0 (rawScalar_raises phi) (gauge_zero z mu a) (by omega) (by omega), selectedWord]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg (by omega)]

theorem dualScalar_gauge_fullWord_selected (cut : ℕ) (phi : Scalar) (z : SourceCoordinateSlice)
    (mu : Component) (a : NativeLie) (r s t : ℝ) (F : Index) :
    fullWord cut (dualScalar phi) (gaugeReader z mu a) r s t F=
      selectedWord cut (dualScalar phi) (gaugeReader z mu a) (-1) 0 r s t F :=
  fullWord_selected cut _ _ _ _ (dualScalar_lowers phi) (gauge_zero z mu a) (by omega) (by omega) r s t F

/-- Adjointing the actual word changes the entire generator family and reverses
all times and insertions. It is not an adjoint of the local reader alone. -/
def sharpWord (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) : Operator :=
  let D := GaussGradedCompression.compression F+(FullYSourceCutoffVolterra.cutoff cut).adjoint
  sourceProjection*SourceFiniteUnitary.time D (-t)*B.adjoint*SourceFiniteUnitary.time D (-s)*
    A.adjoint*SourceFiniteUnitary.time D (-r)*sourceProjection

theorem fullWord_adjoint (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) :
    (fullWord cut A B r s t F).adjoint=sharpWord cut A B r s t F := by
  have projection : star sourceProjection=sourceProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (NativeHistoryGrade.projection_symmetric sourceLabel)).star_eq
  have sharp (u : ℝ) : star (SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+FullYSourceCutoffVolterra.cutoff cut) u)=
      SourceFiniteUnitary.time (GaussGradedCompression.compression F+
        (FullYSourceCutoffVolterra.cutoff cut).adjoint) (-u) := by
    change (SourceFiniteUnitary.time _ u).adjoint= _
    rw [FullYSourceCutoffVolterra.time_adjoint]
    have h : (GaussGradedCompression.compression F+FullYSourceCutoffVolterra.cutoff cut).adjoint=
        GaussGradedCompression.compression F+(FullYSourceCutoffVolterra.cutoff cut).adjoint := by
      change star (_+_)=_
      rw [star_add, (GaussGradedCompression.compression_selfAdjoint F).star_eq]
      rfl
    rw [h]
  change star (fullWord cut A B r s t F)=_
  simp only [fullWord, sharpWord, star_mul, projection, sharp, ContinuousLinearMap.star_eq_adjoint, mul_assoc]

theorem wholeWord_real (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) (x y : GaussCoreHilbert.H) :
    ((inner ℂ x (fullWord cut A B r s t F y)).re : ℂ) =
      (1/2 : ℂ)*(inner ℂ x (fullWord cut A B r s t F y)+inner ℂ y (sharpWord cut A B r s t F x)) := by
  rw [← fullWord_adjoint, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    Complex.re_eq_add_conj]
  simp only [starRingEnd_self_apply]
  ring


open GaussUnitaryHistory (HistorySpace reader sourceFilter)

private theorem historyWord_bilinear (cut : ℕ) (A B : Fin 3 → Operator) (r s t : ℝ) :
    CanonicalGradedMixedReturn.fullWord cut (∑ i, A i) (∑ j, B j) r s t=
      ∑ i : Fin 3, ∑ j : Fin 3, CanonicalGradedMixedReturn.fullWord cut (A i) (B j) r s t := by
  have readerSum (C : Fin 3 → Operator) : reader (∑ i, C i)=∑ i, reader (C i) :=
    map_sum GaussYukawaInteraction.representation C Finset.univ
  simp only [CanonicalGradedMixedReturn.fullWord, readerSum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem source_historyWord_selected (cut : ℕ) (phi psi : Scalar) (z w : SourceCoordinateSlice)
    (mu nu : Component) (a b : NativeLie) (r s t : ℝ) :
    CanonicalGradedMixedReturn.fullWord cut (sourceReader phi z mu a) (sourceReader psi w nu b) r s t=
      ∑ i : Fin 3, ∑ j : Fin 3,
        CanonicalGradedMixedReturn.selectedWord cut (sourceBand phi z mu a i) (sourceBand psi w nu b j)
          (bandGrade i) (bandGrade j) r s t := by
  rw [sourceReader, sourceReader, historyWord_bilinear]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact CanonicalGradedMixedReturn.fullWord_selected cut _ _ _ _
    (sourceBand_homogeneous phi z mu a i) (sourceBand_homogeneous psi w nu b j)
    (bandGrade_lower i) (bandGrade_lower j) r s t

theorem rawScalar_gauge_historyWord_zero (cut : ℕ) (phi : Scalar) (z : SourceCoordinateSlice)
    (mu : Component) (a : NativeLie) (r s t : ℝ) :
    CanonicalGradedMixedReturn.fullWord cut (rawScalar phi) (gaugeReader z mu a) r s t=0 := by
  rw [CanonicalGradedMixedReturn.fullWord_selected cut _ _ 1 0
    (rawScalar_raises phi) (gauge_zero z mu a) (by omega) (by omega), CanonicalGradedMixedReturn.selectedWord]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg (by omega)]

theorem sourceEvolution_adjoint (cut : ℕ) (t : ℝ) :
    (FullYSourceCutoffVolterra.sourceEvolution cut t).adjoint=
      FullYSourceCutoffVolterra.sourceSharpEvolution cut (-t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, FullYSourceCutoffVolterra.source_evolution_sharp_pair, neg_neg]

theorem reader_adjoint (A : Operator) : (reader A).adjoint=reader A.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (SourceFamilyOperator.lift_pair sourceFilter (SourceFamilyOperator.constant A.adjoint)
    (SourceFamilyOperator.constant A) (fun _ u v => ContinuousLinearMap.adjoint_inner_left A v u) x y).symm

def historySharpWord (cut : ℕ) (A B : Operator) (r s t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  historyProjection*FullYSourceCutoffVolterra.sourceSharpEvolution cut (-t)*reader B.adjoint*
    FullYSourceCutoffVolterra.sourceSharpEvolution cut (-s)*reader A.adjoint*
    FullYSourceCutoffVolterra.sourceSharpEvolution cut (-r)*historyProjection

theorem historyWord_adjoint (cut : ℕ) (A B : Operator) (r s t : ℝ) :
    (CanonicalGradedMixedReturn.fullWord cut A B r s t).adjoint=historySharpWord cut A B r s t := by
  have projection : star historyProjection=historyProjection :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr CanonicalGradedCurrent.projection_pair).star_eq
  change star (CanonicalGradedMixedReturn.fullWord cut A B r s t)=_
  simp only [CanonicalGradedMixedReturn.fullWord, historySharpWord, star_mul, projection,
    ContinuousLinearMap.star_eq_adjoint, sourceEvolution_adjoint, reader_adjoint, mul_assoc]

theorem historyWord_real (cut : ℕ) (A B : Operator) (r s t : ℝ) (x y : HistorySpace) :
    ((inner ℂ x (CanonicalGradedMixedReturn.fullWord cut A B r s t y)).re : ℂ) = (1/2 : ℂ)*
      (inner ℂ x (CanonicalGradedMixedReturn.fullWord cut A B r s t y)+inner ℂ y (historySharpWord cut A B r s t x)) := by
  rw [← historyWord_adjoint, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    Complex.re_eq_add_conj]
  simp only [starRingEnd_self_apply]
  ring

end LowEnergy.CanonicalGradedMixedSource
