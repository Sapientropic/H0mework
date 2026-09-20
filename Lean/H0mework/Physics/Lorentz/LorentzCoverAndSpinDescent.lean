import H0mework.Physics.Gauge.GlobalConnection
import H0mework.Physics.Dirac.SpinMatterBundle
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Stage-9A Spin--Lorentz cover and smooth connection descent

The standard Pauli--Hermitian encoding is used to construct an actual
multiplicative action of `SL(2,ℂ)` on the existing real four-dimensional
base carrier.  The action is proved real-linear, invertible, multiplicative,
and Minkowski-quadratic-form preserving.  A concrete dilation proves that
the Lorentz action is nontrivial, while the nonidentity central sign is
identified with the identity action, exposing the expected two-to-one
feature without storing a cover certificate.

For the source-generated coframe, smoothness of the Lorentz connection is
proved componentwise from the source coframe itself.  Matrix inverses are
handled through determinant and adjugate formulas under the already-derived
global nondegeneracy theorem.  The resulting chart-local spin connections
therefore descend across the generated identity Spin transition.  No
smoothness, cover, or descent receipt is accepted from the source.
-/

namespace SaturationMonoid.PhysicsCore.StageNineLorentzCoverAndSpinDescent

open ProofFreeRicherAnholonomicSource
open PointwiseLorentzianCoframeJet
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNineGlobalConnection
open StageNineSpinMatterBundle
open Matrix
open scoped MatrixGroups ComplexConjugate

noncomputable section

abbrev PauliMatrix := Matrix (Fin 2) (Fin 2) ℂ

def pauliEncode (point : BasePoint) : PauliMatrix :=
  !![(point 0 : ℂ) + point 3,
      (point 1 : ℂ) - Complex.I * point 2;
     (point 1 : ℂ) + Complex.I * point 2,
      (point 0 : ℂ) - point 3]

def pauliDecode (matrix : PauliMatrix) : BasePoint :=
  WithLp.toLp 2 fun index =>
    if index = 0 then ((matrix 0 0 + matrix 1 1).re) / 2
    else if index = 1 then ((matrix 0 1 + matrix 1 0).re) / 2
    else if index = 2 then ((matrix 1 0 - matrix 0 1).im) / 2
    else ((matrix 0 0 - matrix 1 1).re) / 2

theorem pauliDecode_encode (point : BasePoint) :
    pauliDecode (pauliEncode point) = point := by
  apply PiLp.ext
  intro index
  fin_cases index <;> simp [pauliDecode, pauliEncode]

theorem pauliEncode_injective : Function.Injective pauliEncode := by
  intro first second equality
  rw [← pauliDecode_encode first, ← pauliDecode_encode second, equality]

theorem pauliEncode_add (first second : BasePoint) :
    pauliEncode (first + second) = pauliEncode first + pauliEncode second := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pauliEncode]
  all_goals ring

theorem pauliEncode_smul (scalar : ℝ) (point : BasePoint) :
    pauliEncode (scalar • point) =
      (scalar : ℂ) • pauliEncode point := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pauliEncode]
  all_goals ring

theorem pauliEncode_isHermitian (point : BasePoint) :
    (pauliEncode point).IsHermitian := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pauliEncode, Matrix.conjTranspose_apply]
  ring

theorem pauliEncode_decode_of_isHermitian
    (matrix : PauliMatrix) (hermitian : matrix.IsHermitian) :
    pauliEncode (pauliDecode matrix) = matrix := by
  have h00 := congrFun (congrFun hermitian 0) 0
  have h01 := congrFun (congrFun hermitian 0) 1
  have h10 := congrFun (congrFun hermitian 1) 0
  have h11 := congrFun (congrFun hermitian 1) 1
  simp only [Matrix.conjTranspose_apply] at h00 h01 h10 h11
  have h00re := congrArg Complex.re h00
  have h00im := congrArg Complex.im h00
  have h01re := congrArg Complex.re h01
  have h01im := congrArg Complex.im h01
  have h10re := congrArg Complex.re h10
  have h10im := congrArg Complex.im h10
  have h11re := congrArg Complex.re h11
  have h11im := congrArg Complex.im h11
  simp at h00re h00im h01re h01im h10re h10im h11re h11im
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [pauliEncode, pauliDecode]
  all_goals apply Complex.ext <;> simp_all <;> linarith

def spinHermitianAction
    (groupElement : SpinPlus13) (point : BasePoint) : BasePoint :=
  pauliDecode
    (groupElement.1 * pauliEncode point * star groupElement.1)

theorem spinHermitianAction_encode
    (groupElement : SpinPlus13) (point : BasePoint) :
    pauliEncode (spinHermitianAction groupElement point) =
      groupElement.1 * pauliEncode point * star groupElement.1 := by
  change pauliEncode
      (pauliDecode (groupElement.1 * pauliEncode point * star groupElement.1)) =
    groupElement.1 * pauliEncode point * star groupElement.1
  apply pauliEncode_decode_of_isHermitian
  change star (groupElement.1 * pauliEncode point * star groupElement.1) = _
  simp only [star_mul, star_star]
  have pointHermitian : star (pauliEncode point) = pauliEncode point := by
    exact (pauliEncode_isHermitian point).star_eq
  rw [pointHermitian]
  noncomm_ring

@[simp] theorem spinHermitianAction_one (point : BasePoint) :
    spinHermitianAction 1 point = point := by
  apply pauliEncode_injective
  rw [spinHermitianAction_encode]
  simp

theorem spinHermitianAction_mul
    (first second : SpinPlus13) (point : BasePoint) :
    spinHermitianAction (first * second) point =
      spinHermitianAction first (spinHermitianAction second point) := by
  apply pauliEncode_injective
  rw [spinHermitianAction_encode, spinHermitianAction_encode,
    spinHermitianAction_encode]
  change
    (first.1 * second.1) * pauliEncode point *
        star (first.1 * second.1) = _
  rw [star_mul]
  noncomm_ring

theorem spinHermitianAction_add
    (groupElement : SpinPlus13) (first second : BasePoint) :
    spinHermitianAction groupElement (first + second) =
      spinHermitianAction groupElement first +
        spinHermitianAction groupElement second := by
  apply pauliEncode_injective
  rw [spinHermitianAction_encode]
  change groupElement.1 * pauliEncode (first + second) * star groupElement.1 =
    pauliEncode (spinHermitianAction groupElement first +
      spinHermitianAction groupElement second)
  rw [pauliEncode_add, pauliEncode_add,
    spinHermitianAction_encode, spinHermitianAction_encode]
  rw [Matrix.mul_add, Matrix.add_mul]

theorem spinHermitianAction_smul
    (groupElement : SpinPlus13) (scalar : ℝ) (point : BasePoint) :
    spinHermitianAction groupElement (scalar • point) =
      scalar • spinHermitianAction groupElement point := by
  apply pauliEncode_injective
  rw [spinHermitianAction_encode]
  change groupElement.1 * pauliEncode (scalar • point) * star groupElement.1 =
    pauliEncode (scalar • spinHermitianAction groupElement point)
  rw [pauliEncode_smul, pauliEncode_smul, spinHermitianAction_encode]
  rw [Matrix.mul_smul, Matrix.smul_mul]

def spinLorentzLinearMap (groupElement : SpinPlus13) :
    BasePoint →ₗ[ℝ] BasePoint where
  toFun := spinHermitianAction groupElement
  map_add' := spinHermitianAction_add groupElement
  map_smul' := spinHermitianAction_smul groupElement

theorem spinLorentzLinearMap_mul
    (first second : SpinPlus13) :
    spinLorentzLinearMap (first * second) =
      (spinLorentzLinearMap first).comp (spinLorentzLinearMap second) := by
  apply LinearMap.ext
  intro point
  exact spinHermitianAction_mul first second point

def spinLorentzLinearEquiv (groupElement : SpinPlus13) :
    BasePoint ≃ₗ[ℝ] BasePoint where
  toLinearMap := spinLorentzLinearMap groupElement
  invFun := spinHermitianAction groupElement⁻¹
  left_inv point := by
    change spinHermitianAction groupElement⁻¹
      (spinHermitianAction groupElement point) = point
    rw [← spinHermitianAction_mul]
    simp
  right_inv point := by
    change spinHermitianAction groupElement
      (spinHermitianAction groupElement⁻¹ point) = point
    rw [← spinHermitianAction_mul]
    simp

def spinLorentzCover : SpinPlus13 →* (BasePoint ≃ₗ[ℝ] BasePoint) where
  toFun := spinLorentzLinearEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro point
    exact spinHermitianAction_one point
  map_mul' first second := by
    apply LinearEquiv.ext
    intro point
    exact spinHermitianAction_mul first second point

def minkowskiQuadratic (point : BasePoint) : ℝ :=
  -(point 0)^2 + (point 1)^2 + (point 2)^2 + (point 3)^2

theorem pauliEncode_det (point : BasePoint) :
    Matrix.det (pauliEncode point) = -(minkowskiQuadratic point : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [pauliEncode, minkowskiQuadratic]
  ring_nf
  simp
  ring

theorem spinLorentzCover_preserves_minkowski
    (groupElement : SpinPlus13) (point : BasePoint) :
    minkowskiQuadratic (spinLorentzCover groupElement point) =
      minkowskiQuadratic point := by
  have determinantEquality := congrArg Matrix.det
    (spinHermitianAction_encode groupElement point)
  rw [Matrix.det_mul, Matrix.det_mul, pauliEncode_det,
    pauliEncode_det] at determinantEquality
  have groupDet : Matrix.det groupElement.1 = 1 := groupElement.property
  have starDet : Matrix.det (star groupElement.1) = 1 := by
    change Matrix.det groupElement.1ᴴ = 1
    rw [Matrix.det_conjTranspose, groupDet]
    simp
  rw [groupDet, starDet] at determinantEquality
  norm_num at determinantEquality ⊢
  exact_mod_cast determinantEquality

theorem spinDilation_lorentz_timeCoordinate :
    spinLorentzCover spinDilation stageNineUnitPoint 0 = 17 / 8 := by
  have three_ne_zero : (3 : LorentzianIndex) ≠ 0 := by decide
  norm_num [spinLorentzCover, spinLorentzLinearEquiv,
    spinLorentzLinearMap, spinHermitianAction, pauliDecode, pauliEncode,
    spinDilation, stageNineUnitPoint, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, three_ne_zero]

theorem spinLorentzCover_nontrivial : spinLorentzCover spinDilation ≠ 1 := by
  intro equality
  have atUnit := LinearEquiv.congr_fun equality stageNineUnitPoint
  have timeCoordinate := congrArg (fun point : BasePoint => point 0) atUnit
  rw [spinDilation_lorentz_timeCoordinate] at timeCoordinate
  norm_num [stageNineUnitPoint] at timeCoordinate

def spinCentralSign : SpinPlus13 := by
  refine ⟨-(1 : PauliMatrix), ?_⟩
  norm_num [Matrix.det_fin_two]

theorem spinCentralSign_ne_one : spinCentralSign ≠ 1 := by
  intro equality
  have entry := congrArg (fun value : SpinPlus13 => value.1 0 0) equality
  norm_num [spinCentralSign, Matrix.one_apply] at entry

theorem spinCentralSign_action (point : BasePoint) :
    spinLorentzCover spinCentralSign point = point := by
  change spinHermitianAction spinCentralSign point = point
  apply pauliEncode_injective
  rw [spinHermitianAction_encode]
  simp [spinCentralSign]

theorem spinLorentzCover_identifies_central_sign :
    spinLorentzCover spinCentralSign = spinLorentzCover 1 := by
  apply LinearEquiv.ext
  intro point
  rw [spinCentralSign_action]
  exact (spinHermitianAction_one point).symm


theorem matrixDet_componentwiseSmooth
    {n : Type} [Fintype n] [DecidableEq n]
    (matrix : BasePoint → Matrix n n ℝ)
    (smooth : ∀ row column,
      ContDiff ℝ ⊤ (fun point => matrix point row column)) :
    ContDiff ℝ ⊤ (fun point => Matrix.det (matrix point)) := by
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro permutation _
  apply ContDiff.const_smul
  apply contDiff_prod
  intro column _
  exact smooth (permutation column) column

theorem matrixAdjugate_componentwiseSmooth
    {n : Type} [Fintype n] [DecidableEq n]
    (matrix : BasePoint → Matrix n n ℝ)
    (smooth : ∀ row column,
      ContDiff ℝ ⊤ (fun point => matrix point row column))
    (row column : n) :
    ContDiff ℝ ⊤ (fun point => (matrix point).adjugate row column) := by
  simp only [Matrix.adjugate_apply]
  apply matrixDet_componentwiseSmooth
  intro updatedRow updatedColumn
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact smooth updatedRow updatedColumn

theorem matrixInv_componentwiseSmooth
    {n : Type} [Fintype n] [DecidableEq n]
    (matrix : BasePoint → Matrix n n ℝ)
    (smooth : ∀ row column,
      ContDiff ℝ ⊤ (fun point => matrix point row column))
    (nonsingular : ∀ point, Matrix.det (matrix point) ≠ 0)
    (row column : n) :
    ContDiff ℝ ⊤ (fun point => (matrix point)⁻¹ row column) := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.mul
  · rw [show
      (fun x => Ring.inverse (matrix x).det) =
        (fun x => (matrix x).det⁻¹) by
          funext x
          exact Ring.inverse_eq_inv _]
    exact (matrixDet_componentwiseSmooth matrix smooth).inv nonsingular
  · exact matrixAdjugate_componentwiseSmooth matrix smooth row column

theorem canonicalCoframe_componentwiseSmooth
    (row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      canonicalPhysicalSource.coframeAt point row column) := by
  exact contDiff_pi.mp (contDiff_pi.mp
    canonicalPhysicalSource.coframeAt_contDiff row) column

theorem metric_componentwiseSmooth
    (row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).metric row column) := by
  unfold PointwiseLorentzianCoframeJet.metric
  unfold lorentzianMetricOfCoframe
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiff.sum
  intro internal _
  apply ContDiff.mul
  · apply ContDiff.sum
    intro internal' _
    apply ContDiff.mul
    · exact canonicalCoframe_componentwiseSmooth internal' row
    · exact contDiff_const
  · exact canonicalCoframe_componentwiseSmooth internal column

theorem coframeInv_componentwiseSmooth
    (row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.coframeAt point)⁻¹ row column) := by
  exact matrixInv_componentwiseSmooth canonicalPhysicalSource.coframeAt
    canonicalCoframe_componentwiseSmooth
    canonicalPhysicalSource_globally_nondegenerate row column

theorem metricInv_componentwiseSmooth
    (row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).metric⁻¹ row column) := by
  exact matrixInv_componentwiseSmooth
    (fun point => (canonicalPhysicalSource.jetAt point).metric)
    metric_componentwiseSmooth
    (fun point =>
      (canonicalPhysicalSource.jetAt point).metric_det_ne_zero_of_coframe
        (canonicalPhysicalSource_globally_nondegenerate point))
    row column

theorem metricDerivative_componentwiseSmooth
    (mu row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).metricDerivative mu row column) := by
  unfold PointwiseLorentzianCoframeJet.metricDerivative
  apply ContDiff.sum
  intro internal _
  apply ContDiff.mul contDiff_const
  apply ContDiff.add
  · apply ContDiff.mul contDiff_const
    exact canonicalCoframe_componentwiseSmooth internal column
  · apply ContDiff.mul
    · exact canonicalCoframe_componentwiseSmooth internal row
    · exact contDiff_const

theorem loweredLeviCivita_componentwiseSmooth
    (rho mu nu : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).loweredLeviCivitaConnection
        rho mu nu) := by
  unfold PointwiseLorentzianCoframeJet.loweredLeviCivitaConnection
  exact ((metricDerivative_componentwiseSmooth mu nu rho).add
    (metricDerivative_componentwiseSmooth nu mu rho) |>.sub
      (metricDerivative_componentwiseSmooth rho mu nu)).div_const 2

theorem leviCivita_componentwiseSmooth
    (upper mu nu : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).leviCivitaConnection
        upper mu nu) := by
  unfold PointwiseLorentzianCoframeJet.leviCivitaConnection
  unfold PointwiseLorentzianCoframeJet.leviCivitaConnectionVector
  unfold Matrix.mulVec dotProduct
  apply ContDiff.sum
  intro rho _
  apply ContDiff.mul
  · exact metricInv_componentwiseSmooth upper rho
  · exact loweredLeviCivita_componentwiseSmooth rho mu nu

theorem coordinateConnectionMatrix_componentwiseSmooth
    (mu row column : LorentzianIndex) :
    ContDiff ℝ ⊤ (fun point : BasePoint =>
      (canonicalPhysicalSource.jetAt point).coordinateConnectionMatrix
        mu row column) := by
  exact leviCivita_componentwiseSmooth row mu column

theorem canonicalLorentzConnection_componentwiseSmooth
    (mu internalOut internalIn : LorentzianIndex) :
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        generatedLorentzConnectionAt positiveSmoothUnifiedSource point
          mu internalOut internalIn) := by
  unfold generatedLorentzConnectionAt
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnection
  unfold PointwiseLorentzianCoframeJet.lorentzSpinConnectionMatrix
  simp only [Matrix.mul_apply, Matrix.sub_apply]
  apply ContDiff.sum
  intro coordinate _
  apply ContDiff.mul
  · apply ContDiff.sub
    · apply ContDiff.sum
      intro upper _
      exact (canonicalCoframe_componentwiseSmooth internalOut upper).mul
        (coordinateConnectionMatrix_componentwiseSmooth mu upper coordinate)
    · exact contDiff_const
  · exact coframeInv_componentwiseSmooth coordinate internalIn


def generatedLocalLorentzConnection
    (source : SmoothUnifiedSource) (_chart : StageNineChart)
    (point : BasePoint) : PointwiseLorentzSpinConnection :=
  generatedLorentzConnectionAt source point

theorem generatedLocalLorentzConnection_overlap
    (source : SmoothUnifiedSource) (initial terminal : StageNineChart)
    (point : BasePoint) :
    generatedLocalLorentzConnection source initial point =
      generatedLocalLorentzConnection source terminal point :=
  rfl

def LorentzConnectionComponentwiseSmooth
    (source : SmoothUnifiedSource) : Prop :=
  ∀ mu internalOut internalIn,
    ContDiff ℝ ⊤
      (fun point : BasePoint =>
        generatedLorentzConnectionAt source point mu internalOut internalIn)

theorem positive_generatedLorentzConnection_componentwiseSmooth :
    LorentzConnectionComponentwiseSmooth positiveSmoothUnifiedSource :=
  canonicalLorentzConnection_componentwiseSmooth

def handFilledIdentityLorentzCover :
    SpinPlus13 →* (BasePoint ≃ₗ[ℝ] BasePoint) := 1

theorem handFilledIdentityLorentzCover_rejected :
    handFilledIdentityLorentzCover ≠ spinLorentzCover := by
  intro equality
  have atDilation := DFunLike.congr_fun equality spinDilation
  exact spinLorentzCover_nontrivial atDilation.symm

/-- S9-A6 positive checkpoint: the Spin carrier acts through a generated,
nontrivial Minkowski-preserving homomorphism, its central sign is genuinely
collapsed, and the same source coframe produces a smooth chart-descending
Lorentz connection. -/
theorem positiveSource_generates_spinLorentzCover_and_smoothDescent :
    (∀ groupElement point,
      minkowskiQuadratic (spinLorentzCover groupElement point) =
        minkowskiQuadratic point) ∧
      spinLorentzCover spinDilation ≠ 1 ∧
      spinCentralSign ≠ 1 ∧
      spinLorentzCover spinCentralSign = spinLorentzCover 1 ∧
      LorentzConnectionComponentwiseSmooth positiveSmoothUnifiedSource ∧
      (∀ initial terminal point,
        generatedLocalLorentzConnection positiveSmoothUnifiedSource
            initial point =
          generatedLocalLorentzConnection positiveSmoothUnifiedSource
            terminal point) ∧
      (∀ point,
        LorentzSkew
          (generatedLorentzConnectionAt positiveSmoothUnifiedSource point)) :=
  ⟨spinLorentzCover_preserves_minkowski,
    spinLorentzCover_nontrivial,
    spinCentralSign_ne_one,
    spinLorentzCover_identifies_central_sign,
    positive_generatedLorentzConnection_componentwiseSmooth,
    generatedLocalLorentzConnection_overlap positiveSmoothUnifiedSource,
    positive_generatedLorentzConnection_lorentzSkew⟩

end

end SaturationMonoid.PhysicsCore.StageNineLorentzCoverAndSpinDescent

