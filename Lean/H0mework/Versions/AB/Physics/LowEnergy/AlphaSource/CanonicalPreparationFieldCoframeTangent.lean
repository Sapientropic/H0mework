import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldGaugeTangent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldConstraintResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal StageNineCoframeVariation
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussQuantumMultiplier CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization PreparationVacuumSourceFieldFamily
open Set Filter
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : FiniteDimensional ℂ SourceMatrix := Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix := Matrix.finiteDimensional

open GaussNativePotential GaussNativeMatter
open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair PointwiseDiracSpinConnectionLift

open GaussCoreHilbert GaussCoreDifferential
open PreparationVacuumNonlinearFieldCurve
open SU7ExteriorBreakingYukawa GaussNativeEnergy StageNineCoframeLocalDifferentiability
open StageNineP286GaugeConnectionVariationDensity

open SourceQuantumScalarChart
open GaussLiveMomentum GaussDensityCore GaussFockPair GaussMomentumAdjoint
open MeasureTheory
open scoped Distributions InnerProductSpace

open PreparationVacuumSourceActionJets StageNineCoframeGravityGaugeRegularity

open StageNineLorentzConnectionVariation ProofFreeRicherAnholonomicSource
open PointwiseLorentzianCoframeJet

def lorentzPart : LorentzianCoframe →ₗ[ℝ] LorentzianCoframe where
  toFun A:=!![0,A 0 1,A 0 2,A 0 3;A 0 1,0,A 1 2,A 1 3;
    A 0 2,-A 1 2,0,A 2 3;A 0 3,-A 1 3,-A 2 3,0]
  map_add' A B:=by ext i j; fin_cases i <;> fin_cases j <;> simp <;> abel
  map_smul' r A:=by ext i j; fin_cases i <;> fin_cases j <;> simp

def lorentzCoordinates (A : LorentzianCoframe) : Fin 6 → ℝ :=
  ![-A 0 1,-A 0 2,-A 0 3,A 2 3,-A 1 3,A 1 2]

theorem lorentzPart_original (A : LorentzianCoframe) :
    lorentzPart A=lorentzSkewConnectionOfBivectorOneForm (fun _=>lorentzCoordinates A) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzPart,lorentzCoordinates,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      pairFirst,pairSecond,minkowskiInternalSign,Fin.sum_univ_six]

theorem lorentzPart_lower (A : LorentzianCoframe) : (A-lorentzPart A).IsLowerTriangular := by
  intro i j hij
  change i<j at hij
  fin_cases i <;> fin_cases j <;> simp [lorentzPart] at hij ⊢

theorem sourceCoframe_lower (z : SourceCoordinateSlice) : (CanonicalGradedSpatialSource.sourceCoframe z).IsLowerTriangular := by
  intro i j hij
  change i<j at hij
  fin_cases i <;> fin_cases j <;> simp [CanonicalGradedSpatialSource.sourceCoframe,GaussNativeEnergy.coframe] at hij ⊢

private theorem lower_mul (A B : LorentzianCoframe) (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) :
    (A*B).IsLowerTriangular := by
  intro i j hij
  change i<j at hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : i<k
  · rw [hA h,zero_mul]
  · have hkj : k<j:=lt_of_le_of_lt (le_of_not_gt h) hij
    have hb : B k j=0:=hB hkj
    rw [hb,mul_zero]

def normalizedCoframe (f : Field289) (z : SourceCoordinateSlice) : LorentzianCoframe :=
  fieldCoframe f*(CanonicalGradedSpatialSource.sourceCoframe z)⁻¹

def coframeResidual (f : Field289) (z : SourceCoordinateSlice) : LorentzianCoframe :=
  (normalizedCoframe f z-lorentzPart (normalizedCoframe f z))*CanonicalGradedSpatialSource.sourceCoframe z

def lowerCoordinates : LorentzianCoframe →ₗ[ℝ] Coframe where
  toFun A:=WithLp.toLp 2 ![A 1 1,A 2 1,A 2 2,A 3 1,A 3 2,A 3 3]
  map_add' A B:=by apply PiLp.ext; intro i; fin_cases i <;> simp
  map_smul' r A:=by apply PiLp.ext; intro i; fin_cases i <;> simp

def coframeSliceDirection (f : Field289) (z : SourceCoordinateSlice) : Coframe :=lowerCoordinates (coframeResidual f z)
def coframeTimeDirection (f : Field289) (z : SourceCoordinateSlice) : Fin 4 → ℝ :=fun i=>coframeResidual f z i 0

theorem lower_readback (A : LorentzianCoframe) (lower : A.IsLowerTriangular) :
    A=GaussNativeEnergy.coframe (fun i=>A i 0) (lowerCoordinates A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GaussNativeEnergy.coframe,lowerCoordinates]
  all_goals exact lower (by decide)

theorem coframe_field_reconstruction (f : Field289) (z : physicalChart) :
    fieldCoframe f=GaussNativeEnergy.coframe (coframeTimeDirection f z.val) (coframeSliceDirection f z.val)+
      lorentzPart (normalizedCoframe f z.val)*CanonicalGradedSpatialSource.sourceCoframe z.val := by
  have read:=lower_readback (coframeResidual f z.val)
    (lower_mul _ _ (lorentzPart_lower _) (sourceCoframe_lower _))
  change coframeResidual f z.val=GaussNativeEnergy.coframe (coframeTimeDirection f z.val) (coframeSliceDirection f z.val) at read
  rw [←read,coframeResidual,Matrix.sub_mul,sub_add_cancel,normalizedCoframe,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (coframe_nondegenerate z)),Matrix.mul_one]

private theorem matrix_product_smooth (F G : SourceCoordinateSlice → LorentzianCoframe) (z : SourceCoordinateSlice)
    (hF : ContDiffAt ℝ ∞ F z) (hG : ContDiffAt ℝ ∞ G z) :
    ContDiffAt ℝ ∞ (fun w=>F w*G w) z := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro k _
  exact ((contDiffAt_pi.mp (contDiffAt_pi.mp hF i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hG k) j))

theorem normalizedCoframe_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (normalizedCoframe f) z.val := by
  have he : ContDiff ℝ ∞ CanonicalGradedSpatialSource.sourceCoframe:=sourceState_smooth.fst
  have hi:=(coframe_inv_contDiffAt (CanonicalGradedSpatialSource.sourceCoframe z.val) (coframe_nondegenerate z)).comp z.val he.contDiffAt
  exact matrix_product_smooth _ _ z.val contDiffAt_const hi

theorem coframeResidual_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coframeResidual f) z.val :=
  matrix_product_smooth _ _ z.val ((normalizedCoframe_smooth f z).sub
    (lorentzPart.toContinuousLinearMap.contDiff.contDiffAt.comp z.val (normalizedCoframe_smooth f z)))
    sourceState_smooth.fst.contDiffAt

theorem coframeSlice_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coframeSliceDirection f) z.val :=
  lowerCoordinates.toContinuousLinearMap.contDiff.contDiffAt.comp z.val (coframeResidual_smooth f z)

-- This field is generated at every integration configuration, never frozen at one event.
def fieldVector (f : Field289) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (coframeSliceDirection f z,(gaugeParameters f z).2)

theorem fieldVector_smooth (f : Field289) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fieldVector f) z.val :=
  (coframeSlice_smooth f z).prodMk (gaugeParameters_smooth f z).snd

theorem original_field_decomposition (f : Field289) (z : physicalChart) :
    fieldCoframe f=GaussNativeEnergy.coframe (coframeTimeDirection f z.val) (fieldVector f z.val).1+
      lorentzPart (normalizedCoframe f z.val)*CanonicalGradedSpatialSource.sourceCoframe z.val ∧
    fieldAmbient f=orbitMap z.val (gaugeOrbitParameter f z.val)+sliceMap (fieldVector f z.val).2 :=
  ⟨coframe_field_reconstruction f z,(gauge_tangent_reconstruction f z).symm⟩

end LowEnergy.PreparationVacuumFieldConstraintResponse
