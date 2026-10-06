import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldQuantizationContacts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceFieldFamily
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineDynamicBreakingVacuum
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineDiracDualYukawaSpinJurisdiction
open StageNineCoframeLocalDifferentiability
open Stage9C.Material.SpinPair SU7MotherLieAlgebra
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open GaussHistoryHilbert GaussNativeEnergy GaussNativePotential
open PreparationVacuumMixedFieldReturn PreparationVacuumActualFieldQuantization
open scoped Matrix Matrix.Norms.L2Operator ContDiff BigOperators
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace

-- Unrepresented source fields and independent matter endpoints remain on actual.
def emitter (z : SourceCoordinateSlice) : StageNineHolonomicConfiguration :=
  { actual with
    coframe:=fun _=>CanonicalGradedSpatialSource.sourceCoframe z
    scalar:=fun _=>scalarField z
    gaugeConnection:=fun _ mu=>Fin.cases (actual.gaugeConnection 0 0)
      (fun j=>p286CoordinateEquiv.symm (connectionField z j)) mu }

def familyConnection (z : SourceCoordinateSlice) (mu : Fin 4) : SourceMatrix :=
  Quantum.operatorMatrix (FullQuantum.connection (emitter z) 0 mu)

def familyScalar (z : SourceCoordinateSlice) : SourceMatrix :=
  Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (scalarField z)))

def familyVolume (z : SourceCoordinateSlice) : ℂ :=
  ((|(CanonicalGradedSpatialSource.sourceCoframe z).det|:ℝ):ℂ)

def familyLower (z : SourceCoordinateSlice) (e : LorentzianCoframe) (p : CanonicalGradedSpatialSource.PhysicalMomentum) : SourceMatrix :=
  (∑ mu : Fin 4,coefficientMatrix mu e*familyConnection z mu)+familyScalar z+
    ∑ j : Fin 3,(Complex.I*(p j:ℂ)) • coefficientMatrix j.succ e

def familyHamiltonian (z : SourceCoordinateSlice) (e : LorentzianCoframe)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) : SourceMatrix :=
  timeSymbol (CoframeResponse.principalMatrix e) (familyLower z e p)

theorem emitted_matter (z : SourceCoordinateSlice) : (emitter z).matter=actual.matter := rfl
theorem emitted_independent_dual (z : SourceCoordinateSlice) :
    (emitter z).conjugateMatter=actual.conjugateMatter := rfl

theorem emitted_source_coframe : (emitter GaussHistoryHilbert.sourcePoint.val).coframe 0=actual.coframe 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem emitted_source_scalar : (emitter GaussHistoryHilbert.sourcePoint.val).scalar 0=actual.scalar 0 := by
  change vacuum+(0:Scalar)=actual.scalar 0
  rw [add_zero,actual_scalar]
  rfl

theorem emitted_source_gauge (mu : Fin 4) :
    (emitter GaussHistoryHilbert.sourcePoint.val).gaugeConnection 0 mu=actual.gaugeConnection 0 mu := by
  refine Fin.cases (by rfl) (fun j=>?_) mu
  change p286CoordinateEquiv.symm (p286CoordinateEquiv (actual.gaugeConnection 0 j.succ))=_
  exact p286CoordinateEquiv.symm_apply_apply _

theorem familyConnection_source (mu : Fin 4) :
    familyConnection GaussHistoryHilbert.sourcePoint.val mu=Electromagnetic.CanonicalCoframe.sourceConnection mu := by
  unfold familyConnection Electromagnetic.CanonicalCoframe.sourceConnection
  apply congrArg Quantum.operatorMatrix
  unfold FullQuantum.connection
  rw [emitted_source_gauge]
  rfl

theorem familyScalar_source : familyScalar GaussHistoryHilbert.sourcePoint.val=Electromagnetic.CanonicalCoframe.sourceScalar := by
  have same:=emitted_source_scalar
  change scalarField GaussHistoryHilbert.sourcePoint.val=actual.scalar 0 at same
  rw [familyScalar,same]
  rfl

theorem coframe_nondegenerate (z : physicalChart) :
    (CanonicalGradedSpatialSource.sourceCoframe z.val).det≠0 := by
  rw [CanonicalGradedSpatialSource.sourceCoframe,coframe_determinant,source_time_generated]
  exact mul_ne_zero lapse_pos.ne' (volume_pos z).ne'

theorem familyVolume_generated (z : physicalChart) : familyVolume z.val=(lapse:ℂ)*(volume z.val:ℂ) := by
  rw [familyVolume,CanonicalGradedSpatialSource.sourceCoframe,coframe_determinant,source_time_generated]
  change ((|lapse*volume z.val|:ℝ):ℂ)=_
  rw [abs_of_pos (mul_pos lapse_pos (volume_pos z)),Complex.ofReal_mul]

theorem spatialVolume_source : volume GaussHistoryHilbert.sourcePoint.val=1 := by
  norm_num [volume,GaussHistoryHilbert.sourcePoint,SourceQuantumConfigurationHilbert.sourceCoframe_eq]

theorem familyVolume_source : familyVolume GaussHistoryHilbert.sourcePoint.val=(lapse:ℂ) := by
  rw [familyVolume_generated]
  rw [spatialVolume_source,Complex.ofReal_one,mul_one]

theorem family_principal_same (z : physicalChart) :
    CoframeResponse.principalMatrix (CanonicalGradedSpatialSource.sourceCoframe z.val)=
      CoframeResponse.principalMatrix (actual.coframe 0) := by
  unfold CoframeResponse.principalMatrix
  congr 1
  apply LinearMap.ext
  intro v
  rw [actual_temporal_principal]
  simp only [currentCoframeMatterTemporalPrincipal,CanonicalGradedSpatialSource.temporal_gamma,
    LinearMap.smul_apply,coframeDiracMatrixMatterAction_smul_matrix,smul_smul]

def familyPhase (z : SourceCoordinateSlice) : SourceMatrix :=
  (Complex.I*(familyVolume z)⁻¹) • Ring.inverse
    (CoframeResponse.principalMatrix (CanonicalGradedSpatialSource.sourceCoframe z))

theorem familyPhase_generated (z : physicalChart) :
    familyPhase z.val=(volume z.val:ℂ)⁻¹ • sourcePhaseMatrix := by
  rw [familyPhase,family_principal_same,familyVolume_generated,source_phase_inverse,smul_smul,mul_inv_rev]
  congr 1
  ring

theorem familyPhase_source : familyPhase GaussHistoryHilbert.sourcePoint.val=sourcePhaseMatrix := by
  rw [familyPhase_generated]
  rw [spatialVolume_source,Complex.ofReal_one,inv_one,one_smul]


theorem familyLower_original (z : SourceCoordinateSlice) (e : LorentzianCoframe)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    familyLower z e p=Quantum.operatorMatrix
      (lowerSymbol {emitter z with coframe:=fun _=>e} 0 p) := by
  simp only [familyLower,lowerSymbol,knownSymbol,map_add,map_smul,map_sum,map_one,Quantum.matrix_composition]
  simp only [currentCoframeMatterTemporalPrincipal,map_smul,coefficientMatrix,spinCoordinates,
    LinearMap.coe_mk,AddHom.coe_mk,FullQuantum.connection,familyConnection,familyScalar,emitter,
    map_add,Matrix.smul_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one,
    Finset.sum_add_distrib,Finset.smul_sum,smul_add,smul_smul]
  have scalar (c : ℂ) : Complex.I*c*Complex.I=Complex.I*(Complex.I*c) := by ring
  simp only [scalar,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  abel

theorem familyHamiltonian_original (z : physicalChart)
    (p : CanonicalGradedSpatialSource.PhysicalMomentum) :
    familyHamiltonian z.val (CanonicalGradedSpatialSource.sourceCoframe z.val) p=
      Quantum.operatorMatrix (FullQuantum.hamiltonian (emitter z.val) 0 p) := by
  rw [familyHamiltonian,familyLower_original]
  unfold timeSymbol
  rw [principal_inverse_original _
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z)]
  have same : {emitter z.val with coframe:=fun _=>CanonicalGradedSpatialSource.sourceCoframe z.val}=emitter z.val := rfl
  rw [same,hamiltonian_lower_original (emitter z.val) 0 p (CanonicalGradedSpatialSource.temporal_noncharacteristic z)]
  simp only [map_smul,Quantum.matrix_composition]
  rfl

end LowEnergy.PreparationVacuumSourceFieldFamily
