import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationMixedDensityContacts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedFieldReturn
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField ProofFreeRicherAnholonomicSource StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineDiracDualYukawaSpinJurisdiction
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorBreakingYukawa
open StageNineExteriorMotherLieYukawaDerivation
open SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open Electromagnetic.CanonicalCoframe
open YangMills.FullPairing Stage10.CanonicalMatter
open scoped BigOperators Matrix InnerProductSpace
local instance : DecidableEq Quantum.Index := Classical.decEq _

def sourcePhaseMatrix : SourceMatrix := Quantum.operatorMatrix phaseInverse

theorem source_volume_generated : sourceVolume=(lapse:ℂ) := by
  rw [sourceVolume,actual_coframe,homogeneousCoframe_det,abs_of_pos lapse_pos]

theorem phase_principal_generated :
    sourcePhaseMatrix*FullQuantum.CoframeResponse.principalMatrix (actual.coframe 0)=
      (Complex.I*(lapse:ℂ)⁻¹) • (1:SourceMatrix) := by
  rw [sourcePhaseMatrix,FullQuantum.CoframeResponse.principalMatrix,←Quantum.matrix_composition]
  have same : phaseInverse.comp (currentCoframeMatterTemporalPrincipal (actual.coframe 0))=
      (Complex.I*(lapse:ℂ)⁻¹) • (1:YangMills.FullPairing.Mother) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply,actual_temporal_principal,map_smul,phase_inverse_source,
      LinearMap.smul_apply,Module.End.one_apply]
  rw [same,map_smul,map_one]

theorem source_phase_inverse : sourcePhaseMatrix=
    (Complex.I*(lapse:ℂ)⁻¹) • Ring.inverse
      (FullQuantum.CoframeResponse.principalMatrix (actual.coframe 0)) := by
  have generated:=congrArg (fun M:SourceMatrix=>M*Ring.inverse
    (FullQuantum.CoframeResponse.principalMatrix (actual.coframe 0))) phase_principal_generated
  have unit:=principalMatrix_regular (actual.coframe 0) (actual_noncharacteristic 0)
  simpa only [mul_assoc,Ring.mul_inverse_cancel _ unit,mul_one,smul_mul_assoc,one_mul] using generated

-- The action reader and the Hamiltonian forcing have opposite source signs.
theorem actual_forcing_reader (f : Field289) (i : Fin 4) :
    fieldHamiltonianCoefficients (sourceField f) i=
      -(sourcePhaseMatrix*fieldDensityCoefficients (sourceField f) i) := by
  rw [fieldHamiltonianCoefficients,source_phase_inverse,source_volume_generated,smul_mul_assoc]
  simp only [neg_mul,neg_smul]

def sourceDensityMother (f : Field289) (i : Fin 4) : YangMills.FullPairing.Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm (fieldDensityCoefficients (sourceField f) i)

def sourceMixedMother (reader force : Field289) (i : Fin 4) : YangMills.FullPairing.Mother :=
  Quantum.operatorMatrix.toLinearEquiv.symm
    (mixedDensityCoefficients (sourceField reader) (sourceField force) i+
      shellContactCoefficients (sourceField reader) (sourceField force) i)

theorem source_field_action_gram (f : Field289) (i : Fin 4) (point : BasePoint)
    (preparation : YangMills.FullPairing.Mother) :
    actual.conjugateMatter point
      (Stage10.CanonicalMatter.canonicalDual preparation (sourceDensityMother f i (preparation (actual.matter point))))=
      4*(spinScale:ℂ)*inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
        (operator ((phaseInverse.comp (sourceDensityMother f i)).comp preparation)
          (YangMills.FullPairing.prepared point)) := by
  have paired (v : DiracExteriorMatterCarrier) :
      Stage10.CanonicalMatter.canonicalDual preparation (sourceDensityMother f i (preparation v))=
        pairedMother preparation ((phaseInverse.comp (sourceDensityMother f i)).comp preparation) v := by
    simp [Stage10.CanonicalMatter.canonicalDual,pairedMother,fromOperator,operator]
  rw [paired,dual_gram]

theorem source_mixed_action_gram (reader force : Field289) (i : Fin 4) (point : BasePoint)
    (preparation : YangMills.FullPairing.Mother) :
    actual.conjugateMatter point
      (Stage10.CanonicalMatter.canonicalDual preparation (sourceMixedMother reader force i (preparation (actual.matter point))))=
      4*(spinScale:ℂ)*inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
        (operator ((phaseInverse.comp (sourceMixedMother reader force i)).comp preparation)
          (YangMills.FullPairing.prepared point)) := by
  have paired (v : DiracExteriorMatterCarrier) :
      Stage10.CanonicalMatter.canonicalDual preparation (sourceMixedMother reader force i (preparation v))=
        pairedMother preparation ((phaseInverse.comp (sourceMixedMother reader force i)).comp preparation) v := by
    simp [Stage10.CanonicalMatter.canonicalDual,pairedMother,fromOperator,operator]
  rw [paired,dual_gram]

theorem source_reader_same (f : Field289) (i : Fin 4) :
    fieldCoefficients (sourceField f) i=operator (phaseInverse.comp (sourceDensityMother f i)) := rfl

theorem source_mixed_reader_same (reader force : Field289) (i : Fin 4) :
    mixedCoefficients (sourceField reader) (sourceField force) i=
      operator (phaseInverse.comp (sourceMixedMother reader force i)) := rfl

private theorem internal_spin_commute (a : SU7MotherLieMatrix) (M : DiracMatrix)
    (v : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction a (diracMatrixMatterAction M v)=
      diracMatrixMatterAction M (diracExteriorMotherLieAction a v) := by
  simpa only [diracExteriorMotherLieAction,LinearMap.comp_apply] using
    (LinearMap.congr_fun (diracMatrixMatterAction_commutes_internal M
      (exteriorSpinorMotherLieAction a)) v).symm

theorem repaired_yukawa_covariance (a : SU7MotherLieMatrix)
    (s : ExteriorBreakingScalarCarrier) (v : DiracExteriorMatterCarrier) :
    diracExteriorMotherLieAction a (diracDualRightChiralYukawaAction s v)=
      diracDualRightChiralYukawaAction (exteriorMotherLieAction 4 a s) v+
        diracDualRightChiralYukawaAction s (diracExteriorMotherLieAction a v) := by
  unfold diracDualRightChiralYukawaAction
  simp only [LinearMap.comp_apply]
  rw [diracExteriorYukawaInternalAction_motherLieAction,internal_spin_commute]

-- Independent primal and dual endpoint variations cancel the actual scalar torque.
theorem independent_dual_scalar_ward (a : SU7MotherLieMatrix)
    (s : ExteriorBreakingScalarCarrier) (v : DiracExteriorMatterCarrier)
    (chi : Module.Dual ℂ DiracExteriorMatterCarrier) :
    chi (diracDualRightChiralYukawaAction (exteriorMotherLieAction 4 a s) v)+
      chi (diracDualRightChiralYukawaAction s (diracExteriorMotherLieAction a v))+
      (-chi.comp (diracExteriorMotherLieAction a)) (diracDualRightChiralYukawaAction s v)=0 := by
  rw [←map_add,←repaired_yukawa_covariance]
  simp



-- Four independent off-shell momenta retain both endpoint variations.
def nativeGaugeMatrix (a : SU7MotherLieMatrix) : SourceMatrix :=
  Quantum.operatorMatrix (diracExteriorMotherLieAction a)

def nativeScalarOrbitMatrix (a : SU7MotherLieMatrix) : SourceMatrix :=
  Quantum.operatorMatrix (diracDualRightChiralYukawaAction
    (exteriorMotherLieAction 4 a (scalarCoordinateEquiv.symm (actual.scalar 0))))

def nativeFullSymbol (p : Fin 4 → ℂ) : SourceMatrix :=
  (∑ mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*
    (p mu • (1:SourceMatrix)+sourceConnection mu))+sourceScalar

def nativeGaugeVertex (a : SU7MotherLieMatrix) (transfer : Fin 4 → ℂ) : SourceMatrix :=
  sourceVolume • ((∑ mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*
    (nativeGaugeMatrix a*sourceConnection mu-sourceConnection mu*nativeGaugeMatrix a-
      transfer mu • nativeGaugeMatrix a))+nativeScalarOrbitMatrix a)

theorem native_scalar_orbit (a : SU7MotherLieMatrix) :
    nativeGaugeMatrix a*sourceScalar=nativeScalarOrbitMatrix a+sourceScalar*nativeGaugeMatrix a := by
  unfold nativeGaugeMatrix sourceScalar nativeScalarOrbitMatrix
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition,←map_add]
  congr 1
  apply LinearMap.ext
  intro v
  exact repaired_yukawa_covariance a _ v

theorem native_coefficient_commute (a : SU7MotherLieMatrix) (mu : Fin 4) :
    nativeGaugeMatrix a*coefficientMatrix mu (actual.coframe 0)=
      coefficientMatrix mu (actual.coframe 0)*nativeGaugeMatrix a := by
  unfold nativeGaugeMatrix coefficientMatrix spinCoordinates
  simp only [LinearMap.coe_mk,AddHom.coe_mk,mul_smul_comm,smul_mul_assoc]
  congr 1
  rw [←Quantum.matrix_composition,←Quantum.matrix_composition]
  congr 1
  apply LinearMap.ext
  intro v
  exact internal_spin_commute a _ v

theorem native_matter_density_ward (a : SU7MotherLieMatrix) (p transfer : Fin 4 → ℂ) :
    nativeGaugeVertex a transfer+sourceVolume •
      (nativeFullSymbol (p+transfer)*nativeGaugeMatrix a-
        nativeGaugeMatrix a*nativeFullSymbol p)=0 := by
  have kinetic (mu : Fin 4) :
      coefficientMatrix mu (actual.coframe 0)*
          (nativeGaugeMatrix a*sourceConnection mu-sourceConnection mu*nativeGaugeMatrix a-
            transfer mu • nativeGaugeMatrix a)+
        coefficientMatrix mu (actual.coframe 0)*((p mu+transfer mu) • (1:SourceMatrix)+sourceConnection mu)*nativeGaugeMatrix a-
        nativeGaugeMatrix a*(coefficientMatrix mu (actual.coframe 0)*(p mu • (1:SourceMatrix)+sourceConnection mu))=0 := by
    rw [←mul_assoc (nativeGaugeMatrix a),native_coefficient_commute,mul_assoc]
    simp only [mul_add,add_mul,mul_sub,add_smul,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,mul_assoc]
    abel
  unfold nativeGaugeVertex nativeFullSymbol
  simp only [Pi.add_apply,add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
  rw [←smul_add]
  have sums:=Finset.sum_eq_zero (fun mu (_ : mu∈(Finset.univ:Finset (Fin 4)))=>kinetic mu)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at sums
  rw [native_scalar_orbit]
  have inside : (∑ mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*
      (nativeGaugeMatrix a*sourceConnection mu-sourceConnection mu*nativeGaugeMatrix a-transfer mu • nativeGaugeMatrix a))+
      nativeScalarOrbitMatrix a+
      ((∑ mu : Fin 4,coefficientMatrix mu (actual.coframe 0)*((p mu+transfer mu) • (1:SourceMatrix)+sourceConnection mu)*nativeGaugeMatrix a)+
      sourceScalar*nativeGaugeMatrix a-
      ((∑ mu : Fin 4,nativeGaugeMatrix a*(coefficientMatrix mu (actual.coframe 0)*(p mu • (1:SourceMatrix)+sourceConnection mu)))+
      (nativeScalarOrbitMatrix a+sourceScalar*nativeGaugeMatrix a)))=0 := by
    calc
      _ = _ := by abel
      _ = 0 := sums
  simpa only [mul_add,add_mul,smul_zero] using congrArg (fun M:SourceMatrix=>sourceVolume • M) inside


open CanonicalGradedSpatialKernel CanonicalGradedSpatialSource CanonicalGradedMixedSource
open CanonicalGradedMixed PreparationVacuumActualPreparedMixed
open GaussUnitaryHistory (Index HistorySpace sourceFilter)

-- This is the source's scalar/gauge restriction; geometry remains in sourceField.
def fieldCurrent (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (mu : Fin 4) : NativeCurrent :=
  ⟨phi,Fin.cases .temporal .spatial mu,fieldGauge f mu⟩

def fieldBand (f : Field289) (phi : CanonicalGradedSpatial.Localizer) : Fin 3 → Op :=
  ![(1/2:ℂ) • dualScalar (fieldScalar f),
    ∑ mu : Fin 4,current (fieldCurrent f phi mu),
    (1/2:ℂ) • rawScalar (fieldScalar f)]

theorem fieldBand_grade (f : Field289) (phi : CanonicalGradedSpatial.Localizer) (i : Fin 3) :
    Homogeneous (fieldBand f phi i) (bandGrade i) := by
  fin_cases i
  · exact homogeneous_smul _ _ (dualScalar_lowers (fieldScalar f)) _
  · change Homogeneous (∑ mu : Fin 4,current (fieldCurrent f phi mu)) 0
    have generated (mu : Fin 4):=localGauge_grade (fieldCurrent f phi mu)
    simp only [Homogeneous,Int.cast_zero] at generated ⊢
    simp only [Finset.mul_sum,Finset.sum_mul,generated]
    apply ContinuousLinearMap.ext
    intro x
    simp
  · exact homogeneous_smul _ _ (rawScalar_raises (fieldScalar f)) _

def fieldReader (f : Field289) (phi : CanonicalGradedSpatial.Localizer) : Op := ∑ i,fieldBand f phi i

theorem fieldReader_source (f : Field289) (phi : CanonicalGradedSpatial.Localizer) :
    fieldReader f phi=(∑ mu : Fin 4,current (fieldCurrent f phi mu))+realPartScalar (fieldScalar f) := by
  simp only [fieldReader,fieldBand,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,realPartScalar,smul_add]
  abel

theorem source_field_paths (cut : ℕ) (f g : Field289) (phi psi : CanonicalGradedSpatial.Localizer)
    (out middle input : PhysicalMomentum) (r s t : ℝ) (F : GaussUnitaryHistory.Index) :
    fullWord cut (fieldReader f phi) (fieldReader g psi) out middle input r s t F=
      ∑ i : Fin 3,∑ j : Fin 3,selectedWord cut (fieldBand f phi i) (fieldBand g psi j)
        (bandGrade i) (bandGrade j) out middle input r s t F := by
  have split : fullWord cut (fieldReader f phi) (fieldReader g psi) out middle input r s t F=
      ∑ i : Fin 3,∑ j : Fin 3,fullWord cut (fieldBand f phi i) (fieldBand g psi j)
        out middle input r s t F := by
    simp only [fieldReader,PreparationVacuumActualPreparedMixed.fullWord,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [split]
  exact Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>
    fullWord_selected cut _ _ _ _ (fieldBand_grade f phi i) (fieldBand_grade g psi j)
      (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F))

def fieldBandFamily (cut : ℕ) (f g : Field289) (phi psi : CanonicalGradedSpatial.Localizer)
    (i j : Fin 3) (out middle input : PhysicalMomentum) (r s t : ℝ) :
    SourceFamilyOperator.Operator GaussUnitaryHistory.Index GaussCoreHilbert.H where
  component F := fullWord cut (fieldBand f phi i) (fieldBand g psi j) out middle input r s t F
  bounded := ⟨‖fieldBand f phi i‖*‖fieldBand g psi j‖*
      CanonicalGradedMixedReturn.pathBound cut (bandGrade i) (bandGrade j) r s t,
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (CanonicalGradedMixedReturn.pathBound_nonnegative cut (bandGrade i) (bandGrade j) r s t),
    fun F x=>by
      have bound:=selectedWord_bound cut (fieldBand f phi i) (fieldBand g psi j)
        (bandGrade i) (bandGrade j) out middle input r s t F
      rw [←fullWord_selected cut _ _ _ _ (fieldBand_grade f phi i) (fieldBand_grade g psi j)
        (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F] at bound
      exact ((fullWord cut _ _ out middle input r s t F).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right bound (norm_nonneg x))⟩

def completedFieldBandWord (cut : ℕ) (f g : Field289) (phi psi : CanonicalGradedSpatial.Localizer)
    (i j : Fin 3) (out middle input : PhysicalMomentum) (r s t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  SourceFamilyOperator.lift sourceFilter (fieldBandFamily cut f g phi psi i j out middle input r s t)



theorem completedFieldBandWord_bound (cut : ℕ) (f g : Field289)
    (phi psi : CanonicalGradedSpatial.Localizer) (i j : Fin 3)
    (out middle input : PhysicalMomentum) (r s t : ℝ) :
    ‖completedFieldBandWord cut f g phi psi i j out middle input r s t‖≤
      ‖fieldBand f phi i‖*‖fieldBand g psi j‖*
        CanonicalGradedMixedReturn.pathBound cut (bandGrade i) (bandGrade j) r s t := by
  apply CanonicalGradedVariation.lift_bound sourceFilter
    (fieldBandFamily cut f g phi psi i j out middle input r s t) _
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (CanonicalGradedMixedReturn.pathBound_nonnegative cut (bandGrade i) (bandGrade j) r s t))
  intro F
  change ‖PreparationVacuumActualPreparedMixed.fullWord cut _ _ out middle input r s t F‖≤_
  rw [fullWord_selected cut _ _ _ _ (fieldBand_grade f phi i) (fieldBand_grade g psi j)
    (bandGrade_lower i) (bandGrade_lower j) out middle input r s t F]
  exact selectedWord_bound cut _ _ _ _ out middle input r s t F


end LowEnergy.PreparationVacuumMixedFieldReturn
