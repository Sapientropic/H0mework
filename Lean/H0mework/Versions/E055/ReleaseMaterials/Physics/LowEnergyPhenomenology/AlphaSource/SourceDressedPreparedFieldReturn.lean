import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceDressedGTCharacter
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeVertexCore
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldPreparedCovector

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalDressedSpinChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite GaussComposite.SourceGraph Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open scoped BigOperators ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FiberOp:=NormedAlgebra.restrictScalars ℝ ℂ _

private def gtWeight : Mode→ℂ
  | .inl i=>(sourceFirstWholeWeight i:ℂ)*Complex.I
  | .inr i=> -(sourceFirstWholeWeight i:ℂ)*Complex.I

private theorem gt_diagonal : sourceFirstBackgroundFullGenerator=Matrix.diagonal gtWeight := by
  unfold sourceFirstBackgroundFullGenerator
  rw [←sourceFirstTemporal_native,sourceFirstTemporal_matrix]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.diagonal_apply,gtWeight]

private theorem gt_create (spin : Fin 2) (c : Fin 3) :
    quantized sourceFirstBackgroundFullGenerator*GaussCARHistory.createFiber (mode spin c)-
      GaussCARHistory.createFiber (mode spin c)*quantized sourceFirstBackgroundFullGenerator=
    ((sourceFirstExteriorWeight (Composite.matterBasis c):ℂ)*Complex.I) •
      GaussCARHistory.createFiber (mode spin c) := by
  rw [quantized_creation_column,gt_diagonal]
  unfold creationColumn
  rw [Finset.sum_eq_single (mode spin c)]
  · rw [Matrix.diagonal_apply,if_pos rfl]
    rfl
  · intro j _ different
    rw [Matrix.diagonal_apply,if_neg different]
    exact _root_.zero_smul ℂ (GaussCARHistory.createFiber j)
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

private theorem gt_annihilate (spin : Fin 2) (c : Fin 3) :
    quantized sourceFirstBackgroundFullGenerator*GaussCARHistory.annihilateFiber (mode spin c)-
      GaussCARHistory.annihilateFiber (mode spin c)*quantized sourceFirstBackgroundFullGenerator=
    -(((sourceFirstExteriorWeight (Composite.matterBasis c):ℂ)*Complex.I) •
      GaussCARHistory.annihilateFiber (mode spin c)) := by
  rw [quantized_annihilation_row,gt_diagonal]
  unfold annihilationRow
  rw [Finset.sum_eq_single (mode spin c)]
  · rw [Matrix.diagonal_apply,if_pos rfl]
    rfl
  · intro j _ different
    rw [Matrix.diagonal_apply,if_neg (Ne.symm different)]
    exact _root_.zero_smul ℂ (GaussCARHistory.annihilateFiber j)
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

private theorem weight_complex (a : Fin 2) (c : Fin 3) :
    (sourceFirstExteriorWeight (Composite.scalarBasis a c):ℂ)+
      (sourceFirstExteriorWeight (Composite.matterBasis c):ℂ)=(5/11:ℂ) := by
  have h:=congrArg (fun q : ℚ=>(q:ℂ)) (sourceDressedGT_weight a c)
  norm_num only [Rat.cast_add,Rat.cast_div] at h
  exact h

/-- The material commutator is subtracted from the scalar variation, without changing the input state. -/
theorem sourceDressed_creation (a s : Fin 2) (phi : Scalar) :
    fiberCreation a s (scalarMotherLieAction sourceFirstTemporalMother phi)-
      (quantized sourceFirstBackgroundFullGenerator*fiberCreation a s phi-
        fiberCreation a s phi*quantized sourceFirstBackgroundFullGenerator)=
      (-((5/11:ℂ)*Complex.I)) • fiberCreation a s phi := by
  simp only [fiberCreation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,sourceDressedGT_scalar,map_mul,
    Complex.star_def,Complex.conj_I,map_ratCast,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro c _
  rw [←_root_.smul_sub ((starRingEnd ℂ) (scalarCoefficient a c phi))
    (quantized sourceFirstBackgroundFullGenerator*GaussCARHistory.createFiber (mode s c))
    (GaussCARHistory.createFiber (mode s c)*quantized sourceFirstBackgroundFullGenerator),gt_create,
    smul_smul]
  rw [←_root_.sub_smul _ _ (GaussCARHistory.createFiber (mode s c))]
  congr 1
  linear_combination (-Complex.I*(starRingEnd ℂ) (scalarCoefficient a c phi))*weight_complex a c

theorem sourceDressed_annihilation (a s : Fin 2) (phi : Scalar) :
    fiberAnnihilation a s (scalarMotherLieAction sourceFirstTemporalMother phi)-
      (quantized sourceFirstBackgroundFullGenerator*fiberAnnihilation a s phi-
        fiberAnnihilation a s phi*quantized sourceFirstBackgroundFullGenerator)=
      ((5/11:ℂ)*Complex.I) • fiberAnnihilation a s phi := by
  simp only [fiberAnnihilation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    ←Finset.sum_sub_distrib,sourceDressedGT_scalar,
    Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro c _
  rw [←_root_.smul_sub (scalarCoefficient a c phi)
    (quantized sourceFirstBackgroundFullGenerator*GaussCARHistory.annihilateFiber (mode s c))
    (GaussCARHistory.annihilateFiber (mode s c)*quantized sourceFirstBackgroundFullGenerator),gt_annihilate,
    smul_neg,smul_smul,sub_neg_eq_add]
  rw [←_root_.add_smul _ _ (GaussCARHistory.annihilateFiber (mode s c))]
  congr 1
  linear_combination (Complex.I*scalarCoefficient a c phi)*weight_complex a c

/-- The two opposite CAR letters carry opposite joint variations. -/
def sourceDressedCharacter (addition : Bool) : ℂ :=
  if addition then -((5/11:ℂ)*Complex.I) else ((5/11:ℂ)*Complex.I)

def sourceDressedFiber (addition : Bool) (a s : Fin 2) (phi : Scalar) : FiberOp :=
  if addition then
    fiberCreation a s (scalarMotherLieAction sourceFirstTemporalMother phi)-
      (quantized sourceFirstBackgroundFullGenerator*fiberCreation a s phi-
        fiberCreation a s phi*quantized sourceFirstBackgroundFullGenerator)
  else
    fiberAnnihilation a s (scalarMotherLieAction sourceFirstTemporalMother phi)-
      (quantized sourceFirstBackgroundFullGenerator*fiberAnnihilation a s phi-
        fiberAnnihilation a s phi*quantized sourceFirstBackgroundFullGenerator)

private theorem fiber_return (addition : Bool) (a s : Fin 2) (phi : Scalar) :
    sourceDressedFiber addition a s phi=sourceDressedCharacter addition •
      (if addition then fiberCreation a s phi else fiberAnnihilation a s phi) := by
  cases addition
  · exact sourceDressed_annihilation a s phi
  · exact sourceDressed_creation a s phi

def sourceDressedTest (addition : Bool) (a s : Fin 2) : QuantumTest→ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z=>
    (if addition then (rootVolume z:ℂ)⁻¹ else (rootVolume z:ℂ)) •
      sourceDressedFiber addition a s (GaussNativePotential.scalarField z)) (by
    intro z
    simp only [fiber_return]
    cases addition
    · simp only [Bool.false_eq_true,if_false]
      exact (root_volume_complex_smooth z).smul
        (((annihilation_matrix_smooth a s).contDiffAt).const_smul _)
    · simp only [if_true]
      exact ((root_volume_complex_smooth z).inv
        (Complex.ofReal_ne_zero.mpr (root_volume_pos z).ne')).smul
          (((creation_matrix_smooth a s).contDiffAt).const_smul _))

/-- The original input action remains inside the CAR commutator; the source measure and volume factors are unchanged. -/
theorem sourceDressedTest_return (addition : Bool) (a s : Fin 2) (f : QuantumTest) :
    sourceDressedTest addition a s f=sourceDressedCharacter addition •
      (if addition then creationTest a s f else annihilationTest a s f) := by
  apply DFunLike.ext
  intro z
  cases addition
  · change (rootVolume z:ℂ) •
        (sourceDressedFiber false a s (GaussNativePotential.scalarField z) (f z))=
      sourceDressedCharacter false • ((rootVolume z:ℂ) •
        (fiberAnnihilation a s (GaussNativePotential.scalarField z) (f z)))
    rw [fiber_return]
    exact smul_comm (rootVolume z:ℂ) (sourceDressedCharacter false)
      (fiberAnnihilation a s (GaussNativePotential.scalarField z) (f z))
  · change (rootVolume z:ℂ)⁻¹ •
        (sourceDressedFiber true a s (GaussNativePotential.scalarField z) (f z))=
      sourceDressedCharacter true • ((rootVolume z:ℂ)⁻¹ •
        (fiberCreation a s (GaussNativePotential.scalarField z) (f z)))
    rw [fiber_return]
    exact smul_comm (rootVolume z:ℂ)⁻¹ (sourceDressedCharacter true)
      (fiberCreation a s (GaussNativePotential.scalarField z) (f z))

def sourceDressedLetter (addition : Bool) (a s : Fin 2) : QuantumTest→ₗ[ℂ] H :=
  embed.comp (sourceDressedTest addition a s)

theorem sourceDressedLetter_return (addition : Bool) (a s : Fin 2) :
    sourceDressedLetter addition a s=sourceDressedCharacter addition • leg addition a s := by
  apply LinearMap.ext
  intro f
  simp only [sourceDressedLetter,LinearMap.comp_apply,sourceDressedTest_return,map_smul,
    LinearMap.smul_apply]
  cases addition <;> simp only [Bool.false_eq_true,if_false,if_true,leg,
    embed_creation_test,embed_annihilation_test]

def sourceDressedCore (addition : Bool) (a s : Fin 2) : ScalarTest→ₗ[ℂ] H :=
  (sourceDressedLetter addition a s).comp seedSection

theorem sourceDressedCore_return (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    sourceDressedCore addition a s f=sourceDressedCharacter addition • legCore addition a s f := by
  rw [sourceDressedCore,sourceDressedLetter_return]
  rfl

private theorem dressed_bound (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    ‖sourceDressedCore addition a s f‖≤
      (‖sourceDressedCharacter addition‖*legBound)*‖core f‖ := by
  rw [sourceDressedCore_return,norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (legCore_bound addition a s f) (norm_nonneg _)

def sourceDressedCompleted (addition : Bool) (a s : Fin 2) : Profile→L[ℂ] H :=
  (sourceDressedCore addition a s).extendOfNorm core

theorem sourceDressedCompleted_core (addition : Bool) (a s : Fin 2) (f : ScalarTest) :
    sourceDressedCompleted addition a s (core f)=sourceDressedCore addition a s f :=
  LinearMap.extendOfNorm_eq core_dense ⟨_,dressed_bound addition a s⟩ f

theorem sourceDressedCompleted_return (addition : Bool) (a s : Fin 2) (f : Profile) :
    sourceDressedCompleted addition a s f=
      sourceDressedCharacter addition • completedLeg addition a s f := by
  have equality : sourceDressedCompleted addition a s=
      sourceDressedCharacter addition • completedLeg addition a s := by
    apply LinearMap.extendOfNorm_unique core_dense _ (dressed_bound addition a s)
    apply LinearMap.ext
    intro g
    simp only [LinearMap.comp_apply,FunLike.coe_smul,Pi.smul_apply,
      ContinuousLinearMap.coe_coe,completedLeg_core,sourceDressedCore_return,legCore]
  exact congrArg (fun T : Profile→L[ℂ] H=>T f) equality

/-- The source-generated profile is inserted at both independent Green endpoints. -/
def sourceDressedPreparedCovector (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) : Fin 289→ℂ :=
  fun i=>
    inner ℂ (sourceDressedCompleted left a s (sourceProfile epsilon precision))
      (currentVertex (fieldBasis i) p k F n z w
        (completedLeg right b t (sourceProfile epsilon precision)))+
    inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
      (currentVertex (fieldBasis i) p k F n z w
        (sourceDressedCompleted right b t (sourceProfile epsilon precision)))

theorem sourceDressedPrepared_return (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    sourceDressedPreparedCovector epsilon precision p k F n z w left right a s b t=
      fun i=>(star (sourceDressedCharacter left)+sourceDressedCharacter right)*
        preparedCovector epsilon precision p k F n z w left right a s b t i := by
  funext i
  simp only [sourceDressedPreparedCovector,sourceDressedCompleted_return,
    inner_smul_left,map_smul,inner_smul_right,preparedCovector,preparedCurrent,add_mul,starRingEnd_apply]

/-- The full 289-field source, including scalar, complement and density terms, is the actual consumer. -/
theorem sourceDressedPrepared_source (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (left right : Bool) (a s b t : Fin 2) :
    sourceDressedPreparedCovector epsilon precision p k F n z w left right a s b t=
      fun i=>(star (sourceDressedCharacter left)+sourceDressedCharacter right)*
        sourceCovector p
          (sourceTestApprox F ((finiteFull (p+k) F n z).adjoint
            (completedLeg left a s (sourceProfile epsilon precision))))
          (sourceTestApprox F (finiteFull p F n w
            (completedLeg right b t (sourceProfile epsilon precision)))) i := by
  rw [sourceDressedPrepared_return,prepared_covector_source]

theorem sourceDressedPrepared_price (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (n : ℕ) (z w : ℂ) (hz : z.im≠0) (hw : w.im≠0)
    (left right : Bool) (a s b t : Fin 2) (i : Fin 289) :
    ‖sourceDressedPreparedCovector epsilon precision p k F n z w left right a s b t i‖≤
      ‖star (sourceDressedCharacter left)+sourceDressedCharacter right‖*
      (‖completedLeg left a s (sourceProfile epsilon precision)‖*
        (normBound n z*currentPrice (fieldBasis i) p F*normBound n w)*
        ‖completedLeg right b t (sourceProfile epsilon precision)‖) := by
  rw [sourceDressedPrepared_return,norm_mul]
  exact mul_le_mul_of_nonneg_left
    (prepared_covector_price epsilon precision p k F n z w hz hw left right a s b t i) (norm_nonneg _)

end LowEnergy.PreparationPhysicalDressedSpinChargeReturn
