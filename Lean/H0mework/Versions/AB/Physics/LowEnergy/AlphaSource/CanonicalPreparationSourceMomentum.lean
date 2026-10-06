import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLieBounds
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationBorelPrincipal

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhaseSource
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286GaugeConnectionVariationDensity Stage9C.Material.SpinPair
open PreparationPhaseScalar PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates
open CanonicalPreparationSquareCutoff CanonicalPreparationCutoff
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice SourceQuantumNativeDimensions GaussLiveMomentum
open scoped BigOperators

theorem original_source_covector (sigma : scalarSlice) (gamma : coordinateSlice) :
    nativeCovector sourceMomentum (0,(sigma,gamma))=
      sourceUnitMomentum 67*(gaugeRaw gamma.val 1+gaugeRaw gamma.val 15+gaugeRaw gamma.val 30) := by
  rw [nativeCovector_apply,full_blocks]
  change (∑ i : Fin 100,sourceUnitMomentum i*
    joinCoordinates (coframeCoordinates 0,read61 (scalarRealify sigma.val),gaugeFree gamma) i)=_
  simp only [map_zero]
  have original : gaugeFree gamma 0=gaugeRaw gamma.val 1 ∧
      gaugeFree gamma 13=gaugeRaw gamma.val 15 ∧
      gaugeFree gamma 27=gaugeRaw gamma.val 30 := ⟨rfl,rfl,rfl⟩
  simp [Fin.sum_univ_succ,sourceUnitMomentum,joinCoordinates]
  rw [original.1,original.2.1,original.2.2]
  ring

theorem original_color_bracket_rows (a : NativeLie) :
    rawCoordinates (jointP286CoordinateLieBracket a (colorGenerator 0)) 1=0 ∧
    rawCoordinates (jointP286CoordinateLieBracket a (colorGenerator 1)) 3=
      -(rawCoordinates a 5)/2 ∧
    rawCoordinates (jointP286CoordinateLieBracket a (colorGenerator 2)) 6=0 := by
  obtain ⟨x,rfl⟩:=rawCoordinates.symm.surjective a
  rw [actual_raw_block_decode]
  unfold jointP286CoordinateLieBracket colorGenerator
  simp only [p286CoordinateEquiv.symm_apply_apply]
  change rawRead (p286CoordinateEquiv (p286LieBracket (actualRawBlock x) (sourceColorP286Generator 0))) 1=0 ∧
    rawRead (p286CoordinateEquiv (p286LieBracket (actualRawBlock x) (sourceColorP286Generator 1))) 3=
      -(rawRead (p286CoordinateEquiv (actualRawBlock x)) 5)/2 ∧
    rawRead (p286CoordinateEquiv (p286LieBracket (actualRawBlock x) (sourceColorP286Generator 2))) 6=0
  unfold rawRead
  simp only [nativeCoordinates_apply]
  constructor
  · norm_num [p286LieBracket,suLieBracket,sourceColorP286Generator_color,
      sourceColorP286Generator_weak_zero,sourceColorP286Generator_hypercharge_zero,
      sourceColorRaw,actualRawBlock,Matrix.mul_apply,Fin.sum_univ_three]
  constructor
  · norm_num [p286LieBracket,suLieBracket,sourceColorP286Generator_color,
      sourceColorP286Generator_weak_zero,sourceColorP286Generator_hypercharge_zero,
      sourceColorRaw,actualRawBlock,Matrix.mul_apply,Fin.sum_univ_three]
    all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals norm_num
    all_goals ring
  · norm_num [p286LieBracket,suLieBracket,sourceColorP286Generator_color,
      sourceColorP286Generator_weak_zero,sourceColorP286Generator_hypercharge_zero,
      sourceColorRaw,actualRawBlock,Matrix.mul_apply,Fin.sum_univ_three]
    all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals norm_num


theorem original_source_gauge_bracket (a : NativeLie) :
    gaugeRaw (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 1=0 ∧
    gaugeRaw (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 15=
      -gaugeScale/2*(nativeCoordinates a).1 5 ∧
    gaugeRaw (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 30=0 := by
  have columns (i : Fin 3) : gaugeCoordinates (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) i=
      gaugeScale • jointP286CoordinateLieBracket a (colorGenerator i) := by
    change jointP286CoordinateLieBracket a (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge i)=_
    rw [sourceGauge_apply,jointP286CoordinateLieBracket_smul_right]
  have rows:=original_color_bracket_rows a
  change rawCoordinates (gaugeCoordinates (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 0) 1=0 ∧
    rawCoordinates (gaugeCoordinates (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 1) 3=_ ∧
    rawCoordinates (gaugeCoordinates (nativeGauge a SourceQuantumResidualGaugeSlice.sourceGauge) 2) 6=0
  simp only [columns,map_smul,Pi.smul_apply,smul_eq_mul]
  rw [rows.1,rows.2.1,rows.2.2]
  change gaugeScale*0=0 ∧ gaugeScale*(-((nativeCoordinates a).1 5)/2)=_ ∧ gaugeScale*0=0
  constructor
  · ring
  constructor <;> ring

end LowEnergy.PreparationPhaseSource
