import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationGaugeCoordinates
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGaugeMeasure

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationCoordinates
open SaturationMonoid.PhysicsCore
open Stage9C.Material.SpinPair
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice
open SourceQuantumConfigurationHilbert
open scoped RealInnerProductSpace

def sourceSlice : coordinateSlice :=
  ⟨SourceQuantumConfigurationHilbert.sourceGauge, sourceGauge_mem_coordinateSlice⟩

def sourceGauge33 (i : Fin 33) : ℝ :=
  if i=0 ∨ i=10 ∨ i=27 then gaugeScale/2 else if i=28 then -gaugeScale/2 else 0

theorem source_gauge_scale : gaugeScale/2=3*Real.sqrt 2/10 := by
  unfold gaugeScale spinScale
  ring

theorem source_gauge_read : gaugeFree sourceSlice=sourceGauge33 := by
  change (fun i => rawRead (gaugeCoordinates SourceQuantumResidualGaugeSlice.sourceGauge
    (spatialRow (freeRow i))) (nativeRow (freeRow i))) = sourceGauge33
  ext i
  fin_cases i <;> simp [freeRow,spatialRow,nativeRow,rawRead,sourceGauge_apply,map_smul,
    colorGenerator_coordinates,sourceGauge33,div_eq_mul_inv]

def coframeCoordinates : Coframe ≃L[ℝ] (Fin 6 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toContinuousLinearEquiv

def partialCoordinates : SourceCoordinateSlice ≃L[ℝ]
    ((Fin 6 → ℝ) × scalarSlice × (Fin 33 → ℝ)) :=
  coframeCoordinates.prodCongr ((ContinuousLinearEquiv.refl ℝ scalarSlice).prodCongr gaugeFreeContinuous)

theorem actual_sourcePoint : partialCoordinates GaussHistoryHilbert.sourcePoint.val =
    (![1,0,1,0,0,1],0,sourceGauge33) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact source_gauge_read

theorem raw_native_cartan (x : Fin 33 → ℝ) :
    (nativeCoordinates (gaugeCoordinates (gaugeFree.symm x).val 2)).1 6=x 27 ∧
    (nativeCoordinates (gaugeCoordinates (gaugeFree.symm x).val 2)).1 7=x 27+x 28 := by
  have sixth := congrFun (decode_original_rows x) 30
  have seventh := congrFun (decode_original_rows x) 31
  change (nativeCoordinates (gaugeCoordinates (gaugeFree.symm x).val 2)).1 6=x 27 at sixth
  change (nativeCoordinates (gaugeCoordinates (gaugeFree.symm x).val 2)).1 7-
    (nativeCoordinates (gaugeCoordinates (gaugeFree.symm x).val 2)).1 6=x 28 at seventh
  exact ⟨sixth, by linarith⟩

def displaced : Fin 33 → ℝ := fun i =>
  sourceGauge33 i + if i=0 then 1/1000 else if i=10 then 1/2000 else if i=28 then 1/37 else 0

theorem displaced_roundtrip : gaugeFree (gaugeFree.symm displaced)=displaced :=
  gaugeFree.apply_symm_apply _

theorem displaced_cartan :
    (nativeCoordinates (gaugeCoordinates (gaugeFree.symm displaced).val 2)).1 7=1/37 := by
  rw [(raw_native_cartan displaced).2]
  simp [displaced,sourceGauge33]
  ring

theorem doubled_source_read : gaugeFree ((2 : ℝ) • sourceSlice) = (2 : ℝ) • sourceGauge33 := by
  rw [map_smul, source_gauge_read]

theorem original_measure_doubles_cubically (N : ℕ) :
    GaussDensityCore.density N (ActualGaugeMeasure.scale 2 GaussHistoryHilbert.sourcePoint.val) =
      8*GaussHistoryHilbert.sourceJacobian := by
  rw [ActualGaugeMeasure.source_density_scale]
  norm_num

private def cartanBlock (a b : ℝ) : SU7MotherLieAlgebra.P286LieBlockData :=
  (⟨!![(a : ℂ)*Complex.I,0,0; 0,(b : ℂ)*Complex.I,0; 0,0,-((a+b : ℝ) : ℂ)*Complex.I], by
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_apply]
    · simp [Matrix.trace,Fin.sum_univ_succ]; ring⟩,0,0)

private theorem cartan_read (a b : ℝ) :
    rawCoordinates (StageNineHolonomicField.p286CoordinateEquiv (cartanBlock a b)) =
      ![0,0,0,0,0,0,a,b,0,0,0,0] := by
  change rawRead _ = _
  unfold rawRead
  rw [nativeCoordinates_apply]
  ext i
  fin_cases i <;> simp [cartanBlock]

theorem raw_cartan_pair :
    inner ℝ (rawCoordinates.symm (Pi.single 6 1)) (rawCoordinates.symm (Pi.single 7 1))=1 := by
  have left : rawCoordinates.symm (Pi.single 6 1) =
      StageNineHolonomicField.p286CoordinateEquiv (cartanBlock 1 0) := by
    apply rawCoordinates.injective
    rw [rawCoordinates.apply_symm_apply,cartan_read]
    ext i; fin_cases i <;> simp
  have right : rawCoordinates.symm (Pi.single 7 1) =
      StageNineHolonomicField.p286CoordinateEquiv (cartanBlock 0 1) := by
    apply rawCoordinates.injective
    rw [rawCoordinates.apply_symm_apply,cartan_read]
    ext i; fin_cases i <;> simp
  rw [left,right]
  change StageNineP286GaugeAuxiliaryVariation.p286CoordinateLiePairing
    (StageNineHolonomicField.p286CoordinateEquiv (cartanBlock 1 0))
    (StageNineHolonomicField.p286CoordinateEquiv (cartanBlock 0 1))=1
  norm_num [StageNineP286GaugeAuxiliaryVariation.p286CoordinateLiePairing,
    StageNineP286GaugeAuxiliaryVariation.p286LiePairing,
    StageNineGlobalIntegratedAction.specialUnitaryLiePairing,
    StageNineGlobalIntegratedAction.hyperchargeLiePairing,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_succ,
    cartanBlock]

end LowEnergy.PreparationCoordinates
#print axioms LowEnergy.PreparationCoordinates.actual_sourcePoint
#print axioms LowEnergy.PreparationCoordinates.displaced_cartan
#print axioms LowEnergy.PreparationCoordinates.original_measure_doubles_cubically
#print axioms LowEnergy.PreparationCoordinates.raw_cartan_pair
