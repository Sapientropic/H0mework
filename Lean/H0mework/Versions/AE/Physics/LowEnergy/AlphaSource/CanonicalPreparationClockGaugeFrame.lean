import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceMomentum
import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricFloor

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumClockPole
open SaturationMonoid.PhysicsCore
open StageNineP286GaugeAuxiliaryVariation StageNineGlobalIntegratedAction StageNineHyperchargeAuxiliaryVariation
open PreparationActualFactor
open PreparationPhaseSource PreparationPhaseScalar PreparationPhaseGuard PreparationPhaseBounds
open PreparationCoordinates PreparationScalarCoordinates PreparationChartGuard
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumScalarChart SourceQuantumNativeDimensions
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential GaussLiveMomentum GaussHistoryHilbert
open scoped BigOperators Matrix

def frameColor (j : Fin 2) : Fin 12 := ![1,3] j

def frameFree (i : Fin 3) (j : Fin 2) : Fin 33 :=
  ![![0,2],![11,13],![22,24]] i j

def frameLie (j : Fin 2) : NativeLie := rawCoordinates.symm (Pi.single (frameColor j) 1)

def frameGauge (i : Fin 3) (j : Fin 2) : coordinateSlice :=
  gaugeFree.symm (Pi.single (frameFree i j) 1)

theorem frameGauge_native (i : Fin 3) (j : Fin 2) (k : Fin 3) :
    gaugeCoordinates (frameGauge i j).val k=if k=i then frameLie j else 0 := by
  change rawCoordinates.symm
    (fun a => insertFree (Pi.single (frameFree i j) 1) (combinedRow k a))=_
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals apply rawCoordinates.injective
  all_goals ext a
  all_goals fin_cases a
  all_goals norm_num [frameFree,frameLie,frameColor,
    insertFree,combinedRow,Pi.single_apply,Fin.ext_iff]

theorem frameLie_norm (j : Fin 2) : ‖frameLie j‖^2=(2 : ℝ) := by
  rw [←real_inner_self_eq_norm_sq]
  change p286CoordinateLiePairing (frameLie j) (frameLie j)=2
  unfold frameLie
  rw [actual_raw_block_decode]
  unfold p286CoordinateLiePairing
  simp only [LinearEquiv.symm_apply_apply]
  fin_cases j
  all_goals norm_num [frameColor,p286LiePairing,specialUnitaryLiePairing_self_eq_sum_normSq,
    hyperchargeLiePairing_eq_coordinate_mul,actualRawBlock,Pi.single_apply,Fin.ext_iff,
    Fin.sum_univ_succ]

theorem frameLie_coefficients (j : Fin 2) :
    (∑ a : LieIndex,(lieBasis.repr (frameLie j) a)^2)=2 := by
  rw [←EuclideanSpace.real_norm_sq_eq,LinearIsometryEquiv.norm_map]
  exact frameLie_norm j

theorem gaugeTest_coordinates (d : Fin 33) :
    fullCoordinates (0,(0,gaugeFree.symm (Pi.single d 1)))=
      Pi.single (PreparationPhaseScalar.gaugeSlot d) 1 := by
  have scalarZero : read61 (0 : Fin 70 → ℝ)=0 := by
    ext a
    fin_cases a <;> simp [read61]
  rw [full_blocks]
  simp only [map_zero,LinearEquiv.apply_symm_apply]
  ext k
  by_cases first : k.val<6
  · have different : k≠PreparationPhaseScalar.gaugeSlot d := by
      intro h
      have same := congrArg Fin.val h
      unfold PreparationPhaseScalar.gaugeSlot at same
      simp only at same
      omega
    simp [joinCoordinates,first,different]
  · by_cases middle : k.val<67
    · have different : k≠PreparationPhaseScalar.gaugeSlot d := by
        intro h
        have same := congrArg Fin.val h
        unfold PreparationPhaseScalar.gaugeSlot at same
        simp only at same
        omega
      simp [joinCoordinates,first,middle,different,scalarZero]
    · have indices : (⟨k.val-67,by omega⟩ : Fin 33)=d ↔
          k=PreparationPhaseScalar.gaugeSlot d := by
        simp only [Fin.ext_iff,PreparationPhaseScalar.gaugeSlot]
        omega
      simp only [joinCoordinates,dif_neg first,dif_neg middle,Pi.single_apply,indices]

theorem frameGauge_momentum (z : physicalChart) (u : FlatConfiguration)
    (i : Fin 3) (j : Fin 2) :
    ambientMomentum z.val (nativeCovector (WithLp.toLp 2 u)) (0,(frameGauge i j).val)=
      u (PreparationPhaseScalar.gaugeSlot (frameFree i j)) := by
  have splice : ((0,(frameGauge i j).val) : Ambient)=splitMap z.val (0,(0,frameGauge i j)) := by
    simp [splitMap,sliceMap]
  change nativeCovector (WithLp.toLp 2 u) (direction (0,(frameGauge i j).val) z.val)=_
  rw [splice]
  simp only [direction,inverse_left]
  rw [nativeCovector_apply]
  unfold frameGauge
  rw [gaugeTest_coordinates]
  simp [Pi.single_apply]

theorem frameGauge_electric (z : physicalChart) (p : Cotangent) (i : Fin 3) (j : Fin 2) :
    ambientMomentum z.val p (0,(frameGauge i j).val)=
      ∑ a : LieIndex,lieBasis.repr (frameLie j) a*electricMomentum z.val p i a := by
  rw [original_gauge_decomposition,map_sum]
  simp only [map_sum,map_smul,smul_eq_mul]
  change (∑ k : Fin 3,∑ a : LieIndex,
    lieBasis.repr (gaugeCoordinates (frameGauge i j).val k) a*electricMomentum z.val p k a)=_
  fin_cases i <;> simp [frameGauge_native,Fin.sum_univ_three]

end LowEnergy.PreparationVacuumClockPole
