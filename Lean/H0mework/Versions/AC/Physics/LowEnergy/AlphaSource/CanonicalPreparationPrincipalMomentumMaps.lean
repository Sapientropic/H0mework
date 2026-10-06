import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaugeInverse
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationClockBudgetActualBounds
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeOriginal

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPrincipalBudget
open PreparationVacuumSourceMatrixInverse PreparationVacuumCentralBudget PreparationVacuumClockBudget
open PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol PreparationVacuumClockJacobian
open PreparationVacuumEngineBudget PreparationVacuumEngineSmooth
open PreparationActualFactor PreparationScalarCoordinates PreparationCoordinates
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumResidualGaugeSlice SourceQuantumNativeDimensions GaussLiveMomentum
open GaussNativeEnergy GaussNativeForm GaussCoreDifferential
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology Matrix RealInnerProductSpace

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := Phase → ℝ

/-- The actual inverseL coefficient map; the theorem below reads its literal D9/M3 formula. -/
def sourceCoefficient (z : FlatConfiguration) (v : Ambient) (k : Fin 94) : ℝ :=
  fullCoordinates (direction v (fullCoordinates.symm z)) (Fin.natAdd 6 k)

def explicitCoefficient (z : FlatConfiguration) (xi : Scalar) (eta : Gauge) (k : Fin 94) : ℝ :=
  if h : k.val<61 then
    read61 (scalarRealify (xi-action (vacuum+((fullCoordinates.symm z).2.1 : Scalar))
      (matrixLie z xi eta))) ⟨k.val,h⟩
  else gaugeRaw (eta-nativeGauge (matrixLie z xi eta) (fullCoordinates.symm z).2.2.val)
    (freeRow ⟨k.val-61,by omega⟩)

theorem actual_coefficient_matrix_formula (z : FlatConfiguration)
    (box : ∀ i,|z i-flatSource i| ≤ sourceRadius) (xi : Scalar) (eta : Gauge) (k : Fin 94) :
    sourceCoefficient z (xi,eta) k=explicitCoefficient z xi eta k := by
  have original := actual_inverseL_matrix_formula z box xi eta
  have scalar := congrArg (fun t : NativeLie × Scalar × Gauge => t.2.1) original
  have gauge := congrArg (fun t : NativeLie × Scalar × Gauge => t.2.2) original
  unfold sourceCoefficient direction
  rw [full_blocks,map_zero]
  change joinCoordinates (0,read61 (scalarRealify (inverseL (fullCoordinates.symm z) (xi,eta)).2.1.val),
    (fun j => gaugeRaw (inverseL (fullCoordinates.symm z) (xi,eta)).2.2.val (freeRow j))) (Fin.natAdd 6 k)=_
  dsimp only at scalar gauge
  rw [scalar,gauge]
  unfold explicitCoefficient joinCoordinates
  simp only [Fin.val_natAdd]
  simp only [Nat.add_sub_cancel_left,show 6+k.val-67=k.val-61 by omega]
  split_ifs <;> first | omega | rfl

theorem actual_momentum_coefficients (z : FlatConfiguration) (p : PhysicalMomentum) (v : Ambient) :
    nativeCovector p (direction v (fullCoordinates.symm z))=
      ∑ k : Fin 94,p (Fin.natAdd 6 k)*sourceCoefficient z v k := by
  rw [nativeCovector_apply]
  rw [Fin.sum_univ_add (a:=6) (b:=94)]
  have zero : ∀ k : Fin 6,fullCoordinates (direction v (fullCoordinates.symm z)) (Fin.castAdd 94 k)=0 := by
    intro k
    rw [full_blocks]
    simp [direction,joinCoordinates,k.isLt]
  simp only [zero,mul_zero,Finset.sum_const_zero,zero_add,sourceCoefficient]

def scalarCoefficients (z : FlatConfiguration) : Matrix (Fin 70) (Fin 94) ℝ :=
  fun a k => sourceCoefficient z (scalarRealify.symm (Pi.single a 1),0) k

def gaugeCoefficients (z : FlatConfiguration) : Matrix (Fin 36) (Fin 94) ℝ :=
  fun a k => sourceCoefficient z (0,gaugeRaw.symm (Pi.single a 1)) k

def rawScalarMomentum (a : Fin 70) : Symbol := fun x =>
  nativeCovector x.2 (direction (scalarRealify.symm (Pi.single a 1),0) (fullCoordinates.symm x.1))

def rawGaugeMomentum (a : Fin 36) : Symbol := fun x =>
  nativeCovector x.2 (direction (0,gaugeRaw.symm (Pi.single a 1)) (fullCoordinates.symm x.1))

theorem actual_rawScalar_momentum_matrix (x : Phase) (a : Fin 70) :
    rawScalarMomentum a x=∑ k : Fin 94,scalarCoefficients x.1 a k*x.2 (Fin.natAdd 6 k) := by
  rw [rawScalarMomentum,actual_momentum_coefficients]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem actual_rawGauge_momentum_matrix (x : Phase) (a : Fin 36) :
    rawGaugeMomentum a x=∑ k : Fin 94,gaugeCoefficients x.1 a k*x.2 (Fin.natAdd 6 k) := by
  rw [rawGaugeMomentum,actual_momentum_coefficients]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem actual_scalar_matrix_formula (z : FlatConfiguration)
    (box : ∀ i,|z i-flatSource i| ≤ sourceRadius) (a : Fin 70) (k : Fin 94) :
    scalarCoefficients z a k=explicitCoefficient z (scalarRealify.symm (Pi.single a 1)) 0 k :=
  actual_coefficient_matrix_formula z box _ _ k

theorem actual_gauge_matrix_formula (z : FlatConfiguration)
    (box : ∀ i,|z i-flatSource i| ≤ sourceRadius) (a : Fin 36) (k : Fin 94) :
    gaugeCoefficients z a k=explicitCoefficient z 0 (gaugeRaw.symm (Pi.single a 1)) k :=
  actual_coefficient_matrix_formula z box _ _ k

theorem rawScalarMomentum_smooth (a : Fin 70) : SmoothSymbol (rawScalarMomentum a) := by
  intro x hx
  exact ((nativeCovectorMap.contDiff.contDiffAt.comp x contDiffAt_snd).clm_apply
    ((direction_smooth _ ⟨_,hx.1.1⟩).comp x
      (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst))).contDiffWithinAt

theorem rawGaugeMomentum_smooth (a : Fin 36) : SmoothSymbol (rawGaugeMomentum a) := by
  intro x hx
  exact ((nativeCovectorMap.contDiff.contDiffAt.comp x contDiffAt_snd).clm_apply
    ((direction_smooth _ ⟨_,hx.1.1⟩).comp x
      (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst))).contDiffWithinAt


theorem sourceCoefficient_smooth (v : Ambient) (k : Fin 94) :
    SmoothSymbol (fun x => sourceCoefficient x.1 v k) := by
  intro x hx
  have smooth := fullCoordinates.contDiff.contDiffAt.comp x
    ((direction_smooth v ⟨_,hx.1.1⟩).comp x
      (fullCoordinates.symm.contDiff.contDiffAt.comp x contDiffAt_fst))
  exact ((ContinuousLinearMap.proj (Fin.natAdd 6 k) : (Fin 100 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp x smooth) |>.contDiffWithinAt

end LowEnergy.PreparationVacuumPrincipalBudget
