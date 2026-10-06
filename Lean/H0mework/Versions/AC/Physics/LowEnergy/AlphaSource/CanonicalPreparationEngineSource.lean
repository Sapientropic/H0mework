import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationMoyalSourceLeaves
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalActualN0

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineSource
open PreparationVacuumCanonicalMoyal PreparationVacuumTemporalOrdering
open PreparationActualFactor PreparationVacuumEnergyTail PreparationVacuumLowerLeaves
open PreparationScalarCoordinates CanonicalPreparationSquareCutoff CanonicalPreparationCutoff
open PreparationPhaseSource
open PreparationVacuumWeyl
open SourceQuantumGaugeSliceCoordinates GaussNativeEnergy
open scoped BigOperators

abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def sourceClock (zp : Phase) : ℝ := C (nativePhase zp).1 (nativePhase zp).2
def sourceTrace (zp : Phase) : ℝ := T (nativePhase zp).1 (nativePhase zp).2

-- This is Engine.source's literal degree2/1/0 filtration, including its
-- original addition of the Y slot into source slot0 and zero padding above2.
def engineSource (filtration : ℕ) (slot : Fin 13) : Symbol := fun zp =>
  match filtration with
  | 0 => originalEnginePrincipalLeaves (nativePhase zp).1 (nativePhase zp).2 slot
  | 1 => originalLeaf 1 (Fin.castSucc slot) zp
  | 2 => originalLeaf 0 (Fin.castSucc slot) zp+
      if slot=0 then originalLeaf 0 (Fin.last 13) zp else 0
  | _ => 0

def engineTrace (filtration : ℕ) : Symbol := fun zp =>
  engineSource filtration 4 zp+engineSource filtration 5 zp+engineSource filtration 6 zp

theorem engineSource_first (slot : Fin 13) :
    engineSource 1 slot=originalLeaf 1 (Fin.castSucc slot) := rfl

theorem engineSource_zero (slot : Fin 13) :
    engineSource 2 slot=originalLeaf 0 (Fin.castSucc slot) := by
  funext zp
  simp only [engineSource,originalLeaf_Y_zero,ite_self,add_zero]

theorem engineSource_padding (k : ℕ) (slot : Fin 13) : engineSource (k+3) slot=fun _ => 0 := rfl

theorem engineSource_principal (slot : Fin 13) (zp : Phase)
    (position : zp.1∈thetaPositionClosed)
    (direction : normalizedMomentum zp.2∈thetaDirectionClosed) (nonzero : zp.2≠0) :
    engineSource 0 slot zp=originalLeaf 2 (Fin.castSucc slot) zp := by
  have equal := originalEnginePrincipalLeaves_native zp position direction nonzero
  rw [originalLeaf_principal]
  exact congrArg (fun v : Fin 13 → ℝ => v slot) equal

theorem engineTrace_principal (zp : Phase) : engineTrace 0 zp=sourceTrace zp := by
  change S (nativePhase zp).1 (nativePhase zp).2 0 0+
    S (nativePhase zp).1 (nativePhase zp).2 1 1+
    (T (nativePhase zp).1 (nativePhase zp).2-S (nativePhase zp).1 (nativePhase zp).2 0 0-
      S (nativePhase zp).1 (nativePhase zp).2 1 1)=T (nativePhase zp).1 (nativePhase zp).2
  ring

theorem engineTrace_first : engineTrace 1=fun _ => 0 := by
  funext zp
  simp [engineTrace,engineSource,originalLeaf_first,originalFirstLeaves]

def engineLeadingEnergy (zp : Phase) : ℝ :=
  sourceClock zp*engineSource 0 0 zp+engineTrace 0 zp/(2*sourceClock zp)

theorem engineLeadingEnergy_native (zp : Phase)
    (position : zp.1∈thetaPositionClosed)
    (direction : normalizedMomentum zp.2∈thetaDirectionClosed) (nonzero : zp.2≠0) :
    engineLeadingEnergy zp=timelikePrincipal (nativePhase zp).1 (nativePhase zp).2 (sourceClock zp) 0 := by
  have cone := source_support_positiveCone zp.1 zp.2 position direction nonzero
  have clockNonzero : sourceClock zp≠0 := (C_positive cone).ne'
  rw [engineLeadingEnergy,engineTrace_principal,engineSource_principal 0 zp position direction nonzero,
    originalLeaf_principal,zero_shift_principal _ _ _ clockNonzero]
  rfl

def engineLeadingLocalizedEnergy (zp : Phase) : ℝ :=
  sourceTheta zp.1 (normalizedMomentum zp.2)*sourceChi (2*‖zp.2‖)*engineLeadingEnergy zp

theorem engineLeadingLocalizedEnergy_b1_square (zp : Phase) :
    engineLeadingLocalizedEnergy zp=b1 zp^2 := by
  rw [←originalLeadingEnergy_b1_square]
  by_cases zero : zp.2=0
  · simp [engineLeadingLocalizedEnergy,originalLeadingEnergy,zero,sourceChi]
  · by_cases position : zp.1∈thetaPositionClosed
    · by_cases direction : normalizedMomentum zp.2∈thetaDirectionClosed
      · rw [engineLeadingLocalizedEnergy,originalLeadingEnergy,
          engineLeadingEnergy_native zp position direction zero]
        rfl
      · simp only [engineLeadingLocalizedEnergy,originalLeadingEnergy,
          sourceTheta_zero_direction direction,zero_mul]
    · simp only [engineLeadingLocalizedEnergy,originalLeadingEnergy,
        sourceTheta_zero_position position,zero_mul]

theorem engineZeroSource_wholeFunction (slot : Fin 13) (zp : Phase) :
    engineSource 2 slot zp=originalZeroLeaves (nativePhase zp).1 (Fin.castSucc slot) := by
  rw [engineSource_zero]
  rfl

end LowEnergy.PreparationVacuumEngineSource
