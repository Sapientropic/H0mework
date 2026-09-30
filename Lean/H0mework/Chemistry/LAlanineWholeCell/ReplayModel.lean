import H0mework.Chemistry.LAlanineWholeCell.ReplayData
import H0mework.Chemistry.LAlanineParametric.IntervalFourStep

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator WholeCellPartition SourceFields IntervalParameterMap
noncomputable section

def gradientIndex (axis : Fin 3) : LowJet := ⟨axis.val + 1, by omega⟩
def hessianIndex (axis direction : Fin 3) : LowJet :=
  ![![4, 5, 6], ![5, 7, 8], ![6, 8, 9]] axis direction
def recordedField (f : WholeCellSource.Field) : FieldBox :=
  ⟨fun axis => WholeCellSource.reportedDensity f (gradientIndex axis),
    fun axis direction => WholeCellSource.reportedDensity f (hessianIndex axis direction)⟩
def sourceCall (q : Quarter) (step stage : Fin 4) : WholeCellSource.Field :=
  WholeCellSource.fieldCall q ⟨4 * step.val + stage.val, by omega⟩
def recordedFields (q : Quarter) (step stage : Fin 4) : FieldBox := recordedField (sourceCall q step stage)
def generatedStates (q : Quarter) : Fin 5 → JetBox :=
  fourStepState (recordedFields q) SourceCellGeometry.initialJetBox (stepSizeInterval q)
    SourceCellGeometry.stepDerivativeInterval
def generatedStageInput (q : Quarter) (step stage : Fin 4) : JetBox :=
  match stage.val with
  | 0 => generatedStates q step.castSucc
  | 1 => intervalStage2 (recordedFields q step) (generatedStates q step.castSucc)
      (stepSizeInterval q) SourceCellGeometry.stepDerivativeInterval
  | 2 => intervalStage3 (recordedFields q step) (generatedStates q step.castSucc)
      (stepSizeInterval q) SourceCellGeometry.stepDerivativeInterval
  | _ => intervalStage4 (recordedFields q step) (generatedStates q step.castSucc)
      (stepSizeInterval q) SourceCellGeometry.stepDerivativeInterval

def finalField (q : Quarter) : WholeCellSource.Field := WholeCellSource.fieldCall q 16
def generatedTargetLaplacian (q : Quarter) : Pair :=
  add (add (add (point 0) (WholeCellSource.reportedDensity (finalField q) 4))
    (WholeCellSource.reportedDensity (finalField q) 7)) (WholeCellSource.reportedDensity (finalField q) 9)
def generatedTargetDeterminant (q : Quarter) : Pair := determinantPair (generatedStates q 4).derivative
def generatedTargetIntegrand (q : Quarter) : Pair := mul (generatedTargetLaplacian q) (generatedTargetDeterminant q)
def quarterMeasure (q : Quarter) : ℚ := rationalBoxVolume (quarterLowerQ q) (quarterUpperQ q)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay
