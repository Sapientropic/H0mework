import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.SourceFrameMatrixPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualSourceFieldMatrixPriceOwn
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumMixedFieldReturn
open PreparationVacuumFieldConstraintResponse ActualQuantitativePreparedFrameOwn
open GaussCoreHilbert GaussFockPair CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open scoped BigOperators InnerProductSpace
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

def originalBaseMatrix (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    FrameIndex F → FrameIndex F → ℂ := fun i j =>
  sourcePair (frameTest F i) ((physicalAction p + GaussYukawaOperator.originalAction) (frameTest F j))

def sourceFormPrice (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  matrixPrice F (originalBaseMatrix p F)

def sourceCurrentPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  matrixPrice F (fun i j => (fieldJets f p (frameTest F i) (frameTest F j)).first 0)

def sourceContactPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  matrixPrice F (fun i j => (fieldJets f p (frameTest F i) (frameTest F j)).second)

def bestFormPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (originalFormPrice f p F) (sourceFormPrice p F)
def bestCurrentPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (currentPrice f p F) (sourceCurrentPrice f p F)
def bestContactPrice (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (contactPrice f p F) (sourceContactPrice f p F)

theorem fieldMatrix_original_source (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    fieldMatrix f p F 0 = originalBaseMatrix p F := by
  funext i j
  exact fieldForm_source f p (frameTest F i) (frameTest F j)

theorem original_form_matrix_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖formRestriction f p F 0‖ ≤ sourceFormPrice p F := by
  unfold formRestriction
  rw [fieldMatrix_original_source]
  exact original_frame_matrix_operator_price F _

theorem original_current_matrix_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖currentRestriction f p F 0‖ ≤ sourceCurrentPrice f p F :=
  original_frame_matrix_operator_price F _

theorem original_contact_matrix_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖contactRestriction f p F‖ ≤ sourceContactPrice f p F :=
  original_frame_matrix_operator_price F _

theorem original_form_best_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖formRestriction f p F 0‖ ≤ bestFormPrice f p F :=
  le_min (finiteRiesz_price F _) (original_form_matrix_price f p F)
theorem original_current_best_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖currentRestriction f p F 0‖ ≤ bestCurrentPrice f p F :=
  le_min (finiteRiesz_price F _) (original_current_matrix_price f p F)
theorem original_contact_best_price (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖contactRestriction f p F‖ ≤ bestContactPrice f p F :=
  le_min (finiteRiesz_price F _) (original_contact_matrix_price f p F)

end LowEnergy.ActualSourceFieldMatrixPriceOwn
