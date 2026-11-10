import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedMixed289Price
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.SourceFieldMatrixPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicStaticPrice
import H0mework.Versions.Rdf421ff6.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNoetherContactBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualMixedNoetherTimePriceOwn
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumFullFieldRiesz
open PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart PreparationVacuumRawJointFeedback
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationVacuumYukawaTransport
open PreparationVacuumPhysicalHalfAxis PreparationVacuumNoetherResponsePrice PreparationVacuumSourcePreparedResponse
open GaussComposite.ActualDressedLeftFreeJet GaussComposite.ActualDressedCubicPrice GaussComposite.ActualDressedNumberField
open ActualSourceMixed289ResponseOwn ActualSourceFieldMatrixPriceOwn
open scoped BigOperators Topology InnerProductSpace
attribute [local irreducible] jointCurrent jointResolvent noetherReader noetherReaderContact rawReaderContact
  physicalTime actualA transportedCurrent uncutSlope sourceYJet sourceProfile

def originalNoetherReaderPrice (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (finitePrice F (fun i j => noetherForm reader p (frameTest F i) (frameTest F j) 0))
    (matrixPrice F (fun i j => noetherForm reader p (frameTest F i) (frameTest F j) 0))

def originalNoetherContactPrice (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (finitePrice F (fun i j => noetherContactForm reader force p (frameTest F i) (frameTest F j)))
    (matrixPrice F (fun i j => noetherContactForm reader force p (frameTest F i) (frameTest F j)))

def originalNoetherRawIncrementPrice (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  min (sourceContactIncrementPrice reader force p F) (matrixPrice F (sourceContactIncrementEntries reader force p F))

private theorem original_noether_reader_entries (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader reader p F 0 = finiteRiesz F (fun i j => noetherForm reader p (frameTest F i) (frameTest F j) 0) := by
  unfold noetherReader
  rfl

theorem originalNoetherReader_price (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖noetherReader reader p F 0‖ ≤ originalNoetherReaderPrice reader p F := by
  rw [original_noether_reader_entries]
  exact le_min (finiteRiesz_price F _) (original_frame_matrix_operator_price F _)

theorem originalNoetherContact_price (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖noetherReaderContact reader force p F‖ ≤ originalNoetherContactPrice reader force p F := by
  rw [noetherReaderContact_source]
  exact le_min (finiteRiesz_price F _) (original_frame_matrix_operator_price F _)

theorem originalNoetherRawIncrement_price (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖noetherReaderContact reader force p F - rawReaderContact reader force p F‖ ≤ originalNoetherRawIncrementPrice reader force p F := by
  rw [sourceContactIncrement_reader]
  exact le_min (finiteRiesz_price F _) (original_frame_matrix_operator_price F _)

private theorem original_free_current (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    freeCompressionCurrent p F force = transportedCurrent force p F 0 :=
  ((free_compression_direction p F force).congr_of_eventuallyEq (jointCompression_ray force p F).symm).unique
    (transportedCompression_first force p F)

private theorem original_free_current_split (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    freeCompressionCurrent p F force = jointCurrent p F 0 0 force - uncutSlope force (finiteRetainer p F) := by
  rw [jointCurrent_source]
  unfold sourceCurrent sourceYJet uncutJetOperator
  change freeCompressionCurrent p F force = (transportedCurrent force p F 0 + uncutSlope force (finiteRetainer p F)) - uncutSlope force (finiteRetainer p F)
  rw [add_sub_cancel_right]
  exact original_free_current force p F

def originalFreeCurrentPrice (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ :=
  originalJointCurrentPrice force p F + (originalCompactYPrice force p F 1 + originalCompactYPrice force p F 0)

theorem originalFreeCurrent_price (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖freeCompressionCurrent p F force‖ ≤ originalFreeCurrentPrice force p F := by
  rw [original_free_current_split]
  have slope : ‖uncutSlope force (finiteRetainer p F)‖ ≤ originalCompactYPrice force p F 1 + originalCompactYPrice force p F 0 := by
    unfold uncutSlope
    exact (norm_sub_le _ _).trans (add_le_add (originalCompactY_price force p F 1) (originalCompactY_price force p F 0))
  exact (norm_sub_le _ _).trans (add_le_add (originalJointCurrent_price force p F 0) slope)

theorem originalFreeResolvent_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im ≠ 0) :
    ‖jointCResolvent p F z 0‖ ≤ 1 / |z.im| := by
  rw [free_green_base]
  exact CanonicalPhysicalResolvent.finite_bound p F z hz

def originalPhysicalTimePrice (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 57, (|age| * originalCompactYPrice 0 p F 0)^n

private theorem scalar_time_price_mono (T a b : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.range 57, (T*a)^n) ≤ ∑ n ∈ Finset.range 57, (T*b)^n := by
  apply Finset.sum_le_sum
  intro n _
  exact pow_le_pow_left₀ (mul_nonneg hT ha) (mul_le_mul_of_nonneg_left hab hT) n

private theorem original_actualA_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖actualA p F‖ ≤ originalCompactYPrice 0 p F 0 := by
  have source : actualA p F = uncutOperator 0 (finiteRetainer p F) 0 := by
    unfold actualA
    rfl
  exact (congrArg norm source).le.trans (originalCompactY_price 0 p F 0)

theorem originalPhysicalTime_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) :
    ‖physicalTime p F age 0‖ ≤ originalPhysicalTimePrice p F age :=
  (actual_time_bound p F age).trans
    (scalar_time_price_mono |age| ‖actualA p F‖ (originalCompactYPrice 0 p F 0)
      (abs_nonneg age) (norm_nonneg _) (original_actualA_price p F))

end LowEnergy.ActualMixedNoetherTimePriceOwn
