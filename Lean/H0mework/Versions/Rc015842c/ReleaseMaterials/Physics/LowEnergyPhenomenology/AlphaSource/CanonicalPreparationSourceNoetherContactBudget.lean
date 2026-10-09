import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActionFieldFeed
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalFiveSourcePrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherResponsePrice
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair GaussQuantumMultiplier
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open PreparationVacuumFixedMomentumActionReturn PreparationVacuumIndependentMomentumReturn
open PreparationVacuumMatterEulerFeedback PreparationVacuumPhysicalTailPrice
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherOrdinaryWard PreparationVacuumFullFieldRiesz
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift CanonicalGradedSpatialSource
open PreparationVacuumHalfDensityFiber PreparationVacuumGaugeSourceInjection
open PreparationVacuumSourceActionJets
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] physicalTime jointResolvent noetherReaderContact rawReaderContact
  factorialBudget sourceFixedMomentumContact

def sourceContactScalar (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∫z,pairSample z (a z)
    (quantizer (sourceFixedMomentumContact reader force p (sourceState z) (sourceState z)) (b z))
      ∂GaussHistoryHilbert.configurationMeasure

theorem sourceContactScalar_actual (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    sourceContactScalar reader force p a b=noetherContactForm reader force p a b :=by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change pairSample z (a z) (quantizer (sourceFixedMomentumContact reader force p (sourceState z) (sourceState z)) (b z))=
    pairSample z (a z) (quantizer (noetherContactSymbol reader force (sourceState z) p) (b z))
  by_cases inside : z∈tsupport a
  · rw [sourceFixedMomentumContact_noether reader force p ⟨z,a.tsupport_subset inside⟩]
  · simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

def sourceContactIncrementEntries (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i j : FrameIndex F) : ℂ:=
  sourceContactScalar reader force p (frameTest F i) (frameTest F j)-
    rawContactForm reader force p (frameTest F i) (frameTest F j)

def sourceContactIncrementPrice (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℝ:=
  finitePrice F (sourceContactIncrementEntries reader force p F)

theorem sourceContactIncrement_reader (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact reader force p F-rawReaderContact reader force p F=
      finiteRiesz F (sourceContactIncrementEntries reader force p F) :=by
  rw [noetherReaderContact_source,rawReaderContact]
  simp only [finiteRiesz,sourceContactIncrementEntries,sourceContactScalar_actual,sub_smul,Finset.sum_sub_distrib]

theorem sourceContactIncrementPrice_nonnegative (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : 0 ≤ sourceContactIncrementPrice reader force p F :=
  finitePrice_nonnegative F _

theorem sourceContactIncrement_norm (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ‖noetherReaderContact reader force p F-rawReaderContact reader force p F‖≤
      sourceContactIncrementPrice reader force p F :=by
  rw [sourceContactIncrement_reader]
  exact finiteRiesz_price F _

def correctedContactCoefficient (q : PhysicalResponsePoint) (reader force : Field289) (eta : ℝ) : ℝ:=
  factorialBudget (q.p+q.k) q.F eta*‖jointResolvent (q.p+q.k) q.F q.z 0‖*
    sourceContactIncrementPrice reader force q.p q.F*‖jointResolvent q.p q.F q.w 0‖*
      factorialBudget q.p q.F eta

theorem correctedContactCoefficient_nonnegative (q : PhysicalResponsePoint) (reader force : Field289)
    (eta : ℝ) (positive : 0<eta) : 0≤correctedContactCoefficient q reader force eta :=by
  have left:=factorialBudget_nonnegative (q.p+q.k) q.F eta positive
  have right:=factorialBudget_nonnegative q.p q.F eta positive
  have contact:=sourceContactIncrementPrice_nonnegative reader force q.p q.F
  unfold correctedContactCoefficient
  positivity

private theorem source_envelope_mul (A B : SourceOperator) (a b x y t : ℝ)
    (hA : ‖A‖≤a*Real.exp (x*t)) (hB : ‖B‖≤b*Real.exp (y*t)) :
    ‖A*B‖≤a*b*Real.exp ((x+y)*t) :=by
  refine (norm_mul_le A B).trans
    ((mul_le_mul hA hB (norm_nonneg B) ((norm_nonneg A).trans hA)).trans_eq ?_)
  rw [add_mul,Real.exp_add]
  ring

private theorem source_constant_envelope (A : SourceOperator) (t : ℝ) : ‖A‖≤‖A‖*Real.exp (0*t) :=by simp

theorem correctedContactKernel_price (q : PhysicalResponsePoint) (reader force : Field289) (eta t : ℝ)
    (positive : 0<eta) (future : 0≤t) :
    ‖(correctedContactJet q reader force t).value‖≤
      correctedContactCoefficient q reader force eta*Real.exp (2*eta*t) :=by
  have contact : ‖noetherReaderContact reader force q.p q.F-rawReaderContact reader force q.p q.F‖≤
      sourceContactIncrementPrice reader force q.p q.F*Real.exp (0*t):=by
    simpa only [zero_mul,Real.exp_zero,mul_one] using sourceContactIncrement_norm reader force q.p q.F
  have actual:=source_envelope_mul _ _ _ _ _ _ t
    (source_envelope_mul _ _ _ _ _ _ t
      (source_envelope_mul _ _ _ _ _ _ t
        (source_envelope_mul _ _ _ _ _ _ t
          (actualTime_past (q.p+q.k) q.F eta t positive future)
          (source_constant_envelope (jointResolvent (q.p+q.k) q.F q.z 0) t)) contact)
      (source_constant_envelope (jointResolvent q.p q.F q.w 0) t))
    (actualTime_future q.p q.F eta t positive future)
  change ‖(physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*
    (noetherReaderContact reader force q.p q.F-rawReaderContact reader force q.p q.F)*
      jointResolvent q.p q.F q.w 0)*physicalTime q.p q.F t 0‖≤_ at actual
  convert! actual using 1
  · simp only [correctedContactJet,jetMul,jetConst,physicalTimeJet,timeJet,physicalTime,
      neg_one_mul,one_mul,add_zero]
  · simp only [correctedContactCoefficient,add_zero]
    rw [show eta+eta=2*eta from by ring]

end LowEnergy.PreparationVacuumNoetherResponsePrice
