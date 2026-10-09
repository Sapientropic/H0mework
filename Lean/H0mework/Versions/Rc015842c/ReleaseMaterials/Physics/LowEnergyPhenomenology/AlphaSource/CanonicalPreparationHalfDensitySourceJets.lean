import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationHalfDensityFixedFiber
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationFieldPreparedCovector

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumHalfDensityFiber
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussQuantumMultiplier
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse
open PreparationVacuumActionDecomposition PreparationVacuumActualFieldQuantization
open PreparationVacuumSourceActionJets SourceQuantumScalarChart GaussLiveMomentum
open PreparationVacuumCausalFieldResponse PreparationVacuumNonlinearFieldCurve
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open GaussComposite GaussComposite.SourceGraph PreparationVacuumSourcePreparedResponse
open CanonicalGradedLocalCurrent Filter Set
open GaussUnitaryHistory (Index)
open scoped Matrix Matrix.Norms.L2Operator ContDiff Topology BigOperators Distributions InnerProductSpace Interval
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationVacuumGradedTransport GaussDensityCore GaussYukawaCoefficient GaussNativePotential
open MeasureTheory

open PreparationVacuumFieldCovector PreparationVacuumActionFieldLift

def pairRight (z : SourceCoordinateSlice) (v : FockFiber) : FockFiber→L[ℂ] ℂ:=
  (show FockFiber→ₗ[ℂ] ℂ from {
    toFun:=pairSample z v
    map_add':=fun a b=>PreparationVacuumFullFieldRiesz.pairSample_add_right z v a b
    map_smul':=fun c a=>by
      simpa only [RingHom.id_apply,smul_eq_mul] using PreparationVacuumFullFieldRiesz.pairSample_smul_right z c v a
  }).toContinuousLinearMap

theorem fixedSample_smooth (A : SourceCoordinateSlice→FiberMap)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (f : Field289) (a b : QuantumTest)
    (u : Parameter) (base : u.2∈physicalChart) (moved : fieldCoordinateCurve f u.1 u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (fixedSample A f a b) u :=by
  let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
  have ha:=R.contDiff.contDiffAt.comp u ((smooth ⟨_,moved⟩).comp u (field_curve_smooth f u.1 ⟨u.2,base⟩))
  exact pairSample_param Prod.snd _ _ u base contDiffAt_snd (a.contDiff.contDiffAt.comp u contDiffAt_snd)
    (ha.clm_apply (b.contDiff.contDiffAt.comp u contDiffAt_snd))

theorem fixedSample_zero (A : SourceCoordinateSlice→FiberMap) (f : Field289) (a b : QuantumTest)
    (r : ℝ) (z : SourceCoordinateSlice) (outside : z∉tsupport a) : fixedSample A f a b (r,z)=0 :=by
  simp only [fixedSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem fixedFiber_integrable (A : SourceCoordinateSlice→FiberMap)
    (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (f : Field289) (a b : QuantumTest)
    (r : ℝ) (small : |r|<fieldRadius f a) :
    Integrable (fun z=>fixedSample A f a b (r,z)) GaussHistoryHilbert.configurationMeasure :=by
  have continuous : Continuous (fun z=>fixedSample A f a b (r,z)) :=by
    apply continuous_iff_continuousAt.mpr;intro z
    by_cases inside : z∈tsupport a
    · exact (fixedSample_smooth A smooth f a b (r,z) (a.tsupport_subset inside)
        (fieldRadius_chart f a r z small.le inside)).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds inside] with y hy
      exact fixedSample_zero A f a b r y hy
  apply continuous.integrable_of_hasCompactSupport
  apply a.hasCompactSupport.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport a)
  intro z hz;by_contra outside
  exact hz (fixedSample_zero A f a b r z outside)

theorem fixedFiber_sub (A B : SourceCoordinateSlice→FiberMap)
    (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (hB : ∀z : physicalChart,ContDiffAt ℝ ∞ B z.val)
    (f : Field289) (a b : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) :
    fixedFiber (fun z=>A z-B z) f a b r=fixedFiber A f a b r-fixedFiber B f a b r :=by
  have point : fixedSample (fun z=>A z-B z) f a b=fun u=>fixedSample A f a b u-fixedSample B f a b u :=by
    funext u
    simp only [fixedSample,sub_apply,pairSample,PiLp.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [fixedFiber,point,integral_sub (fixedFiber_integrable A hA f a b r small) (fixedFiber_integrable B hB f a b r small)]
  rfl

def fixedJets (A : SourceCoordinateSlice→FiberMap) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (f : Field289) (a b : QuantumTest) : TwoJets (fixedFiber A f a b) :=
  parameterIntegralJets (fixedSample A f a b) f a (fixedSample_smooth A smooth f a b) (fixedSample_zero A f a b)

theorem fiber_first_fixed (A : SourceCoordinateSlice→FiberMap) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (neutral : NumberNeutral A) (f : Field289) (a b : QuantumTest) :
    (fiberIntegralJets f a b A smooth).first 0=(fixedJets A smooth f a b).first 0 :=
  (fiberIntegralJets f a b A smooth).actual.1.unique
    ((fixedJets A smooth f a b).actual.1.congr_of_eventuallyEq (fiberIntegral_fixed_germ A neutral f a b))

theorem fiber_second_fixed (A : SourceCoordinateSlice→FiberMap) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (neutral : NumberNeutral A) (f : Field289) (a b : QuantumTest) :
    (fiberIntegralJets f a b A smooth).second=(fixedJets A smooth f a b).second :=
  (fiberIntegralJets f a b A smooth).actual.2.unique
    ((fixedJets A smooth f a b).actual.2.congr_of_eventuallyEq (fiberIntegral_fixed_germ A neutral f a b).deriv)

def fixedCurrent (A : SourceCoordinateSlice→FiberMap) (f : Field289) (a b : QuantumTest) (z : SourceCoordinateSlice) : ℂ:=
  pairSample z (a z) (fderiv ℝ A z (fieldVector f z) (b z))

theorem fixedSample_current (A : SourceCoordinateSlice→FiberMap) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (f : Field289) (a b : QuantumTest) (z : physicalChart) :
    parameterJet (fixedSample A f a b) (0,z.val)=fixedCurrent A f a b z.val :=by
  have joint:=fixedSample_smooth A smooth f a b (0,z.val) z.property
    (by rw [curve_zero];exact z.property)
  have left:=partial_parameter _ 0 z.val joint
  have line : HasDerivAt (fun r : ℝ=>fieldCoordinateCurve f r z.val) (fieldVector f z.val) 0 :=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const (fieldVector f z.val)).const_add z.val using 1
    simp
  have hs : HasFDerivAt A (fderiv ℝ A z.val) (fieldCoordinateCurve f 0 z.val) :=by
    rw [curve_zero];exact (smooth z).differentiableAt (by simp) |>.hasFDerivAt
  let E : FiberMap→L[ℝ] FockFiber:=(ContinuousLinearMap.apply ℂ FockFiber (b z.val)).restrictScalars ℝ
  let P : FockFiber→L[ℝ] ℂ:=(pairRight z.val (a z.val)).restrictScalars ℝ
  have hv:=E.hasFDerivAt.comp_hasDerivAt 0 (hs.comp_hasDerivAt 0 line)
  have hp:=P.hasFDerivAt.comp_hasDerivAt 0 hv
  exact left.unique hp

theorem fixedJets_first (A : SourceCoordinateSlice→FiberMap) (smooth : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (f : Field289) (a b : QuantumTest) :
    (fixedJets A smooth f a b).first 0=∫z,fixedCurrent A f a b z ∂GaussHistoryHilbert.configurationMeasure :=by
  change (∫z,parameterJet (fixedSample A f a b) (0,z) ∂GaussHistoryHilbert.configurationMeasure)=_
  apply integral_congr_ae;apply Filter.Eventually.of_forall;intro z
  by_cases inside : z∈tsupport a
  · exact fixedSample_current A smooth f a b ⟨z,a.tsupport_subset inside⟩
  · dsimp only
    rw [partial_zero_outside _ (tsupport a) (isClosed_tsupport a) (fixedSample_zero A f a b) 0 z inside]
    simp only [fixedCurrent,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem actual_fixed_current (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    fixedCurrent (actualFiber p) f a b z.val=
      pairSample z.val (a z.val) (quantizer (symbolFirst p (sourceState z.val) (sliceState (fieldVector f z.val))) (b z.val)) :=by
  rw [fixedCurrent,actualFiber_slice]

theorem transported_mother_balance (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (z : physicalChart) :
    fixedCurrent (actualFiber p) f a b z.val+
      pairSample z.val (a z.val) (quantizer (symbolFirst p (sourceState z.val) (complement f z.val)) (b z.val))=
      -pairSample z.val (a z.val) (fiberFamily f p z.val (b z.val)) :=by
  have read:=congrArg (fun T : FiberMap=>pairSample z.val (a z.val) (T (b z.val))) (mother_current_slice f p z)
  simpa only [fixedCurrent,add_apply,PreparationVacuumFullFieldRiesz.pairSample_add_right,neg_apply,
    pairSample,PiLp.neg_apply,PiLp.add_apply,mul_add,Finset.sum_add_distrib,mul_neg,Finset.sum_neg_distrib] using read

end LowEnergy.PreparationVacuumHalfDensityFiber
