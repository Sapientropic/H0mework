import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationTransportedGraded
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaUncutDomain

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
abbrev Localizer:=CanonicalGradedLocalCurrent.Localizer
abbrev FiberMap:=CanonicalGradedLocalCurrent.FiberMap
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

def NumberNeutral (A : SourceCoordinateSlice→FiberMap) : Prop:=
  ∀z w,Commute (weight w) (A z)

theorem actualFiber_number (p : PhysicalMomentum) : NumberNeutral (actualFiber p) :=by
  intro z w;exact weight_commute w _

def matterFiber (z : SourceCoordinateSlice) : FiberMap:=
  ∑i : Fin 3,∑j : Fin 3,quantized (GaussMatterCore.localMatrix i j z)

theorem matterFiber_number : NumberNeutral matterFiber :=by
  intro z w
  apply Commute.sum_right;intro i _
  apply Commute.sum_right;intro j _
  exact weight_commute w _

theorem yukawaFiber_number : NumberNeutral yukawaFiber :=by
  intro z w
  exact PreparationVacuumUncutYukawa.sourceMap_number (scalarField z) w

theorem retained_number : NumberNeutral retainedCoefficient :=by
  intro z w
  change Commute (weight w) (actualFiber 0 z-yukawaFiber z-matterFiber z)
  have h:=((actualFiber_number 0 z w).sub_right (yukawaFiber_number z w)).sub_right (matterFiber_number z w)
  exact h

theorem transport_commutes (A : SourceCoordinateSlice→FiberMap) (neutral : NumberNeutral A)
    (f : Field289) (z : SourceCoordinateSlice) (r : ℝ) :
    Commute (transportFiber f z r) (A (fieldCoordinateCurve f r z)) :=
  neutral _ (fun N=>halfRatio f N z r)

def fixedSample (A : SourceCoordinateSlice→FiberMap) (f : Field289) (a b : QuantumTest) (u : Parameter) : ℂ:=
  pairSample u.2 (a u.2) (A (fieldCoordinateCurve f u.1 u.2) (b u.2))

theorem movingFiber_fixed (A : SourceCoordinateSlice→FiberMap) (neutral : NumberNeutral A)
    (f : Field289) (a b : QuantumTest) (r : ℝ) (z : physicalChart)
    (moved : fieldCoordinateCurve f r z.val∈physicalChart) :
    movingFiber f (transportedSection f a) (transportedSection f b) A (r,z.val)=fixedSample A f a b (r,z.val) :=by
  have commute:=congrArg (fun T : FiberMap=>T (b z.val)) (transport_commutes A neutral f z.val r).eq
  change transportFiber f z.val r (A (fieldCoordinateCurve f r z.val) (b z.val))=
    A (fieldCoordinateCurve f r z.val) (transportFiber f z.val r (b z.val)) at commute
  change pairSample (fieldCoordinateCurve f r z.val) (transportFiber f z.val r (a z.val))
    (A (fieldCoordinateCurve f r z.val) (transportFiber f z.val r (b z.val)))=_
  rw [←commute]
  exact pair_transport f z r moved _ _

def fixedFiber (A : SourceCoordinateSlice→FiberMap) (f : Field289) (a b : QuantumTest) (r : ℝ) : ℂ:=
  ∫z,fixedSample A f a b (r,z) ∂GaussHistoryHilbert.configurationMeasure

theorem fiberIntegral_fixed (A : SourceCoordinateSlice→FiberMap) (neutral : NumberNeutral A)
    (f : Field289) (a b : QuantumTest) (r : ℝ) (small : |r|<fieldRadius f a) :
    fiberIntegral f a b A r=fixedFiber A f a b r :=by
  unfold fiberIntegral fixedFiber
  apply integral_congr_ae
  apply Filter.Eventually.of_forall;intro z
  by_cases inside : z∈tsupport a
  · exact movingFiber_fixed A neutral f a b r ⟨z,a.tsupport_subset inside⟩
      (fieldRadius_chart f a r z small.le inside)
  · simp only [movingFiber,transportedSection_zero_outside f a r z inside,fixedSample,
      image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

theorem fiberIntegral_fixed_germ (A : SourceCoordinateSlice→FiberMap) (neutral : NumberNeutral A)
    (f : Field289) (a b : QuantumTest) : fiberIntegral f a b A=ᶠ[𝓝 0] fixedFiber A f a b :=by
  have small : ∀ᶠr : ℝ in 𝓝 0,|r|<fieldRadius f a:=
    (continuous_abs.tendsto 0).eventually (gt_mem_nhds (by simpa using fieldRadius_positive f a))
  exact small.mono (fun r hr=>fiberIntegral_fixed A neutral f a b r hr)

theorem actualFiber_fixed (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    fiberIntegral f a b (actualFiber p)=ᶠ[𝓝 0] fixedFiber (actualFiber p) f a b :=
  fiberIntegral_fixed_germ _ (actualFiber_number p) f a b

theorem retained_fixed (f : Field289) (a b : QuantumTest) :
    fiberIntegral f a b retainedCoefficient=ᶠ[𝓝 0] fixedFiber retainedCoefficient f a b :=
  fiberIntegral_fixed_germ _ retained_number f a b

end LowEnergy.PreparationVacuumHalfDensityFiber
