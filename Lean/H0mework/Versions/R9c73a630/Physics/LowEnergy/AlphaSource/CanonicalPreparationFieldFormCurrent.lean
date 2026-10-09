import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationFieldTangentCurrent

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumFieldCovector
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

open GaussCoframeForm GaussDensityCore

def Reconstruct (J : Field289→ℂ) : Prop:=∀f,J f=∑i : Fin 289,(f i:ℂ)*J (fieldBasis i)

theorem reconstruct_add {J K : Field289→ℂ} (hj : Reconstruct J) (hk : Reconstruct K) : Reconstruct (fun f=>J f+K f) :=by
  intro f;dsimp only;rw [hj f,hk f]
  simp only [mul_add,Finset.sum_add_distrib]

theorem reconstruct_sub {J K : Field289→ℂ} (hj : Reconstruct J) (hk : Reconstruct K) : Reconstruct (fun f=>J f-K f) :=by
  intro f;dsimp only;rw [hj f,hk f]
  simp only [mul_sub,Finset.sum_sub_distrib]

theorem reconstruct_scale {J : Field289→ℂ} (hj : Reconstruct J) (c : ℂ) : Reconstruct (fun f=>c*J f) :=by
  intro f;dsimp only;rw [hj f,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _;ring

theorem reconstruct_sum {ι : Type*} [Fintype ι] {J : ι→Field289→ℂ} (hj : ∀i,Reconstruct (J i)) :
    Reconstruct (fun f=>∑i,J i f) :=by
  intro f
  dsimp only
  calc
    _=∑i,∑a : Fin 289,(f a:ℂ)*J i (fieldBasis a):=Finset.sum_congr rfl (fun i _=>hj i f)
    _=∑a : Fin 289,∑i,(f a:ℂ)*J i (fieldBasis a):=Finset.sum_comm
    _=_:=by simp only [Finset.mul_sum]

theorem row_first_coordinates (c : SourceCoordinateSlice→ℝ) (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (a b : QuantumTest) : Reconstruct (fun f=>(rowFieldJets f c hc a b).first 0) :=by
  intro f
  exact sample_first_coordinates (rowSample c a b) a
    (fun g r z hz hx=>rowSample_param c hc a b (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fun z=>(rowSample_param c hc a b id (fun _=>z.val) z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (rowSample_zero_outside c a b) f

theorem fiber_first_coordinates (A : SourceCoordinateSlice→FiberMap) (hA : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val)
    (a b : QuantumTest) : Reconstruct (fun f=>(fiberFieldJets f A hA a b).first 0) :=by
  intro f
  exact sample_first_coordinates (fiberSample A a b) a
    (fun g r z hz hx=>fiberSample_param A hA a b (fun u : Parameter=>fieldCoordinateCurve g u.1 u.2) Prod.snd
      (r,z) hx (field_curve_smooth g r ⟨z,hz⟩) contDiffAt_snd)
    (fun z=>(fiberSample_param A hA a b id (fun _=>z.val) z.val z.property contDiffAt_id contDiffAt_const).differentiableAt (by simp))
    (fiberSample_zero_outside A a b) f

theorem mixed_first_coordinates (i : Fin 6) (k : Fin 7) (c : SourceCoordinateSlice→ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) (a b : QuantumTest) :
    Reconstruct (fun f=>(mixedFieldJets f i k c hc a b).first 0) :=
  reconstruct_scale (reconstruct_add
    (row_first_coordinates c hc (GaussCoframeSpin.current k a) (GaussCoframeCore.momentum i b))
    (row_first_coordinates c hc (GaussCoframeCore.momentum i a) (GaussCoframeSpin.current k b))) (1/2:ℂ)

theorem coframe_first_coordinates (a b : QuantumTest) :
    Reconstruct (fun f=>(coframeFieldJets f a b).first 0) :=by
  have kin:=reconstruct_sum (fun i : Fin 6=>reconstruct_sum (fun j : Fin 6=>
    row_first_coordinates (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)
      (GaussCoframeCore.momentum i a) (GaussCoframeCore.momentum j b)))
  have cur:=reconstruct_add (reconstruct_add (reconstruct_add
    (mixed_first_coordinates 1 5 (currentCoefficient 0) (currentCoefficient_smooth 0) a b)
    (mixed_first_coordinates 3 3 (currentCoefficient 1) (currentCoefficient_smooth 1) a b))
    (mixed_first_coordinates 3 4 (fun z=>-currentCoefficient 0 z) (fun z=>(currentCoefficient_smooth 0 z).neg) a b))
    (mixed_first_coordinates 4 3 (currentCoefficient 2) (currentCoefficient_smooth 2) a b)
  have spin:=reconstruct_sum (fun k : Fin 7=>reconstruct_scale
    (row_first_coordinates inverseVolume inverseVolume_smooth (GaussCoframeSpin.current k a) (GaussCoframeSpin.current k b)) (spinWeight k:ℂ))
  have num:=reconstruct_scale (reconstruct_add
    (row_first_coordinates numberCoefficient numberCoefficient_smooth (number a) b)
    (row_first_coordinates numberCoefficient numberCoefficient_smooth a (number b))) (1/2:ℂ)
  exact reconstruct_add (reconstruct_add (reconstruct_add (reconstruct_add kin cur) spin) num)
    (row_first_coordinates volumePotential volumePotential_smooth a b)

theorem field_first_coordinates (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    (fieldJets f p a b).first 0=∑i : Fin 289,(f i:ℂ)*(fieldJets (fieldBasis i) p a b).first 0 :=
  reconstruct_sub (reconstruct_add (reconstruct_add (fun f=>native_first_coordinates f a b)
    (coframe_first_coordinates a b)) (fiber_first_coordinates (actualFiber p) (actualFiber_smooth p) a b))
    (fiber_first_coordinates retainedCoefficient retainedCoefficient_smooth a b) f

def sourceCovector (p : PhysicalMomentum) (a b : QuantumTest) : Fin 289→ℂ:=
  fun i=>(fieldJets (fieldBasis i) p a b).first 0

theorem sourceCovector_derivative (f : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fieldForm f p a b) (∑i : Fin 289,(f i:ℂ)*sourceCovector p a b i) 0 :=by
  simp only [sourceCovector]
  rw [←field_first_coordinates]
  exact (fieldJets f p a b).actual.1

end LowEnergy.PreparationVacuumFieldCovector
