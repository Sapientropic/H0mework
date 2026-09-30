import H0mework.NavierStokes.WindowEnergyCrossHistory.Green

set_option autoImplicit false
open scoped BigOperators Topology ContDiff ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportGreen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowCrossHistoryAction NativeWindowCrossHistoryGreen
noncomputable section
variable {nu : Viscosity}

def drift (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (time : ℝ) : Vector :=
  velocity seed F time-velocity seed A time

def driftJet (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (time : ℝ) : Gradient :=
  gradient seed F time-gradient seed A time

def commonField (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) : C(Torus,ℝ) :=
  ∑ j : Coordinate,(drift seed F A first j+drift seed F A last j)*
    crossDerivative (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j

def incrementField (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) : C(Torus,ℝ) :=
  ∑ j : Coordinate,(drift seed F A first j-drift seed F A last j)*
    wedge (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j

def transportPair (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) : C(Torus,ℝ) :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,
    (drift seed F A first j*velocity seed F first output*velocity seed F first input)*
      (gradient seed F last j output*velocity seed F last input+velocity seed F last output*gradient seed F last j input)

def flux (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) (x : PhysicalSpace) : PhysicalSpace :=
  inner ℝ (vector seed F first x) (vector seed F last x)^2 •
    ((vector seed F first x-vector seed A first x)+(vector seed F last x-vector seed A last x))

theorem flux_smooth (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) :
    ContDiff ℝ ∞ (flux seed F A first last) :=
  (((vector_smooth seed F first).inner ℝ (vector_smooth seed F last)).pow 2).smul
    (((vector_smooth seed F first).sub (vector_smooth seed A first)).add
      ((vector_smooth seed F last).sub (vector_smooth seed A last)))

theorem flux_periodic (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) :
    LatticePeriodic (flux seed F A first last) := by
  intro shift x
  simp only [flux,vector_periodic seed F first shift x,vector_periodic seed F last shift x,
    vector_periodic seed A first shift x,vector_periodic seed A last shift x]

theorem flux_coordinate (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ)
    (x : PhysicalSpace) (j : Coordinate) : flux seed F A first last x j =
      ((drift seed F A first j+drift seed F A last j)*pair (velocity seed F first) (velocity seed F last)^2)
        (NativeFullOrderSynthesis.circlePoint x) := by
  rw [flux,← pair_inner]
  simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,vector,drift,Pi.sub_apply,
    ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.pow_apply,smul_eq_mul]
  ring

theorem drift_derivative (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (time : ℝ)
    (i j : Coordinate) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => drift seed F A time i (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (driftJet seed F A time j i (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter :=
  (velocity_derivative seed F time i j x parameter).sub (velocity_derivative seed A time i j x parameter)

theorem flux_divergence (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0≤first) (last0 : 0≤last) (x : PhysicalSpace) :
    velocityDivergence (flux seed F A first last) x=2*(pair (velocity seed F first) (velocity seed F last)*
      commonField seed F A first last) (NativeFullOrderSynthesis.circlePoint x) := by
  have diagonal (j : Coordinate) : (fderiv ℝ (flux seed F A first last) x (EuclideanSpace.single j 1)) j =
      (((driftJet seed F A first j j+driftJet seed F A last j j)*pair (velocity seed F first) (velocity seed F last)^2+
        (2 : ℝ) • ((drift seed F A first j+drift seed F A last j)*pair (velocity seed F first) (velocity seed F last)*
          crossDerivative (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j))
        (NativeFullOrderSynthesis.circlePoint x)) := by
    have source := ((drift_derivative seed F A first j j x 0).add (drift_derivative seed F A last j j x 0)).mul
      ((pair_derivative seed F first last j x 0).pow 2)
    have path := (hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ)) |>.const_add x
    have actual := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Coordinate => ℝ) j).hasFDerivAt.comp_hasDerivAt 0
      (((flux_smooth seed F A first last).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 path)
    simp only [Function.comp_def,id_eq,zero_smul,add_zero,one_smul,PiLp.proj_apply,flux_coordinate,
      NativeWindowFiniteGramSource.line] at actual source
    simp only [Pi.add_apply,Pi.pow_apply,zero_smul,add_zero,Nat.cast_ofNat,
      show (2 : ℕ)-1=1 by decide,pow_one] at source
    have same := actual.unique source
    convert! same using 1
    simp only [ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
      ContinuousMap.smul_apply,smul_eq_mul]
    ring
  have zero (time : ℝ) (nonnegative : 0≤time) : (∑ j : Coordinate,driftJet seed F A time j j)=0 := by
    simp only [driftJet,Pi.sub_apply,Finset.sum_sub_distrib,gradient_trace_zero seed F time nonnegative,
      gradient_trace_zero seed A time nonnegative,sub_self]
  change (∑ j : Coordinate,(fderiv ℝ (flux seed F A first last) x (EuclideanSpace.single j 1)) j)=_
  simp_rw [diagonal]
  have firstZero := congrArg (fun f : C(Torus,ℝ) => f (NativeFullOrderSynthesis.circlePoint x)) (zero first first0)
  have lastZero := congrArg (fun f : C(Torus,ℝ) => f (NativeFullOrderSynthesis.circlePoint x)) (zero last last0)
  simp only [ContinuousMap.sum_apply,ContinuousMap.zero_apply] at firstZero lastZero
  simp only [commonField,ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.pow_apply,
    ContinuousMap.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.sum_mul,Finset.mul_sum]
  rw [firstZero,lastZero]
  ring

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem common_integral_zero (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0≤first) (last0 : 0≤last) : (∫ point : Torus,(pair (velocity seed F first) (velocity seed F last)*
      commonField seed F A first last) point)=0 := by
  have source := coordinateUnitCube_velocityDivergence_integral_eq_zero (flux seed F A first last)
    ((flux_smooth seed F A first last).of_le (by simp)) (flux_periodic seed F A first last)
  simp only [flux_divergence seed F A first last first0 last0] at source
  rw [integral_const_mul] at source
  rw [torus_cell]
  linarith

theorem green_algebra (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ) :
    -(1/2 : ℝ) • (pair (velocity seed F first) (velocity seed F last)*incrementField seed F A first last)+
      (1/2 : ℝ) • (pair (velocity seed F first) (velocity seed F last)*commonField seed F A first last)=
    (1/2 : ℝ) • (transportPair seed F A first last+transportPair seed F A last first) := by
  ext point
  simp only [pair,incrementField,commonField,transportPair,wedge,crossDerivative,Fin.sum_univ_three,
    ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem paired_green (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector) (first last : ℝ)
    (first0 : 0≤first) (last0 : 0≤last) :
    -(1/2 : ℝ)*(∫ point : Torus,(pair (velocity seed F first) (velocity seed F last)*incrementField seed F A first last) point)=
      (1/2 : ℝ)*((∫ point : Torus,transportPair seed F A first last point)+(∫ point : Torus,transportPair seed F A last first point)) := by
  have integral := congrArg (fun f : C(Torus,ℝ) => ∫ point : Torus,f point) (green_algebra seed F A first last)
  have paid (f : C(Torus,ℝ)) : Integrable f := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul] at integral
  rw [integral_add ((paid _).const_mul _) ((paid _).const_mul _),integral_const_mul,integral_const_mul,
    common_integral_zero seed F A first last first0 last0,integral_const_mul,integral_add (paid _) (paid _)] at integral
  linarith only [integral]

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportGreen
