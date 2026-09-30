import H0mework.NavierStokes.WindowEnergyAugmented.Gradient
import H0mework.NavierStokes.WindowEnergyAugmented.TimeForm
import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderEnergyHierarchy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowStageNineWords
open Set
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open NativeCommonAdvectorAction
open NativeFiniteActionResolvent NativeWindowOperatorGreen NativeWindowAugmentedFixedOperator
open NativeWindowAugmentedGradient (derivative derivative_apply)
open SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
noncomputable section
variable {nu : Viscosity}

def spatialGenerator (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (j : Coordinate) : Module.End ℝ (physicalSpace M) where
  toFun := derivative M zero closed j
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext k
    simp only [derivative_apply,Submodule.coe_add,lp.coeFn_add,Pi.add_apply,smul_add]
  map_smul' c x := by
    apply Subtype.ext
    apply lp.ext
    funext k
    simp only [derivative_apply,Submodule.coe_smul,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]
    exact smul_comm _ _ _

def word (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M) :
    List Coordinate → Module.End ℝ (physicalSpace M)
  | [] => LinearMap.id
  | j::rest => (spatialGenerator M zero closed j).comp (word M zero closed rest)

def multiplier : List Coordinate → IntegerWavevector → ℂ
  | [],_ => 1
  | j::rest,k => NativePhysicalGradient.multiplier k j*multiplier rest k

theorem word_row (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (directions : List Coordinate) (value : physicalSpace M) (k : IntegerWavevector) :
    (word M zero closed directions value).1 k=multiplier directions k • value.1 k := by
  induction directions with
  | nil => simp [word,multiplier]
  | cons j rest ih =>
    change (derivative M zero closed j (word M zero closed rest value)).1 k=_
    rw [derivative_apply,ih,smul_smul]
    rfl

def bracket {M : Finset IntegerWavevector} (D A : Module.End ℝ (physicalSpace M)) := D.comp A-A.comp D

theorem bracket_cons (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (j : Coordinate) (rest : List Coordinate) (A : Module.End ℝ (physicalSpace M)) :
    bracket (word M zero closed (j::rest)) A=
      (spatialGenerator M zero closed j).comp (bracket (word M zero closed rest) A)+
        (bracket (spatialGenerator M zero closed j) A).comp (word M zero closed rest) := by
  ext value
  simp only [bracket,word,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,map_sub]
  abel

theorem action_split (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (directions : List Coordinate) (A : Module.End ℝ (physicalSpace M)) (value forcing : physicalSpace M) :
    word M zero closed directions (A value+forcing)=
      A (word M zero closed directions value)+bracket (word M zero closed directions) A value+
        word M zero closed directions forcing := by
  simp only [bracket,LinearMap.sub_apply,LinearMap.comp_apply,map_add]
  abel

def energy (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) (values : FixedMatterSpatialWordIndex order → physicalSpace M) : ℝ :=
  ∑ index,pairing M (values index) (test seed time M M F radius (values index))

def timeRate (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) (values : FixedMatterSpatialWordIndex order → physicalSpace M) : ℝ :=
  ∑ index,NativeWindowAugmentedTimeForm.quadraticJet seed M F radius 1 time (values index)

theorem energy_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (time : ℝ)
    (M F : Finset IntegerWavevector) (radius : ℕ) (values : FixedMatterSpatialWordIndex order → physicalSpace M) :
    HasDerivAt (fun t => energy seed order t M F radius values) (timeRate seed order time M F radius values) time := by
  simpa only [energy,timeRate,Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ) fun index _ =>
    NativeWindowAugmentedTimeForm.actual_hasDerivAt seed M F radius time (values index)

theorem source_hierarchy_control (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius order,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ time∈Icc 0 horizon,∀ values : FixedMatterSpatialWordIndex order →physicalSpace M,
        (∑ index,pairing M (values index) (values index))+
          (nu.coeff/2)*(∑ index,curlPair M (values index).1 (values index).1)≤
          energy seed order time M (integerWaveFrequencyCube outerRadius) radius values ∧
        |timeRate seed order time M (integerWaveFrequencyCube outerRadius) radius values|≤
          C*energy seed order time M (integerWaveFrequencyCube outerRadius) radius values := by
  obtain ⟨first,coercive⟩ := NativeWindowAugmentedCoercivity.source_coercivity seed horizon nonnegative
  obtain ⟨last,C,C0,temporal⟩ := NativeWindowAugmentedTimeForm.source_time_bound seed horizon nonnegative 1
  refine ⟨max first last,C,C0,fun radius above outerRadius order M zero closed time inside values => ⟨?_,?_⟩⟩
  · have paid := Finset.sum_le_sum (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex order))) fun index _ =>
      coercive radius ((le_max_left first last).trans above) M _ zero closed
        (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside (values index)
    simpa only [energy,Finset.sum_add_distrib,← Finset.mul_sum] using paid
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    have paid := Finset.sum_le_sum (s := (Finset.univ : Finset (FixedMatterSpatialWordIndex order))) fun index _ =>
      temporal radius ((le_max_right first last).trans above) outerRadius M zero closed time inside (values index)
    exact paid.trans_eq (by simp only [energy,Finset.mul_sum])

theorem word_green (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ)
    (M F : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M) (radius : ℕ)
    (advector : ComplexVorticityHilbertState) (reality : FiniteStateFourierReality advector)
    (directions : List Coordinate) (value : physicalSpace M) :
    let A:=physicalOperator M zero closed nu advector reality
    let B:=test seed observation M M F radius
    let D:=word M zero closed directions
    pairing M (D (A value)) (B (D value))+pairing M (D value) (B (D (A value)))=
      pairing M (D value) (lyapunov M zero closed nu advector reality B (D value))+
        pairing M (bracket D A value) (B (D value))+pairing M (D value) (B (bracket D A value)) := by
  dsimp only
  have split := action_split M zero closed directions (physicalOperator M zero closed nu advector reality) value 0
  simp only [add_zero,map_zero] at split
  rw [split]
  simp only [map_add,LinearMap.add_apply]
  rw [← whole_green seed observation M M F zero closed radius advector reality (word M zero closed directions value)]
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowStageNineWords
