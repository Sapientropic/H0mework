import H0mework.Versions.X.NavierStokes.WindowStressHeat.Balance

set_option autoImplicit false
open scoped BigOperators Topology TensorProduct
namespace SaturationMonoid.NavierStokes.NativeWindowCrossHistoryAction
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeWindowStressHeatTime
noncomputable section

abbrev Vector := Coordinate → C(Torus,ℝ)
abbrev Gradient := Coordinate → Vector

def pair (first last : Vector) : C(Torus,ℝ) := ∑ i : Coordinate, first i*last i
def advection (field : Vector) (gradient : Gradient) : Vector := fun i => ∑ j : Coordinate, field j*gradient j i
def crossDerivative (first last : Vector) (firstJet lastJet : Gradient) (j : Coordinate) : C(Torus,ℝ) :=
  pair (firstJet j) last+pair first (lastJet j)
def wedge (first last : Vector) (firstJet lastJet : Gradient) (j : Coordinate) : C(Torus,ℝ) :=
  pair (firstJet j) last-pair first (lastJet j)
def common (first last : Vector) (firstJet lastJet : Gradient) : C(Torus,ℝ) :=
  ∑ j : Coordinate, (first j+last j)*crossDerivative first last firstJet lastJet j
def increment (first last : Vector) (firstJet lastJet : Gradient) : C(Torus,ℝ) :=
  ∑ j : Coordinate, (first j-last j)*wedge first last firstJet lastJet j

theorem convection_split (first last : Vector) (firstJet lastJet : Gradient) :
    pair (advection first firstJet) last+pair first (advection last lastJet) =
      (1/2 : ℝ) • common first last firstJet lastJet+(1/2 : ℝ) • increment first last firstJet lastJet := by
  ext point
  simp only [pair,advection,common,increment,crossDerivative,wedge,Fin.sum_univ_three,
    ContinuousMap.add_apply,ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem action_split (first last firstAction lastAction : Vector) (firstJet lastJet : Gradient) :
    pair firstAction last+pair first lastAction =
      -(1/2 : ℝ) • common first last firstJet lastJet-(1/2 : ℝ) • increment first last firstJet lastJet+
        pair (firstAction+advection first firstJet) last+pair first (lastAction+advection last lastJet) := by
  have commonLaw := convection_split first last firstJet lastJet
  have left : pair (firstAction+advection first firstJet) last = pair firstAction last+pair (advection first firstJet) last := by
    simp only [pair,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  have right : pair first (lastAction+advection last lastJet) = pair first lastAction+pair first (advection last lastJet) := by
    simp only [pair,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  rw [left,right]
  rw [neg_smul]
  linear_combination -commonLaw

variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Vector :=
  fun i => field seed F i time
def gradient (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Gradient :=
  fun j i => NativeWindowStressHeatSource.jetRead F j 1 i (NativeUnifiedCompleteSource.source seed time)
def action (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Vector :=
  fun i => fieldAction seed F i time
def retained (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) : Vector :=
  action seed F time+advection (velocity seed F time) (gradient seed F time)
def pairAction (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) : C(Torus,ℝ) :=
  pair (action seed F first) (velocity seed F last)+pair (velocity seed F first) (action seed F last)

theorem source_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) :
    pairAction seed F first last =
      -(1/2 : ℝ) • common (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last)-
      (1/2 : ℝ) • increment (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last)+
      pair (retained seed F first) (velocity seed F last)+pair (velocity seed F first) (retained seed F last) :=
  action_split _ _ _ _ _ _

theorem retained_original_ae (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) :
    ∀ᵐ time : ℝ, 0 ≤ time → ∀ i,
    retained seed F time i =
      (∑ wave ∈ F, NativeWindowStressHeatBalance.basis wave
        (NativeTimeJetCarrier.projectedDivergenceCLM wave
          (NativeHigherTimeJets.mixedFlux (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst)
            (NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst) wave) i))+
      advection (velocity seed F time) (gradient seed F time) i := by
  filter_upwards [NativeWindowStressHeatBalance.action_original_ae seed F] with time original nonnegative i
  change fieldAction seed F i time+_ = _
  rw [original nonnegative i]

theorem velocity_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ)
    (i j : Coordinate) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => velocity seed F time i (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (gradient seed F time j i (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have original := NativeWindowStressHeatSource.jetRead_line F j 0 i (NativeUnifiedCompleteSource.source seed time) x parameter
  simpa only [NativeWindowStressHeatSource.jetRead_zero,velocity,gradient,field_original] using original

theorem pair_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (j : Coordinate) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => pair (velocity seed F first) (velocity seed F last)
      (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (crossDerivative (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have paid := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    (velocity_derivative seed F first i j x parameter).mul (velocity_derivative seed F last i j x parameter)
  simpa only [pair,crossDerivative,ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    Finset.sum_fn,Pi.mul_apply,Finset.sum_add_distrib] using! paid

theorem native_integrand (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) :
    (∑ output : Coordinate, ∑ input : Coordinate,
      NativeWindowStressHeatTime.product seed F output input last*NativeWindowStressHeatTime.nonlinearPair seed F output input first) =
      (2 : ℝ) • (pair (velocity seed F first) (velocity seed F last)*pair (action seed F first) (velocity seed F last)) := by
  ext point
  simp only [NativeWindowStressHeatTime.product,nonlinearPair,velocity,action,pair,Fin.sum_univ_three,
    ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem symmetric_native_integrand (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ) :
    (1/2 : ℝ) • ((∑ output : Coordinate, ∑ input : Coordinate,
      NativeWindowStressHeatTime.product seed F output input last*nonlinearPair seed F output input first)+
      (∑ output : Coordinate, ∑ input : Coordinate,
      NativeWindowStressHeatTime.product seed F output input first*nonlinearPair seed F output input last)) =
        pair (velocity seed F first) (velocity seed F last)*pairAction seed F first last := by
  rw [native_integrand,native_integrand]
  ext point
  simp only [pair,pairAction,Fin.sum_univ_three,ContinuousMap.add_apply,ContinuousMap.mul_apply,
    ContinuousMap.smul_apply,smul_eq_mul]
  ring

theorem flux_derivative (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (first last : ℝ)
    (j : Coordinate) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => ((velocity seed F first j+velocity seed F last j)*
      pair (velocity seed F first) (velocity seed F last)^2)
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (((gradient seed F first j j+gradient seed F last j j)*pair (velocity seed F first) (velocity seed F last)^2+
        (2 : ℝ) • ((velocity seed F first j+velocity seed F last j)*pair (velocity seed F first) (velocity seed F last)*
          crossDerivative (velocity seed F first) (velocity seed F last) (gradient seed F first) (gradient seed F last) j))
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have paid := ((velocity_derivative seed F first j j x parameter).add
    (velocity_derivative seed F last j j x parameter)).mul ((pair_derivative seed F first last j x parameter).pow 2)
  convert! paid using 1
  simp only [ContinuousMap.add_apply,ContinuousMap.mul_apply,ContinuousMap.pow_apply,ContinuousMap.smul_apply,
    Pi.add_apply,Pi.pow_apply,smul_eq_mul,Nat.cast_ofNat,show (2:ℕ)-1=1 by decide,pow_one]
  ring

theorem gradient_trace_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (time : ℝ) (nonnegative : 0 ≤ time) : (∑ j : Coordinate, gradient seed F time j j) = 0 := by
  ext point
  simp only [gradient,NativeWindowStressHeatSource.jetRead_apply,NativeWindowStressHeatSource.polynomial,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,pow_one,Complex.re_sum,ContinuousMap.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro wave _
  have trans := NativeCompleteVelocityCurl.source_transverse seed time nonnegative wave
  change (∑ j : Coordinate, ThreeDimensionalVorticityCoefficientRawSourceCore.complexWavevector wave j*
    NativeForwardWindowPairingReadout.velocityRead wave j (NativeUnifiedCompleteSource.source seed time)) = 0 at trans
  have complexSum : (∑ j : Coordinate, NativePhysicalGradient.multiplier wave j*
      NativeForwardWindowPairingReadout.velocityRead wave j (NativeUnifiedCompleteSource.source seed time)*UnitAddTorus.mFourier wave point) = 0 := by
    calc
      _ = (Complex.I*(2*Real.pi : ℝ))*(∑ j : Coordinate,
          ThreeDimensionalVorticityCoefficientRawSourceCore.complexWavevector wave j*
            NativeForwardWindowPairingReadout.velocityRead wave j (NativeUnifiedCompleteSource.source seed time))*UnitAddTorus.mFourier wave point := by
        simp only [Finset.sum_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [NativePhysicalGradient.multiplier]
        ring
      _ = 0 := by rw [trans,mul_zero,zero_mul]
  have realPart := congrArg Complex.re complexSum
  simpa only [Complex.re_sum,Complex.zero_re] using realPart

theorem same_time_increment (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (time : ℝ) :
    increment (velocity seed F time) (velocity seed F time) (gradient seed F time) (gradient seed F time) = 0 := by
  simp only [increment,sub_self,zero_mul,Finset.sum_const_zero]

theorem increment_writer (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (first last : ℝ) (first0 : 0 ≤ first) (last0 : 0 ≤ last) (i : Coordinate) :
    velocity seed F last i-velocity seed F first i = ∫ time in first..last, fieldRate seed F i time := by
  change (NativeWindowStressHeatTime.read F i) (NativeUnheatedGlobalNegativeOne.state seed last)-
    (NativeWindowStressHeatTime.read F i) (NativeUnheatedGlobalNegativeOne.state seed first) = _
  rw [← map_sub,NativeUnheatedGlobalNegativeOne.source_integral seed first last first0 last0,
    ← (NativeWindowStressHeatTime.read F i).intervalIntegral_comp_comm
      (NativeUnheatedGlobalNegativeOne.rate_intervalIntegrable seed first last first0 last0)]
  rfl

section HistoryTensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def tensorPair (first last : Coordinate → H) : H ⊗[ℝ] H := ∑ i : Coordinate, first i ⊗ₜ[ℝ] last i

theorem tensorPair_hasDerivAt {path : ℝ → Coordinate → H} {jet : Coordinate → H} {time : ℝ}
    (actual : HasDerivAt path jet time) : HasDerivAt (fun r => tensorPair (path r) (path r))
      (tensorPair jet (path time)+tensorPair (path time) jet) time := by
  have paid := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    ContinuousLinearMap.hasDerivAt_of_bilinear (B := TensorProduct.mkL ℝ H H)
      (fun _ => hasDerivAt_pi.mp actual i) (fun _ => hasDerivAt_pi.mp actual i)
  simpa only [tensorPair,TensorProduct.mkL_apply_apply,Finset.sum_add_distrib,add_comm] using! paid

theorem tensorPair_swap_square (first last : Coordinate → H) : ‖tensorPair first last‖^2 = ‖tensorPair last first‖^2 := by
  simp only [tensorPair,← NativeWindowStressHeatGram.pairing_tensor_square,NativeWindowStressHeatGram.pairing]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem tensor_gradient_energy (value : Coordinate → H) (derivative : Coordinate → Coordinate → H) :
    (∑ j : Coordinate, (‖tensorPair (derivative j) value+tensorPair value (derivative j)‖^2+
      ‖tensorPair (derivative j) value-tensorPair value (derivative j)‖^2)) =
        4*Matrix.trace (NativeWindowStressHeatGram.gram value*NativeWindowStressHeatGram.gradientGram derivative) := by
  rw [NativeWindowStressHeatGram.trace_gradient_square,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [parallelogram_law_with_norm ℝ,tensorPair_swap_square (derivative j) value]
  change 2*(_+_) = 4*‖tensorPair value (derivative j)‖^2
  ring
end HistoryTensor

theorem source_tensor_mass (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (x : PhysicalSpace) :
    ‖tensorPair (NativeWindowFiniteGramSource.value seed time F x) (NativeWindowFiniteGramSource.value seed time F x)‖^2 =
      ∑ i : Coordinate, ∑ j : Coordinate, (NativeWindowFiniteGramSource.stress seed time F x i j)^2 := by
  unfold tensorPair
  rw [← NativeWindowStressHeatGram.pairing_tensor_square]
  simp only [NativeWindowStressHeatGram.pairing,NativeWindowFiniteGramSource.stress,pow_two]

theorem source_tensor_energy (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (x : PhysicalSpace) :
    let v := NativeWindowFiniteGramSource.value seed time F x
    let d := NativeWindowFiniteGramSource.gradient seed time F x
    (∑ j : Coordinate, (‖tensorPair (d j) v+tensorPair v (d j)‖^2+‖tensorPair (d j) v-tensorPair v (d j)‖^2)) =
      4*NativeWindowStressHeatSource.interaction seed time F (NativeFullOrderSynthesis.circlePoint x) := by
  rw [NativeWindowStressHeatSource.interaction_physical]
  exact tensor_gradient_energy _ _

theorem source_tensor_derivative (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector)
    (x : PhysicalSpace) (direction : Coordinate) (parameter : ℝ) :
    let v := fun r => NativeWindowFiniteGramSource.value seed time F (NativeWindowFiniteGramSource.line x direction r)
    let d := NativeWindowFiniteGramSource.gradient seed time F (NativeWindowFiniteGramSource.line x direction parameter) direction
    HasDerivAt (fun r => tensorPair (v r) (v r)) (tensorPair d (v parameter)+tensorPair (v parameter) d) parameter :=
  tensorPair_hasDerivAt (NativeWindowFiniteGramSource.value_derivative seed time F x direction parameter)

end
end SaturationMonoid.NavierStokes.NativeWindowCrossHistoryAction
