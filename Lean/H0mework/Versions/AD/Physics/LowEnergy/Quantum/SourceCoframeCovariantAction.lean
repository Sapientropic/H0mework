import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCoframeSpinConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoframeCovariantAction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeCore GaussCoframeKinetic GaussCoframeForm SourceCoframeSpinConnection
open scoped ContDiff Matrix InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem beta_smooth (i : Fin 6) (a : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w : SourceCoordinateSlice => spinConnection w.1 i a) z.val := by
  have hv := (volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5 ≠ 0 at hv
  have h0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).1
  have h2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv).1).2
  have h5 := (mul_ne_zero_iff.mp hv).2
  fin_cases i <;> fin_cases a <;> simp [spinConnection] <;> fun_prop (disch := aesop)

private theorem fiber_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (connectionFiber i) z.val :=
  ContDiffAt.sum (fun a _ => (beta_smooth i a z).smul contDiffAt_const)

def connectionAction (i : Fin 6) : End := localMultiplier (connectionFiber i) (fiber_smooth i)
def metricAction (i j : Fin 6) : End := multiply (coefficient i j) (coefficient_smooth i j)
def rotationAction (a : Fin 3) : End := GaussCoframeSpin.current ⟨3+a.val,by omega⟩

private theorem local_value (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hs : ∀z : physicalChart,ContDiffAt ℝ ∞ A z.val) (f : QuantumTest) (z : SourceCoordinateSlice) :
    localMultiplier A hs f z=A z (f z) := rfl

private theorem real_smul_fiber (c : ℝ) (v : FockFiber) : c • v=(c : ℂ) • v := by
  apply PiLp.ext
  intro w
  exact Complex.real_smul.symm

private theorem connection_columns (i : Fin 6) :
    connectionAction i=∑ a : Fin 3,multiply (fun z => spinConnection z.1 i a) (beta_smooth i a)*rotationAction a := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (connectionFiber i z) (f z)=_
  simp only [connectionFiber,sum_apply,smul_apply,real_smul_fiber,LinearMap.sum_apply,Module.End.mul_apply]
  rfl

private theorem rotation_real (a : Fin 3) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    Commute (rotationAction a) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (SourceCoframeSpinConnection.rotation a).map_smul (c z : ℂ) (f z)

/-- The connection uses the original Number-weighted formal pairing. -/
theorem original_connection_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (connectionAction i g)=sourcePair (connectionAction i f) g := by
  rw [connection_columns]
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro a _
  change sourcePair f (multiply _ _ (rotationAction a g))=sourcePair (multiply _ _ (rotationAction a f)) g
  have hr (p q : QuantumTest) : sourcePair p (rotationAction a q)=sourcePair (rotationAction a p) q :=
    GaussCoframeSpin.current_pair _ p q
  rw [multiply_pair,hr]
  have h := LinearMap.congr_fun (rotation_real a (fun z => spinConnection z.1 i a) (beta_smooth i a)).eq f
  change rotationAction a (multiply (fun z => spinConnection z.1 i a) (beta_smooth i a) f)=
    multiply (fun z => spinConnection z.1 i a) (beta_smooth i a) (rotationAction a f) at h
  rw [h]

private theorem fiber_row (z : physicalChart) (i : Fin 6) :
    (∑ j : Fin 6,coefficient i j z.val • connectionFiber j z.val)=
      (inverseVolume z.val/2) • (∑ a : Fin 3,currentRows z.val.1 i a • SourceCoframeSpinConnection.rotation a) := by
  simp only [connectionFiber,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_smul]
  simp_rw [original_metric_connection]

def currentRow (i : Fin 6) : End :=
  ![0,multiply (currentCoefficient 0) (currentCoefficient_smooth 0)*GaussCoframeSpin.current 5,
    0,multiply (currentCoefficient 1) (currentCoefficient_smooth 1)*GaussCoframeSpin.current 3+
      multiply (fun z => -currentCoefficient 0 z) (fun z => (currentCoefficient_smooth 0 z).neg)*GaussCoframeSpin.current 4,
    multiply (currentCoefficient 2) (currentCoefficient_smooth 2)*GaussCoframeSpin.current 3,0] i

/-- The metric-contracted original connection recovers each of the four mixed source rows. -/
theorem original_connection_row (i : Fin 6) :
    (∑ j : Fin 6,metricAction i j*connectionAction j)=(1/2 : ℂ) • currentRow i := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have h := congrArg (fun A : FiberEnd => A (f z)) (fiber_row ⟨z,hz⟩ i)
    simp only [sum_apply,smul_apply,real_smul_fiber] at h
    change (∑ j : Fin 6,(coefficient i j z : ℂ) • (connectionFiber j z (f z)))=_ at h
    simp only [LinearMap.sum_apply,Module.End.mul_apply]
    change (∑ j : Fin 6,(coefficient i j z : ℂ) • (connectionFiber j z (f z)))=_
    rw [h]
    fin_cases i <;> simp [currentRow,currentRows,SourceCoframeSpinConnection.rotation,GaussCoframeSpin.current,
      GaussQuantumMultiplier.action,currentCoefficient,Fin.sum_univ_succ,multiply_apply,local_value,smul_add]
    all_goals simp only [real_smul_fiber,smul_smul]
    all_goals module
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

def covariantMomentum (i : Fin 6) : End := momentum i+connectionAction i
def covariantAdjoint (i : Fin 6) : End := adjoint i+connectionAction i

theorem original_covariant_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (covariantMomentum i g)=sourcePair (covariantAdjoint i f) g := by
  simp only [covariantMomentum,covariantAdjoint,LinearMap.add_apply,sourcePair,map_add,inner_add_right,inner_add_left]
  exact congrArg₂ (·+·) (momentum_pair i f g) (original_connection_pair i f g)

def covariantKinetic : End := ∑ i : Fin 6,∑ j : Fin 6,covariantAdjoint i*metricAction i j*covariantMomentum j

def connectionSquare : End := ∑ i : Fin 6,∑ j : Fin 6,connectionAction i*metricAction i j*connectionAction j

def rotationSquare : End := ∑ a : Fin 3,rotationAction a*multiply inverseVolume inverseVolume_smooth*rotationAction a

/-- The pointwise CAR square is now the exact operator on the original compact core. -/
theorem original_connection_square : connectionSquare=(-1/4 : ℂ) • rotationSquare := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · have h := congrArg (fun A : FiberEnd => A (f z)) (original_connection_fiber_square ⟨z,hz⟩)
    simp only [sum_apply,smul_apply,mul_apply_eq_comp,real_smul_fiber] at h
    simp only [connectionSquare,rotationSquare,LinearMap.sum_apply,Module.End.mul_apply,LinearMap.smul_apply]
    change (∑ i : Fin 6,∑ j : Fin 6,connectionFiber i z ((coefficient i j z : ℂ) • (connectionFiber j z (f z))))=_
    simp only [map_smul]
    rw [h]
    change ((-inverseVolume z/4 : ℝ) : ℂ) • (∑ a : Fin 3,SourceCoframeSpinConnection.rotation a (SourceCoframeSpinConnection.rotation a (f z)))=
      (-1/4 : ℂ) • (∑ a : Fin 3,SourceCoframeSpinConnection.rotation a ((inverseVolume z : ℂ) • SourceCoframeSpinConnection.rotation a (f z)))
    simp only [map_smul,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    push_cast
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

end LowEnergy.SourceCoframeCovariantAction
