import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerTranslation
import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerBound
import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.CanonicalAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWeakLowerReadback
open MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open NativePhysicalFourier (Torus)
open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open NativeWindowGreenTestForm (SpinFiber)
open NativeWindowAbsoluteLowerBound (Full)
open NativeWindowAbsoluteTimeCanonicalAction (coordinateBasis)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def read : Full E →L[ℂ] SpinFiber E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 × Fin 2 => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => ∑ output : MatterCoordinateIndex,
      NativeMaterialReadback.coefficient entry.1 entry.2 (coordinateBasis output) •
        PiLp.proj (𝕜 := ℂ) 2 (fun _ : MatterCoordinateIndex => E) output)

theorem read_apply (v : Full E) (entry : Fin 4 × Fin 2) :
    read (E := E) v entry=∑ output : MatterCoordinateIndex,
      NativeMaterialReadback.coefficient entry.1 entry.2 (coordinateBasis output) • v output := by
  simp [read]

def lift (L : Module.End ℂ DiracExteriorMatterCarrier) : SpinFiber E →L[ℂ] Full E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : MatterCoordinateIndex => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun output => ∑ entry : Fin 4 × Fin 2,
      matterCoordinateEquiv (L (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)) output •
        PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 × Fin 2 => E) entry)

theorem lift_original (L : Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) :
    lift (E := E) L v=NativeWindowAbsoluteLowerBound.lift L v := by
  apply PiLp.ext
  intro output
  simp [lift,NativeWindowAbsoluteLowerBound.lift]

theorem read_original (v : NativeWindowAbsoluteTimePhysicalMatter.WholeMatter) (spin : Fin 4) (color : Fin 2) :
    read (E := NativeWindowAbsoluteTimeFourier.Fiber) (WithLp.toLp 2 v) (spin,color)=NativeWindowAbsoluteTimeCanonicalAction.read spin color v := by
  rw [read_apply]
  rfl

def readCap : ℝ := ∑ entry : Fin 4 × Fin 2,∑ output : MatterCoordinateIndex,
  ‖NativeMaterialReadback.coefficient entry.1 entry.2 (coordinateBasis output)‖

theorem readCap_nonnegative : 0 ≤ readCap :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem read_norm (v : Full E) : ‖read (E := E) v‖ ≤ readCap*‖v‖ := by
  have l1:‖read (E := E) v‖ ≤ ∑ entry : Fin 4 × Fin 2,‖read (E := E) v entry‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  apply l1.trans
  simp only [read_apply,readCap,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro entry _
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun output _ => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v output) (norm_nonneg _)

def operator (L : Module.End ℂ DiracExteriorMatterCarrier) : SpinFiber E →L[ℂ] SpinFiber E :=
  (read (E := E)).comp (lift (E := E) L)

theorem operator_original (L : Module.End ℂ DiracExteriorMatterCarrier)
    (v : NativeWindowAbsoluteTimePhysicalMatter.Spinor) (spin : Fin 4) (color : Fin 2) :
    operator (E := NativeWindowAbsoluteTimeFourier.Fiber) L (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => v entry.1 entry.2)) (spin,color)=
      NativeWindowAbsoluteTimeCanonicalAction.read spin color (NativeWindowAbsoluteTimePhysicalMatter.extension L v) := by
  rw [operator,ContinuousLinearMap.comp_apply,lift_original,NativeWindowAbsoluteLowerBound.lift_original,read_original]

section Norms
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem inner_young (u v : G) (epsilon : ℝ) (positive : 0<epsilon) :
    ‖inner ℂ u v‖ ≤ epsilon*‖u‖^2+(4*epsilon)⁻¹*‖v‖^2 := by
  apply (norm_inner_le_norm u v).trans
  apply (mul_le_mul_iff_left₀ (show 0<4*epsilon by positivity)).mp
  have scalar : (epsilon*‖u‖^2+(4*epsilon)⁻¹*‖v‖^2)*(4*epsilon)=4*epsilon^2*‖u‖^2+‖v‖^2 := by
    field_simp [positive.ne']
  rw [scalar]
  nlinarith only [sq_nonneg (2*epsilon*‖u‖-‖v‖)]

theorem two_test_absorption (p dp bq bp : G) (K A D epsilon : ℝ) (K0 : 0 ≤ K) (D0 : 0 ≤ D)
    (positive : 0<epsilon) (pMass : ‖p‖^2 ≤ A) (derivative : ‖dp‖^2 ≤ D)
    (zeroWord : ‖bq‖^2 ≤ K) (oneWord : ‖bp‖^2 ≤ K*(A+D)) :
    ‖-inner ℂ dp bq-inner ℂ p bp‖ ≤ epsilon*D+
      (2*epsilon)⁻¹*K+(epsilon/(2*(K+1))*K+(4*(epsilon/(2*(K+1))))⁻¹)*A := by
  let delta:=epsilon/(2*(K+1))
  have delta0:0<delta:=by dsimp only [delta]; positivity
  have coefficient:delta*K ≤ epsilon/2 := by
    dsimp only [delta]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0<2*(K+1) by positivity)).mpr
    nlinarith
  have first:‖inner ℂ dp bq‖ ≤ epsilon/2*D+(2*epsilon)⁻¹*K := by
    have paid:=inner_young dp bq (epsilon/2) (by positivity)
    have same:4*(epsilon/2)=2*epsilon:=by ring
    rw [same] at paid
    exact paid.trans (add_le_add (mul_le_mul_of_nonneg_left derivative (by positivity))
      (mul_le_mul_of_nonneg_left zeroWord (by positivity)))
  have last:‖inner ℂ p bp‖ ≤ delta*K*(A+D)+(4*delta)⁻¹*A := by
    rw [norm_inner_symm]
    exact (inner_young bp p delta delta0).trans (by
      have paid:=add_le_add (mul_le_mul_of_nonneg_left oneWord delta0.le)
        (mul_le_mul_of_nonneg_left pMass (by positivity : 0 ≤ (4*delta)⁻¹))
      nlinarith only [paid])
  have paid:‖-inner ℂ dp bq-inner ℂ p bp‖ ≤ ‖inner ℂ dp bq‖+‖inner ℂ p bp‖ := by
    simpa only [norm_neg] using norm_sub_le (-inner ℂ dp bq) (inner ℂ p bp)
  have total:=mul_le_mul_of_nonneg_right coefficient D0
  change _ ≤ epsilon*D+(2*epsilon)⁻¹*K+(delta*K+(4*delta)⁻¹)*A
  nlinarith only [first,last,paid,total]

end Norms
end
end SaturationMonoid.NavierStokes.NativeWindowWeakLowerReadback
