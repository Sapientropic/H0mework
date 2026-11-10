import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPhysicalFullResponseRay
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualElectronQuarterSourceMatchingOwn.ThresholdWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronQuarterSourceMatching
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumNoetherChart
open PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumFieldPerturbation.Blocks
open ActualCompositeFieldCurrent
open ActualDressedFullCoulomb ActualDressedNoether ActualElectronWholeNoetherObserver
open ActualElectronFullNoetherMixedSoft MeasureTheory Set
open SaturationMonoid.PhysicsCore.LowEnergy.ThresholdWindow
open SaturationMonoid.PhysicsCore.LowEnergy.EulerDiagonal
open scoped Topology InnerProductSpace
local instance rationalOperators : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
local instance realOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance operatorNorm : NormedAddCommGroup (H→L[ℂ]H):=ContinuousLinearMap.toNormedAddCommGroup
local instance operatorRealSpace : NormedSpace ℝ (H→L[ℂ]H):=realOperators.toNormedSpace
attribute [local irreducible] actualPhysicalEulerObserver actualFullNoetherVariation physicalTime timeSlope jointGenerator jointCurrent

private theorem variation_time {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (C B : E→L[ℂ]E) : Continuous (CanonicalGradedVariation.variation C B) := by
  let : Fact ((1:ENNReal)≤2):=⟨by norm_num⟩
  let : NormedAddCommGroup (Channel E):=WithLp.instProdNormedAddCommGroup 2 E E
  let : NormedSpace ℂ (Channel E):=WithLp.instProdNormedSpace 2 ℂ E E
  let : InnerProductSpace ℂ (Channel E):=WithLp.instProdInnerProductSpace
  let realChannel : NormedAlgebra ℝ (Channel E→L[ℂ]Channel E):=NormedAlgebra.restrictScalars ℝ ℂ _
  let : NormedAddCommGroup (Channel E→L[ℂ]Channel E):=ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (Channel E→L[ℂ]Channel E):=realChannel.toNormedSpace
  let : NormedAlgebra ℚ (Channel E→L[ℂ]Channel E):=NormedAlgebra.restrictScalars ℚ ℂ _
  have exponential : Continuous (SourceFiniteUnitary.time (diagonal C C+upper B)) :=
    continuous_iff_continuousAt.mpr (fun t=>
      (hasDerivAt_exp_smul_const ((-Complex.I) • (diagonal C C+upper B)) t).continuousAt)
  have observed:=(corner (E:=E)).continuous.comp exponential
  have identity (t : ℝ) : corner (SourceFiniteUnitary.time (diagonal C C+upper B) t)=
      CanonicalGradedVariation.variation C B t := by
    have paid:=triangular_time C C B (1:ℂ) t
    simp only [one_smul] at paid
    rw [paid,map_add,corner_diagonal,corner_upper,zero_add,crossTime_integral]
    simp only [CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,zero_smul,add_zero]
  exact observed.congr identity

theorem actual_full_response_time_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) : Continuous (actualFullNoetherVariation event transfer reader force) := by
  have time (p : PhysicalMomentum) : Continuous (fun t : ℝ=>physicalTime p event.frame t 0) := by
    unfold physicalTime SourceFiniteUnitary.time
    exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
  have slope (p : PhysicalMomentum) : Continuous (timeSlope force p event.frame) := by
    unfold timeSlope
    exact variation_time _ _
  have TL:=(time (event.momentum-transfer)).comp continuous_neg
  have dTL:=(slope (event.momentum-transfer)).comp continuous_neg
  have TR:=time event.momentum
  have dTR:=slope event.momentum
  have L : Continuous (fun _ : ℝ=>jointResolvent (event.momentum-transfer) event.frame event.energy 0):=continuous_const
  have R : Continuous (fun _ : ℝ=>jointResolvent event.momentum event.frame event.energy 0):=continuous_const
  have J : Continuous (fun _ : ℝ=>noetherReader reader event.momentum event.frame 0):=continuous_const
  have dJ : Continuous (fun _ : ℝ=>noetherReaderContact reader force event.momentum event.frame):=continuous_const
  have dL : Continuous (fun _ : ℝ=>-(jointResolvent (event.momentum-transfer) event.frame event.energy 0*
    jointCurrent (event.momentum-transfer) event.frame event.energy 0 force*
    jointResolvent (event.momentum-transfer) event.frame event.energy 0)):=continuous_const
  have dR : Continuous (fun _ : ℝ=>-(jointResolvent event.momentum event.frame event.energy 0*
    jointCurrent event.momentum event.frame event.energy 0 force*jointResolvent event.momentum event.frame event.energy 0)):=continuous_const
  have generated:=(((((dTL.mul L).add (TL.mul dL)).mul J).add ((TL.mul L).mul dJ)).mul R |>.add
    (((TL.mul L).mul J).mul dR)).mul TR |>.add ((((TL.mul L).mul J).mul R).mul dTR)
  unfold actualFullNoetherVariation
  convert! generated using 1

private theorem weighted_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (test : TimeTest) (damping : ℝ) (f : ℝ→E) (continuous : Continuous f) :
    Integrable (fun t=>momentDensity test damping t • f t) :=
  ((momentDensity_continuous test damping).smul continuous).integrable_of_hasCompactSupport
    ((momentDensity_compact test damping).smul_right)

/-- The original test window consumes the whole five-factor source operator, before any observer. -/
def actualQuarterOperator (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289)
    (test : TimeTest) (damping : ℝ) : H→L[ℂ]H :=
  (M0 test damping)⁻¹ • ∫t, momentDensity test damping t • actualFullNoetherVariation event transfer reader force t

/-- Exact source moment; its integrand is the complete original operator, not an assumed response envelope. -/
def actualQuarterSourceMoment (event : DressedEvent) (transfer : PhysicalMomentum) (reader force : Field289)
    (test : TimeTest) (damping : ℝ) : ℝ :=
  (∫t, momentDensity test damping t * ‖actualFullNoetherVariation event transfer reader force t‖) / M0 test damping

private theorem source_moment_nonnegative {E : Type*} [NormedAddCommGroup E]
    (test : TimeTest) (damping : ℝ) (f : ℝ→E) (positive : 0<M0 test damping) :
    0≤(∫t,momentDensity test damping t*‖f t‖)/M0 test damping :=
  div_nonneg (integral_nonneg (fun t=>mul_nonneg (momentDensity_nonneg test damping t) (norm_nonneg _))) positive.le

private theorem quarter_average_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (test : TimeTest) (damping : ℝ) (f : ℝ→E) (positive : 0<M0 test damping) :
    ‖(M0 test damping)⁻¹ • ∫t,momentDensity test damping t • f t‖≤
      (∫t,momentDensity test damping t*‖f t‖)/M0 test damping := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos positive,div_eq_mul_inv]
  have bound:=norm_integral_le_integral_norm (μ:=volume) (fun t=>momentDensity test damping t • f t)
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (momentDensity_nonneg test damping _)] at bound
  exact (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positive.le)).trans_eq (mul_comm _ _)

theorem actual_quarter_source_moment_nonnegative (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    0≤actualQuarterSourceMoment event transfer reader force test damping :=
  source_moment_nonnegative test damping _ (M0_pos test window damping)

theorem actual_quarter_operator_source_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (reader force : Field289) (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    ‖actualQuarterOperator event transfer reader force test damping‖≤
      actualQuarterSourceMoment event transfer reader force test damping :=
  quarter_average_norm test damping _ (M0_pos test window damping)

def actualPhysicalQuarterResponse (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum)
    (test : TimeTest) (damping : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>actualPhysicalEulerObserver event leg
    (actualQuarterOperator event transfer (fieldUnit i) (fieldUnit j) test damping)

theorem source_quarter_observation_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L : E→L[ℂ]ℂ) (test : TimeTest) (damping : ℝ) (f : ℝ→E) (continuous : Continuous f) :
    L ((M0 test damping)⁻¹ • ∫t,momentDensity test damping t • f t)=
      ((M0 test damping)⁻¹:ℂ)*∫t,(momentDensity test damping t:ℂ)*L (f t) := by
  have paid:=weighted_integrable test damping f continuous
  have scalar (r : ℝ) (x : E) : L (r • x)=(r:ℂ)*L x := by
    simpa only [ContinuousLinearMap.coe_restrictScalars',Complex.real_smul] using (L.restrictScalars ℝ).map_smul r x
  rw [scalar,←ContinuousLinearMap.integral_comp_comm _ paid]
  simp only [scalar,Complex.ofReal_inv]

theorem actual_physical_quarter_integral (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum)
    (reader force : Field289) (test : TimeTest) (damping : ℝ) :
    actualPhysicalEulerObserver event leg (actualQuarterOperator event transfer reader force test damping)=
      ((M0 test damping)⁻¹:ℂ)*∫t, (momentDensity test damping t:ℂ)*
        actualPhysicalEulerObserver event leg (actualFullNoetherVariation event transfer reader force t) :=
  source_quarter_observation_integral (actualPhysicalEulerObserver event leg) test damping _
    (actual_full_response_time_continuous event transfer reader force)

theorem actual_physical_quarter_all289_price (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum)
    (test : TimeTest) (window : QuarterContract test) (damping : ℝ) (i j : Fin 289) :
    ‖actualPhysicalQuarterResponse event leg transfer test damping i j‖≤
      2*actualQuarterSourceMoment event transfer (fieldUnit i) (fieldUnit j) test damping :=
  (actual_physical_observer_operator_price event leg _).trans
    (mul_le_mul_of_nonneg_left (actual_quarter_operator_source_price event transfer _ _ test window damping) (by norm_num))

end LowEnergy.GaussComposite.ActualElectronQuarterSourceMatching
