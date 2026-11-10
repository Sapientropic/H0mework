import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPhysicalQuarterResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.CompleteSourceNoetherPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronQuarterSourceMatching
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumActionFieldLift PreparationVacuumSourcePreparedResponse
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSourcePreparation
open ActualElectronWholeNoetherObserver ActualElectronFullNoetherMixedSoft ActualElectronPhysicalJointInverse
open ActualMixedNoetherTimePriceOwn ActualDressedSignal GaussComposite.SourceGraph
open SaturationMonoid.PhysicsCore.LowEnergy.ThresholdWindow
open SaturationMonoid.PhysicsCore.LowEnergy.EulerDiagonal
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] actualFullNoetherVariation dressedEulerObserver actualPhysicalEulerObserver
  actualElectronPhysicalState actualNoetherBackground sourceDressedUnit sourceProfile prepared

/-- The two actual preparations use the same full operator and the unchanged original background. -/
def actualPhysicalObserverChange (event : DressedEvent) (leg : CompositeLeg) : (H→L[ℂ]H)→L[ℂ]ℂ :=
  actualPhysicalEulerObserver event leg-dressedEulerObserver event

theorem actual_observer_change_same_operator (event : DressedEvent) (leg : CompositeLeg) (A : H→L[ℂ]H) :
    actualPhysicalEulerObserver event leg A=dressedEulerObserver event A+actualPhysicalObserverChange event leg A := by
  simp only [actualPhysicalObserverChange,sub_apply]
  abel

private theorem embedded_background_read {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : Ultrafilter I) (A : E→L[ℂ]E) (b : E) :
    inner ℂ (SourceFamilyHilbert.embed u b)
      (SourceFamilyOperator.lift u (SourceFamilyOperator.constant A) (SourceFamilyHilbert.embed u b))=inner ℂ b (A b) := by
  rw [SourceFamilyOperator.lift_constant_embed,(SourceFamilyHilbert.embed u).inner_map_map]

private theorem same_background_subtract (x y b c : ℂ) (paid : b=c) :
    (-x+b)-(-y+c)= -x+y := by rw [paid];abel

theorem actual_observer_change_background_cancels (event : DressedEvent) (leg : CompositeLeg) (A : H→L[ℂ]H) :
    actualPhysicalObserverChange event leg A=
      -inner ℂ (actualElectronPhysicalState event.momentum event.energy event.nonreal leg)
        (GaussUnitaryHistory.reader A (actualElectronPhysicalState event.momentum event.energy event.nonreal leg))+
      inner ℂ (sourceDressedUnit event.epsilon event.precision) (A (sourceDressedUnit event.epsilon event.precision)) := by
  have background : inner ℂ (actualNoetherBackground event)
      (GaussUnitaryHistory.reader A (actualNoetherBackground event))=
        inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (A (prepared (sourceProfile event.epsilon event.precision))) := by
    simpa only [actualNoetherBackground,GaussUnitaryHistory.reader,GaussUnitaryHistory.inclusion] using!
      embedded_background_read GaussUnitaryHistory.sourceFilter A (prepared (sourceProfile event.epsilon event.precision))
  have observed:=congrArg₂ (fun x y : ℂ=>x-y)
    (actual_physical_euler_observer_value event leg A) (dressed_euler_observer_original event A)
  have value : actualPhysicalObserverChange event leg A=
      actualPhysicalEulerObserver event leg A-dressedEulerObserver event A:=rfl
  exact value.trans (observed.trans (same_background_subtract _ _ _ _ background))

theorem actual_original_jet_same_operator (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) (i : Fin 289) :
    dressedEulerObserver event (actualFullNoetherVariation event transfer (fieldUnit i) force age)=
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value := by
  have actual:=((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actual_full_noether_kernel_field_generated event transfer (fieldUnit i) force age)
  exact actual.unique (dressed_noether_action_derivative event transfer force age i)

def actualOriginalQuarterResponse (event : DressedEvent) (transfer : PhysicalMomentum)
    (test : TimeTest) (damping : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>dressedEulerObserver event (actualQuarterOperator event transfer (fieldUnit i) (fieldUnit j) test damping)

def actualQuarterObserverChange (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum)
    (test : TimeTest) (damping : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>actualPhysicalObserverChange event leg (actualQuarterOperator event transfer (fieldUnit i) (fieldUnit j) test damping)

theorem actual_quarter_same_event_return (event : DressedEvent) (leg : CompositeLeg) (transfer : PhysicalMomentum)
    (test : TimeTest) (damping : ℝ) :
    actualPhysicalQuarterResponse event leg transfer test damping=
      actualOriginalQuarterResponse event transfer test damping+actualQuarterObserverChange event leg transfer test damping := by
  funext i j
  exact actual_observer_change_same_operator event leg _

theorem actual_original_quarter_jet (event : DressedEvent) (transfer : PhysicalMomentum)
    (test : TimeTest) (damping : ℝ) (i j : Fin 289) :
    actualOriginalQuarterResponse event transfer test damping i j=
      ((M0 test damping)⁻¹:ℂ)*∫t, (momentDensity test damping t:ℂ)*
        (dressedNoetherJet event transfer (fun _=>⟨fieldUnit j,0,0⟩) t i).value := by
  have original:=source_quarter_observation_integral (dressedEulerObserver event) test damping
    (actualFullNoetherVariation event transfer (fieldUnit i) (fieldUnit j))
    (actual_full_response_time_continuous event transfer (fieldUnit i) (fieldUnit j))
  simpa only [actualOriginalQuarterResponse,actualQuarterOperator,actual_original_jet_same_operator] using original

theorem actual_quarter_observer_change_source_price (event : DressedEvent) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (test : TimeTest) (window : QuarterContract test) (damping : ℝ) (i j : Fin 289) :
    ‖actualQuarterObserverChange event leg transfer test damping i j‖≤
      4*actualQuarterSourceMoment event transfer (fieldUnit i) (fieldUnit j) test damping := by
  let A:=actualQuarterOperator event transfer (fieldUnit i) (fieldUnit j) test damping
  have newBound:=actual_physical_observer_operator_price event leg A
  have oldBound:=((dressedEulerObserver event).le_opNorm A).trans
    (mul_le_mul_of_nonneg_right (dressed_euler_observer_price event) (norm_nonneg A))
  have opBound:=actual_quarter_operator_source_price event transfer (fieldUnit i) (fieldUnit j) test window damping
  change ‖actualPhysicalEulerObserver event leg A-dressedEulerObserver event A‖≤_
  exact ((norm_sub_le _ _).trans (add_le_add newBound oldBound)).trans (by nlinarith)

private theorem normalized_integral_price (density : ℝ→ℝ) (dContinuous : Continuous density)
    (compact : HasCompactSupport density) (mass : ℝ) (positive : 0 < mass) (massEq : ∫t,density t=mass)
    (densityNonnegative : ∀t,0≤density t) (f : ℝ→ℂ) (continuous : Continuous f) (B : ℝ)
    (bound : ∀t,density t*‖f t‖≤density t*B) :
    ‖(mass:ℂ)⁻¹*∫t,(density t:ℂ)*f t‖≤B := by
  have complexCompact : HasCompactSupport (fun t=>(density t:ℂ)):=by
    simpa only [Function.comp_def] using compact.comp_left (g:=Complex.ofReal) rfl
  have integrable : Integrable (fun t=>(density t:ℂ)*f t) volume:=
    ((Complex.continuous_ofReal.comp dContinuous).mul continuous).integrable_of_hasCompactSupport
    complexCompact.mul_right
  have majorant : Integrable (fun t=>density t*B) volume:=
    (dContinuous.integrable_of_hasCompactSupport compact).mul_const B
  have point (t : ℝ) : ‖(density t:ℂ)*f t‖≤density t*B := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (densityNonnegative t)] using bound t
  have integralBound:=(norm_integral_le_integral_norm (μ:=volume) _).trans (integral_mono integrable.norm majorant point)
  rw [integral_mul_const,massEq] at integralBound
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  calc
    _ ≤ mass⁻¹*(mass*B):=mul_le_mul_of_nonneg_left integralBound (inv_nonneg.mpr positive.le)
    _=B:=by rw [←mul_assoc,inv_mul_cancel₀ positive.ne',one_mul]

private theorem quarter_average_price (test : TimeTest) (window : QuarterContract test) (damping : ℝ)
    (f : ℝ→ℂ) (continuous : Continuous f) (B : ℝ)
    (bound : ∀t,test.cutoff t≠0→‖f t‖≤B) :
    ‖((M0 test damping)⁻¹:ℂ)*∫t,(momentDensity test damping t:ℂ)*f t‖≤B := by
  apply normalized_integral_price (momentDensity test damping) (momentDensity_continuous test damping)
    (momentDensity_compact test damping) (M0 test damping) (M0_pos test window damping) rfl
    (momentDensity_nonneg test damping) f continuous B
  intro t
  by_cases zero : test.cutoff t=0
  · simp [momentDensity,zero]
  · exact mul_le_mul_of_nonneg_left (bound t zero) (momentDensity_nonneg test damping t)

theorem actual_original_quarter_source_cubic_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (test : TimeTest) (window : QuarterContract test) (damping : ℝ) (i j : Fin 289) :
    ‖actualOriginalQuarterResponse event transfer test damping i j‖≤
      (1331/512:ℝ)*sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) := by
  rw [actual_original_quarter_jet]
  have continuous:=(dressed_noether_jet_continuous event transfer (fun _=>⟨fieldUnit j,0,0⟩)
    ⟨continuous_const,continuous_const,continuous_const⟩ i).1
  apply quarter_average_price test window damping _ continuous _
  intro t nonzero
  have interval:=window.1 (subset_closure (show t∈Function.support test.cutoff from nonzero))
  have positiveTime : 0≤t:=le_trans (by norm_num : (0:ℝ)≤1/8) interval.1
  have timeBound : (1+|t|)^3≤(1331/512:ℝ) := by
    rw [abs_of_nonneg positiveTime]
    have power:=pow_le_pow_left₀ (by linarith : 0≤1+t) (by linarith [interval.2] : 1+t≤(11/8:ℝ)) 3
    norm_num at power ⊢
    exact power
  exact (actual_complete_noether_source_price event transfer (fieldUnit j) t i).trans
    ((mul_le_mul_of_nonneg_left timeBound (sourceCompleteCubicNoetherPrice_nonnegative event transfer _ _)).trans_eq (mul_comm _ _))

theorem actual_physical_quarter_original_plus_change_price (event : DressedEvent) (leg : CompositeLeg)
    (transfer : PhysicalMomentum) (test : TimeTest) (window : QuarterContract test) (damping : ℝ) (i j : Fin 289) :
    ‖actualPhysicalQuarterResponse event leg transfer test damping i j‖≤
      (1331/512:ℝ)*sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)+
      4*actualQuarterSourceMoment event transfer (fieldUnit i) (fieldUnit j) test damping := by
  rw [actual_quarter_same_event_return]
  exact (norm_add_le _ _).trans (add_le_add
    (actual_original_quarter_source_cubic_price event transfer test window damping i j)
    (actual_quarter_observer_change_source_price event leg transfer test window damping i j))

end LowEnergy.GaussComposite.ActualElectronQuarterSourceMatching
