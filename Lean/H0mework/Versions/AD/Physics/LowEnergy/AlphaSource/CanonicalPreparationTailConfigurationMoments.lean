import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailPositionJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailSupport
open PreparationVacuumWholeTail PreparationVacuumLocalizedTail PreparationVacuumCanonicalMoyal
open PreparationVacuumWeyl PreparationVacuumClockSymbol PreparationPhaseSource
open PreparationVacuumEngineSource PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory
open scoped BigOperators ContDiff Topology

abbrev ConfigurationExponent := Fin 100 → ℕ

def configurationMonomial (a : ConfigurationExponent) (z : FlatConfiguration) : ℝ :=
  ∏ i : Fin 100,z i^a i

def configurationMomentSize (a : ConfigurationExponent) : ℝ :=
  ∏ i : Fin 100,(|flatSource i|+sourceRadius)^a i

theorem configurationMonomial_continuous (a : ConfigurationExponent) :
    Continuous (configurationMonomial a) :=
  continuous_finsetProd _ (fun i _=>(continuous_apply i).pow (a i))

theorem configurationMomentSize_nonnegative (a : ConfigurationExponent) : 0 ≤ configurationMomentSize a :=
  Finset.prod_nonneg (fun _i _=>pow_nonneg (add_nonneg (abs_nonneg _) radius_small.1.le) _)

theorem configurationMonomial_bound (a : ConfigurationExponent) (z : FlatConfiguration)
    (box : z∈thetaPositionClosed) : |configurationMonomial a z|≤configurationMomentSize a := by
  rw [configurationMonomial,Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _;exact abs_nonneg _
  · intro i _
    rw [abs_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have difference:=box i
    have triangle : |z i|≤|z i-flatSource i|+|flatSource i| := by
      simpa only [sub_add_cancel] using abs_add_le (z i-flatSource i) (flatSource i)
    linarith

def momentJet (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m)
    (p : PhysicalMomentum) (a : ConfigurationExponent) : FlatConfiguration → ℝ :=
  fun z=>configurationMonomial a z*positionJet B m w p z

theorem momentJet_compact (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m)
    (p : PhysicalMomentum) (a : ConfigurationExponent) : HasCompactSupport (momentJet B m w p a) := by
  apply thetaPositionClosed_compact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ thetaPositionClosed_closed
  intro z nonzero
  by_contra outside
  have zero:=tailJet_position_zero B m w (z,p) outside
  exact nonzero (by simp only [momentJet,positionJet,zero,mul_zero])

theorem momentJet_integrable (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m)
    (p : PhysicalMomentum) (a : ConfigurationExponent) : Integrable (momentJet B m w p a) flatMeasure := by
  rw [←raw100_volume]
  have cont : Continuous (momentJet B m w p a):=
    (configurationMonomial_continuous a).mul (positionJet_smooth B m w p).continuous
  exact cont.integrable_of_hasCompactSupport (momentJet_compact B m w p a)

theorem actual_configuration_moment_bound (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m)
    (p : PhysicalMomentum) (a : ConfigurationExponent) (C : ℝ)
    (actual : ∀ z∈thetaPositionClosed,|positionJet B m w p z|≤C) :
    (∫ z : FlatConfiguration,|momentJet B m w p a z| ∂flatMeasure)≤
      sourcePositionVolume*configurationMomentSize a*C := by
  have integrable:=(momentJet_integrable B m w p a).norm
  have same : (∫ z in thetaPositionClosed,|momentJet B m w p a z| ∂flatMeasure)=
      ∫ z : FlatConfiguration,|momentJet B m w p a z| ∂flatMeasure := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z outside
    have zero:=tailJet_position_zero B m w (z,p) outside
    simp only [momentJet,positionJet,zero,mul_zero,abs_zero]
  calc
    _=(∫ z in thetaPositionClosed,|momentJet B m w p a z| ∂flatMeasure):=same.symm
    _≤∫ _z in thetaPositionClosed,configurationMomentSize a*C ∂flatMeasure := by
      apply setIntegral_mono_on integrable.integrableOn (integrableOn_const source_position_measure_finite)
        thetaPositionClosed_closed.measurableSet
      intro z hz
      rw [momentJet,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (configurationMonomial_bound a z hz) (actual z hz) (abs_nonneg _)
        (configurationMomentSize_nonnegative a)
    _=sourcePositionVolume*configurationMomentSize a*C := by
      rw [setIntegral_const]
      change (flatMeasure thetaPositionClosed).toReal*(configurationMomentSize a*C)=_
      rw [sourcePositionVolume,mul_assoc]

structure UnitEnergyInputs (B : ℕ → Fin 5 → ArrayBound) (N : ℕ) : Prop where
  coefficients : ∀ z∈thetaPositionClosed,∀ u∈thetaDirectionClosed,
    (∑ i : Fin 100,u i^2)=1 → ∀ k,2≤k →
      FiniteBound (sourceEngineEnergy k) N (B k 4) (z,WithLp.toLp 2 u)

theorem originalTailBudget_nonnegative (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (m : ℕ) : 0 ≤ originalTailBudget B m := by
  unfold originalTailBudget
  apply mul_nonneg (by positivity)
  apply add_nonneg
  · exact Finset.sum_nonneg (fun k _=>localizedArray_nonnegative _ (positive k 4) m)
  · positivity

theorem source_positionJet_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N m : ℕ) (order : m≤N) (w : Word m)
    (input : UnitEnergyInputs B N) (p : PhysicalMomentum) :
    ∀ z∈thetaPositionClosed,|positionJet B m w p z|≤originalTailBudget B m := by
  intro z position
  by_cases low : ‖p‖<1
  · have germ:=energyTailFor_low_germ B (z,p) low
    have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
    rw [positionJet,tailJet_actual]
    change |iteratedFDeriv ℝ m (energyTailFor B) (z,p) (slotDirection∘w)|≤_
    rw [read]
    cases m with
    | zero=>simpa only [iteratedFDeriv_zero_apply,abs_zero] using originalTailBudget_nonnegative B positive 0
    | succ n=>
      rw [iteratedFDeriv_succ_const]
      simpa using originalTailBudget_nonnegative B positive (n+1)
  · have outside : 1≤‖p‖:=le_of_not_gt low
    have nonzero : p≠0:=norm_ne_zero_iff.mp (lt_of_lt_of_le (by norm_num) outside).ne'
    by_cases direction : normalizedMomentum p∈thetaDirectionClosed
    · have hx:=source_support_admitted z p position direction nonzero
      have same : unitPhase (z,p)=(z,WithLp.toLp 2 (normalizedMomentum p)) := by
        apply Prod.ext
        · rfl
        · exact (normalized_native_vector p).symm
      have primitive : ∀ k,2≤k → FiniteBound (sourceEngineEnergy k) m (B k 4) (unitPhase (z,p)) := by
        intro k hk n hn v
        rw [same]
        exact input.coefficients z position (normalizedMomentum p) direction
          (normalized_native_unit p nonzero) k hk n (hn.trans order) v
      rw [positionJet,tailJet_actual]
      exact actual_whole_tail_budget B positive m w (z,p) hx outside primitive
    · have germ:=energyTailFor_direction_germ B (z,p) nonzero direction
      have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
      rw [positionJet,tailJet_actual]
      change |iteratedFDeriv ℝ m (energyTailFor B) (z,p) (slotDirection∘w)|≤_
      rw [read]
      cases m with
      | zero=>simpa only [iteratedFDeriv_zero_apply,abs_zero] using originalTailBudget_nonnegative B positive 0
      | succ n=>
        rw [iteratedFDeriv_succ_const]
        simpa using originalTailBudget_nonnegative B positive (n+1)

-- All configuration moments, including total degree102, are generated directly
-- from primitive unit-energy estimates. No whole-tail point bound is input.
theorem source_configuration_moment_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N m : ℕ) (order : m≤N) (w : Word m)
    (input : UnitEnergyInputs B N) (p : PhysicalMomentum) (a : ConfigurationExponent) :
    (∫ z : FlatConfiguration,|momentJet B m w p a z| ∂flatMeasure)≤
      sourcePositionVolume*configurationMomentSize a*originalTailBudget B m :=
  actual_configuration_moment_bound B m w p a (originalTailBudget B m)
    (source_positionJet_bound B positive N m order w input p)

end LowEnergy.PreparationVacuumTailSupport
