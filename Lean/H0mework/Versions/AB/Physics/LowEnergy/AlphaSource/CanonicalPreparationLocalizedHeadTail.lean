import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLocalizedCutoffProduct

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLocalizedTail
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth PreparationVacuumMoyalSymmetry
open PreparationVacuumClockSymbol PreparationVacuumEngineSource PreparationVacuumConicComposition
open PreparationVacuumCentralBudget PreparationVacuumOriginalRadii PreparationVacuumPrincipalBudget
open PreparationVacuumConicBudget CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

def originalCutoff (B : ℕ → Fin 5 → ArrayBound) : ℕ → UpperArray :=
  localizedCutoff B thetaBound radialChiBound

def sourceRadiusFor (B : ℕ → Fin 5 → ArrayBound) (k : ℕ) : ℝ :=
  originalRadius (originalCutoff B) k

def energyTailTerm (B : ℕ → Fin 5 → ArrayBound) (k : ℕ) : Symbol :=
  localizedEnergy (sourceRadiusFor B k) k

def originalTailStart (m : ℕ) : ℕ := max (m+2) 3

def originalHeadBudget (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) : ℝ :=
  ∑ k∈Finset.Ico 2 (originalTailStart m),localizedArray (B k 4) m

def originalTailBudget (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) : ℝ :=
  (3 : ℝ)^m*(originalHeadBudget B m+2*(1/2 : ℝ)^(originalTailStart m))

theorem actual_localized_low_zero (R : ℝ) (positive : 0<R) (k m : ℕ)
    (w : Word m) (x : Phase) (low : ‖x.2‖<R) : jet m (localizedEnergy R k) w x=0 := by
  have near : ∀ᶠ y : Phase in 𝓝 x,‖y.2‖<R :=
    (continuous_snd.norm.continuousAt).eventually (gt_mem_nhds low)
  have germ : localizedEnergy R k=ᶠ[𝓝 x] (fun _ : Phase=>(0 : ℝ)) := by
    filter_upwards [near] with y hy
    have ratio : rho y/R≤1 := (div_le_one positive).mpr hy.le
    simp only [localizedEnergy,sourceRadialChi,Function.comp_def,sourceChi,if_pos ratio,mul_zero]
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  change iteratedFDeriv ℝ m (localizedEnergy R k) x (slotDirection∘w)=0
  rw [read]
  cases m <;> simp

theorem actual_original_term_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (k m : ℕ) (later : 2<k) (order : m≤k)
    (x : Phase) (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : FiniteBound (sourceEngineEnergy k) m (B k 4) (unitPhase x)) (w : Word m) :
    |jet m (energyTailTerm B k) w x|≤(1/2 : ℝ)^k := by
  have rp : 0<sourceRadiusFor B k:=originalRadius_positive (originalCutoff B) k
  by_cases low : ‖x.2‖<sourceRadiusFor B k
  · rw [energyTailTerm,actual_localized_low_zero _ rp k m w x low,abs_zero]
    positivity
  · have actual:=actual_localized_energy_budget (sourceRadiusFor B k) rp k m x hx outside
      (B k 4) (positive k 4) primitive m (Nat.le_refl _) w
    have array : localizedArray (B k 4) m≤exponentValue (originalCutoff B k m) := by
      have raw:=localizedCutoff_bound B thetaBound radialChiBound positive thetaArray_nonnegative
        radialArray_nonnegative k m 4
      rw [productArray_comm (B k 4) thetaBound] at raw
      exact raw
    have degree : ((2 : ℤ)-k)=-(k-2 : ℕ) := by omega
    have radial : ‖x.2‖^((2 : ℤ)-k)=1/‖x.2‖^(k-2) := by
      rw [degree,zpow_neg,zpow_natCast,one_div]
    rw [radial] at actual
    have comparison : localizedArray (B k 4) m*(1/‖x.2‖^(k-2))≤
        exponentValue (originalCutoff B k m)/‖x.2‖^(k-2) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right array (by positivity : 0≤(‖x.2‖^(k-2))⁻¹)
    exact (actual.trans comparison).trans
      (source_radius_scaled_bound (originalCutoff B) k m 2 later order ‖x.2‖ (le_of_not_gt low))

theorem actual_original_head_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (k m : ℕ) (principal : 2≤k)
    (x : Phase) (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : FiniteBound (sourceEngineEnergy k) m (B k 4) (unitPhase x)) (w : Word m) :
    |jet m (energyTailTerm B k) w x|≤localizedArray (B k 4) m := by
  have rp : 0<sourceRadiusFor B k:=originalRadius_positive (originalCutoff B) k
  have actual:=actual_localized_energy_budget (sourceRadiusFor B k) rp k m x hx outside
    (B k 4) (positive k 4) primitive m (Nat.le_refl _) w
  have scale : ‖x.2‖^((2 : ℤ)-k)≤1 := by
    have power:=zpow_le_zpow_right₀ outside (show (2 : ℤ)-k≤0 by omega)
    simpa only [zpow_zero] using power
  exact actual.trans ((mul_le_mul_of_nonneg_left scale (localizedArray_nonnegative _ (positive k 4) m)).trans_eq (mul_one _))

-- The original K=max(m+2,3) keeps k2 in the finite head. This bound is uniform
-- in finite tail length and consumes only the actual unit-radial coefficient jets.
theorem actual_original_finite_tail (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (m L : ℕ) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (primitive : ∀ k,2≤k → FiniteBound (sourceEngineEnergy k) m (B k 4) (unitPhase x))
    (w : Word m) :
    |(∑ k∈Finset.Ico 2 (originalTailStart m),jet m (energyTailTerm B k) w x)+
      ∑ j∈Finset.range L,jet m (energyTailTerm B (originalTailStart m+j)) w x|≤
        originalTailBudget B m := by
  have start : m+2≤originalTailStart m:=le_max_left _ _
  have three : 3≤originalTailStart m:=le_max_right _ _
  have head : |∑ k∈Finset.Ico 2 (originalTailStart m),jet m (energyTailTerm B k) w x|≤originalHeadBudget B m := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    exact actual_original_head_bound B positive k m (Finset.mem_Ico.mp hk).1 x hx outside
      (primitive k (Finset.mem_Ico.mp hk).1) w
  have tail : |∑ j∈Finset.range L,jet m (energyTailTerm B (originalTailStart m+j)) w x|≤
      2*(1/2 : ℝ)^(originalTailStart m) := by
    calc
      _≤∑ j∈Finset.range L,|jet m (energyTailTerm B (originalTailStart m+j)) w x|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑ j∈Finset.range L,(1/2 : ℝ)^(originalTailStart m+j) := by
        apply Finset.sum_le_sum
        intro j _
        exact actual_original_term_bound B positive _ m (by omega) (by omega) x hx outside
          (primitive _ (by omega)) w
      _≤∑' j : ℕ,(1/2 : ℝ)^(originalTailStart m+j) :=
        (shifted_geometric_hasSum _).summable.sum_le_tsum _ (by intro j _;positivity)
      _=_:=(shifted_geometric_hasSum _).tsum_eq
  have total : |(∑ k∈Finset.Ico 2 (originalTailStart m),jet m (energyTailTerm B k) w x)+
      ∑ j∈Finset.range L,jet m (energyTailTerm B (originalTailStart m+j)) w x|≤
        originalHeadBudget B m+2*(1/2 : ℝ)^(originalTailStart m) :=
    (abs_add_le _ _).trans (add_le_add head tail)
  have nonnegative : 0≤originalHeadBudget B m+2*(1/2 : ℝ)^(originalTailStart m):=by
    apply add_nonneg
    · exact Finset.sum_nonneg (fun k _=>localizedArray_nonnegative _ (positive k 4) m)
    · positivity
  exact total.trans (by
    unfold originalTailBudget
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ)≤3) (n:=m)])

end LowEnergy.PreparationVacuumLocalizedTail
