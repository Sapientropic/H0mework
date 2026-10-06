import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationLocalizedRadialJets

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLocalizedTail
open PreparationVacuumEngineHomogeneity PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol PreparationVacuumEngineSource
open PreparationVacuumConicComposition PreparationVacuumConicBudget PreparationVacuumCutoffBudget
open PreparationVacuumCentralBudget PreparationVacuumClockJacobian PreparationVacuumMoyalBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

theorem pole_nonzero (x : Phase) (hx : x∈poleDomain) : x.2≠0 := by
  intro zero
  have same : radial 0 x=x := by
    apply Prod.ext
    · rfl
    · simpa only [radial,zero_smul] using zero.symm
  have vanish:=actualA_radial 0 x
  rw [same] at vanish
  have positive : 0<actualA x:=hx.1.2.1
  simp only [zero_pow (by omega : (2 : ℕ)≠0),zero_mul] at vanish
  linarith

theorem conicTheta_pole_smooth : SmoothSymbol sourceConicTheta :=
  fun x hx=>(sourceConicTheta_smooth x (pole_nonzero x hx)).contDiffWithinAt

theorem radialChi_pole_smooth (R : ℝ) : SmoothSymbol (sourceRadialChi R) := by
  intro x hx
  have normSmooth : ContDiffAt ℝ ∞ rho x :=
    (contDiffAt_norm ℝ (pole_nonzero x hx)).comp x contDiffAt_snd
  exact (sourceChi_smooth.contDiffAt.comp x (normSmooth.div_const R)).contDiffWithinAt

theorem thetaArray_nonnegative (m : ℕ) : 0 ≤ thetaBound m := by
  unfold thetaBound composeBound
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (boxBound_nonnegative k) (partialBell_nonnegative _ angularBudget_nonnegative _ _)

theorem radialArray_nonnegative (m : ℕ) : 0 ≤ radialChiBound m := by
  unfold radialChiBound composeBound
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (chiBound_nonnegative k) (partialBell_nonnegative _ radialInnerBudget_nonnegative _ _)

theorem inverse_radial_power_le_one (x : Phase) (outside : 1≤‖x.2‖) (n : ℕ) :
    ((rho x)⁻¹)^n≤1 := by
  have positive : 0<rho x:=lt_of_lt_of_le (by norm_num) outside
  apply pow_le_one₀ (inv_nonneg.mpr positive.le)
  exact (inv_le_one₀ positive).mpr outside

theorem actual_theta_finite (N : ℕ) (x : Phase) (hx : x∈poleDomain) (outside : 1≤‖x.2‖) :
    FiniteBound sourceConicTheta N thetaBound x := by
  intro m _ w
  exact (actual_conicTheta_budget m w x (pole_nonzero x hx)).trans
    ((mul_le_mul_of_nonneg_left (inverse_radial_power_le_one x outside _) (thetaArray_nonnegative m)).trans_eq (mul_one _))

theorem actual_radialChi_finite (R : ℝ) (positive : 0<R) (N : ℕ) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖) :
    FiniteBound (sourceRadialChi R) N radialChiBound x := by
  intro m _ w
  exact (actual_radialChi_budget R positive m w x (pole_nonzero x hx)).trans
    ((mul_le_mul_of_nonneg_left (inverse_radial_power_le_one x outside _) (radialArray_nonnegative m)).trans_eq (mul_one _))

def localizedEnergy (R : ℝ) (k : ℕ) : Symbol :=
  fun x=>sourceConicTheta x*sourceEngineEnergy k x*sourceRadialChi R x

def localizedArray (B : ArrayBound) : ArrayBound :=
  productArray (productArray thetaBound B) radialChiBound

theorem localizedArray_nonnegative (B : ArrayBound) (positive : ∀ m,0 ≤ B m) :
    ∀ m,0 ≤ localizedArray B m :=
  productArray_nonnegative _ _ (productArray_nonnegative _ _ thetaArray_nonnegative positive) radialArray_nonnegative

theorem localizedEnergy_smooth (R : ℝ) (k : ℕ) : SmoothSymbol (localizedEnergy R k) :=
  (conicTheta_pole_smooth.mul (sourceEngineEnergy_smooth k)).mul (radialChi_pole_smooth R)

-- A single native homogeneous coefficient and the actual source cutoffs generate
-- the double Leibniz array. The radial factor remains the original degree2-k.
theorem actual_localized_energy_budget (R : ℝ) (positive : 0<R) (k N : ℕ)
    (x : Phase) (hx : x∈poleDomain) (outside : 1≤‖x.2‖)
    (B : ArrayBound) (nonnegative : ∀ m,0 ≤ B m)
    (primitive : FiniteBound (sourceEngineEnergy k) N B (unitPhase x)) :
    FiniteBound (localizedEnergy R k) N
      (fun m=>localizedArray B m*‖x.2‖^((2 : ℤ)-k)) x := by
  let t : ℝ:=‖x.2‖^((2 : ℤ)-k)
  have tpositive : 0≤t:=zpow_nonneg (norm_nonneg _) _
  have eb : FiniteBound (sourceEngineEnergy k) N (fun m=>B m*t) x := by
    intro m hm w
    exact energy_jet_radial_bound k m w x hx outside B (primitive m hm w)
  have first:=finite_product sourceConicTheta (sourceEngineEnergy k) conicTheta_pole_smooth
    (sourceEngineEnergy_smooth k) thetaBound (fun m=>B m*t) thetaArray_nonnegative N x hx
    (actual_theta_finite N x hx outside) eb
  have second:=finite_product (sourceConicTheta*sourceEngineEnergy k) (sourceRadialChi R)
    (conicTheta_pole_smooth.mul (sourceEngineEnergy_smooth k)) (radialChi_pole_smooth R)
    (productArray thetaBound (fun m=>B m*t)) radialChiBound
    (productArray_nonnegative _ _ thetaArray_nonnegative (fun m=>mul_nonneg (nonnegative m) tpositive))
    N x hx first (actual_radialChi_finite R positive N x hx outside)
  have factor (a b : ArrayBound) (c : ℝ) : productArray a (fun m=>b m*c)=(fun m=>productArray a b m*c) := by
    funext m
    unfold productArray
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have factorLeft (a b : ArrayBound) (c : ℝ) : productArray (fun m=>a m*c) b=(fun m=>productArray a b m*c) := by
    funext m
    unfold productArray
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [factor thetaBound B t,factorLeft _ radialChiBound t] at second
  exact second

end LowEnergy.PreparationVacuumLocalizedTail
