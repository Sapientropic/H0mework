import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.WordMass

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeCenteredWorkGate
open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
variable {nu : Viscosity}

private theorem square_upper (p A b c : ℝ) (p0 : 0≤p) (A0 : 0≤A)
    (upper : p*A≤b+c) : p^2*A^2≤2*b^2+2*c^2 := by
  have square:=pow_le_pow_left₀ (mul_nonneg p0 A0) upper 2
  nlinarith only [square,sq_nonneg (b-c)]

private theorem linear_absorb (p A B : ℝ) (positive : 0<p) :
    B*A≤(p^2/2)*A^2+B^2/(2*p^2) := by
  have identity : (p^2/2)*A^2+B^2/(2*p^2)-B*A=(p*A-B/p)^2/2 := by
    field_simp [positive.ne']
    ring
  nlinarith only [sq_nonneg (p*A-B/p),identity]

theorem source_original_work_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃low : ℕ,∃q K C : ℝ,0≤q ∧0≤K ∧0≤C ∧∀M≥low,∀time∈Icc 0 horizon,
      let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
      (nu.coeff^2/32)*‖l‖^4+
        q*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
          q*NativeWindowHistoryAllOrderSpatial.work seed M 1 time+
            K*NativeWindowHistoryAllOrderWord.energy seed M 1 time+C := by
  obtain ⟨low,D,D0,wcost⟩:=NativeCenteredCovariance.source_centered_spatial_cost seed horizon
  obtain ⟨Agen,C1,A0,C10,rate⟩:=NativeCenteredAllWordRate.source_centeredWCost_allWord_rate
    seed horizon 1 (by norm_num)
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have G0 : 0≤G:=le_max_left _ _
  let p:=nu.coeff/4
  have ppos : 0<p:=div_pos nu.coeff_pos (by norm_num)
  let q:=2*G/nu.coeff^2
  have q0 : 0≤q:=div_nonneg (mul_nonneg (by norm_num) G0) (sq_nonneg _)
  let B:=2*G*C1
  let K:=q*Agen
  let C:=2*D^2+B^2/(2*p^2)
  have K0 : 0≤K:=mul_nonneg q0 A0
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨low,q,K,C,q0,K0,C0,fun M above time inside => ?_⟩
  let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
  let X:=‖l‖^2
  let P:=NativeCenteredCovariance.centeredWCost seed M time
  have X0 : 0≤X:=sq_nonneg _
  have P0 : 0≤P:=NativeCenteredCovariance.centeredActionCost_nonnegative seed time inside.1 _
  have w:=wcost M above time inside
  have r:=rate M time inside
  dsimp only at r
  change p*X≤Real.sqrt G*Real.sqrt P+D at w
  have b0 : 0≤Real.sqrt G*Real.sqrt P:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have squared:=square_upper p X (Real.sqrt G*Real.sqrt P) D ppos.le X0 w
  have sqrtG : (Real.sqrt G)^2=G:=Real.sq_sqrt G0
  have sqrtP : (Real.sqrt P)^2=P:=Real.sq_sqrt P0
  have squarePaid : p^2*X^2≤2*G*P+2*D^2 := by
    simpa only [mul_pow,sqrtG,sqrtP,← mul_assoc] using squared
  have scaled:=mul_le_mul_of_nonneg_left r (mul_nonneg (by norm_num : (0:ℝ)≤2) G0)
  have ratePaid : 2*G*P+q*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
      q*(Agen*NativeWindowHistoryAllOrderWord.energy seed M 1 time+
        NativeWindowHistoryAllOrderSpatial.work seed M 1 time)+B*X := by
    change 2*G*(P+(1/nu.coeff^2)*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time)≤
      2*G*((1/nu.coeff^2)*(Agen*NativeWindowHistoryAllOrderWord.energy seed M 1 time+
        NativeWindowHistoryAllOrderSpatial.work seed M 1 time)+C1*X) at scaled
    dsimp only [q,B]
    calc
      _=2*G*(P+(1/nu.coeff^2)*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time) := by ring
      _≤_ := scaled
      _=_ := by ring
  have young:=linear_absorb p X B ppos
  change (nu.coeff^2/32)*‖l‖^4+
      q*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
        q*NativeWindowHistoryAllOrderSpatial.work seed M 1 time+
          K*NativeWindowHistoryAllOrderWord.energy seed M 1 time+C
  dsimp only [p,X,K,C] at squarePaid ratePaid young ⊢
  nlinarith only [squarePaid,ratePaid,young]

theorem source_original_work_gate_paid (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃low : ℕ,∃q C : ℝ,0≤q ∧0≤C ∧∀M≥low,∀time∈Icc 0 horizon,
      let l:=laplacianFiber nu M (mean (finiteHistory seed time M))
      (nu.coeff^2/32)*‖l‖^4+
        q*deriv (NativeWindowHistoryAllOrderSpatial.energy seed M 1) time≤
          q*NativeWindowHistoryAllOrderSpatial.work seed M 1 time+C := by
  obtain ⟨low,q,K,C,q0,K0,C0,gate⟩:=source_original_work_gate seed horizon
  obtain ⟨E,E0,paid⟩:=NativeCenteredWordMass.source_word_one_energy_bound seed horizon
  refine ⟨low,q,K*E+C,q0,add_nonneg (mul_nonneg K0 E0) C0,fun M above time inside => ?_⟩
  have old:=gate M above time inside
  dsimp only at old
  have mass:=mul_le_mul_of_nonneg_left (paid M time inside) K0
  dsimp only
  nlinarith only [old,mass]

end
end SaturationMonoid.NavierStokes.NativeCenteredWorkGate
