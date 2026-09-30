import H0mework.Versions.X.NavierStokes.WindowSourceGreen.LowerOperator

set_option autoImplicit false
open scoped BigOperators Matrix
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteLowerBound
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeCanonicalFluidCoframe (density density_pos scale scale_pos scale_cube)
open NativePauliControl (Vector denominator denominator_pos)
open NativeCartanConstitutive (squared)
open NativeWindowAbsoluteLowerOperator
noncomputable section

theorem scale_one (v : PhysicalSpace) : 1 ≤ scale v := by
  by_contra smaller
  have power:=pow_lt_pow_left₀ (lt_of_not_ge smaller) (scale_pos v).le (by decide : (3:ℕ)≠0)
  rw [scale_cube] at power
  norm_num at power
  linarith [NativeWindowMassReciprocal.density_lower v]

theorem coordinate_bound (v : PhysicalSpace) (i : Fin 3) : |v i| ≤ density v := by
  exact (show |v i| ≤ ‖v‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i).trans
    (NativeWindowMassReciprocal.norm_density v)

theorem cartan_bound (v : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) : |cartanCoefficient v direction pair| ≤ density v := by
  have profile:|NativeCartanCoordinates.profile (NativeCartanCoordinates.currentVector v) direction pair| ≤ density v := by
    fin_cases direction <;> fin_cases pair <;>
      simp [NativeCartanCoordinates.profile,NativeCartanCoordinates.currentVector,
        abs_neg,abs_zero,abs_of_pos (density_pos v)]
    all_goals first | exact (density_pos v).le | exact le_refl _ | exact coordinate_bound v _
  rw [cartanCoefficient,abs_div,abs_of_pos (mul_pos (by norm_num : (0:ℝ)<8) (scale_pos v))]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) (scale_pos v))).mpr
  nlinarith [scale_one v,density_pos v]

theorem flux_one (v : Vector) : 1 ≤ NativeCartanStressLaw.fluxFactor v := by
  rw [NativeCartanStressLaw.fluxFactor]
  apply (le_div_iff₀ (denominator_pos v)).mpr
  change 1*(3+squared v) ≤ _
  have nonnegative : 0 ≤ squared v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [sq_nonneg (squared v)]

private theorem square_coordinate (v : Vector) (i : Fin 3) : (v i)^2 ≤ squared v :=
  Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

private theorem component (v : Vector) (i : Fin 3) : |v i| ≤ 1+squared v := by
  have paid:=square_coordinate v i
  have nonnegative:0 ≤ squared v:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (v i+1)],by nlinarith [sq_nonneg (v i-1)]⟩

private theorem pair_bound (v : Vector) (i j : Fin 3) : |v i*v j| ≤ squared v := by
  rw [abs_mul]
  have first:=square_coordinate v i
  have last:=square_coordinate v j
  nlinarith [sq_nonneg (|v i|-|v j|),sq_abs (v i),sq_abs (v j)]

private theorem ratio_bound (v : Vector) : |(squared v-1)/denominator v| ≤ 1 := by
  rw [abs_div,abs_of_pos (denominator_pos v)]
  apply (div_le_iff₀ (denominator_pos v)).mpr
  have nonnegative:0 ≤ squared v:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  change |squared v-1| ≤ 1*(3+squared v)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem radial_bound (v : Vector) (direction : Fin 4) (color : Fin 3) :
    |NativeConstitutiveColor.radial v direction color| ≤ 2*NativePauliJet.density v := by
  have s0:0 ≤ squared v:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  cases direction using Fin.cases with
  | zero =>
    have tau:|-4*squared v/denominator v| ≤ 4 := by
      rw [abs_div,abs_mul,abs_of_nonneg s0,abs_of_pos (denominator_pos v)]
      rw [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<4)]
      apply (div_le_iff₀ (denominator_pos v)).mpr
      change 4*squared v ≤ 4*(3+squared v)
      linarith
    have paid:=mul_le_mul tau (component v color) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
    have original:NativeConstitutiveColor.radial v 0 color=(-4*squared v/denominator v)*v color := by
      fin_cases color <;> rfl
    rw [original,abs_mul]
    exact paid.trans_eq (by unfold NativePauliJet.density squared; ring)
  | succ direction =>
    rw [NativeConstitutiveMaterial.radial_row]
    have beta:|NativeConstitutiveMaterial.radialDiagonal v| ≤ squared v := by
      have paid:=mul_le_mul_of_nonneg_left (ratio_bound v) s0
      simpa only [NativeConstitutiveMaterial.radialDiagonal,mul_div_assoc,abs_mul,abs_of_nonneg s0,mul_one] using paid
    have diagonal:|NativeConstitutiveMaterial.radialDiagonal v*(if direction=color then 1 else 0)| ≤ squared v := by
      split_ifs <;> simp only [mul_one,mul_zero,abs_zero] <;> assumption
    have paid:=(abs_add_le (v direction*v color) _).trans (add_le_add (pair_bound v direction color) diagonal)
    exact paid.trans (by unfold NativePauliJet.density; change _ ≤ 2*(2*(1+squared v)); linarith)

theorem constitutive_bound (v : PhysicalSpace) (direction : Fin 4) (color : Fin 3) :
    |(density v)⁻¹*NativeConstitutiveColor.coefficients v direction color| ≤ 17*density v := by
  let u:=NativePauliCoframeAction.normalizedVelocity v
  have factor : (density v)⁻¹*NativeConstitutiveColor.correctionScale v=
      (2*scale v)⁻¹*(-16/NativeCartanStressLaw.fluxFactor u-1) := by
    rw [NativeConstitutiveColor.correctionScale,← scale_cube]
    dsimp only [u]
    field_simp [(scale_pos v).ne']
  have denom:0<NativeCartanStressLaw.fluxFactor u:=NativeCartanStressLaw.fluxFactor_pos u
  have quotient:|(-16:ℝ)/NativeCartanStressLaw.fluxFactor u-1| ≤ 17 := by
    have paid:16/NativeCartanStressLaw.fluxFactor u ≤ 16 := by
      apply (div_le_iff₀ denom).mpr
      linarith [flux_one u]
    have nonnegative:0 ≤ 16/NativeCartanStressLaw.fluxFactor u:=div_nonneg (by norm_num) denom.le
    rw [neg_div]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have small:(2*scale v)⁻¹ ≤ 1/2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show 2 ≤ 2*scale v by linarith [scale_one v])
  change |(density v)⁻¹*(NativeConstitutiveColor.correctionScale v*NativeConstitutiveColor.radial u direction color)| ≤ _
  rw [← mul_assoc,factor,abs_mul,abs_mul,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num : (0:ℝ)<2) (scale_pos v)))]
  have paid:=mul_le_mul (mul_le_mul small quotient (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2))
    (radial_bound u direction color) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ (1/2)*17)
  rw [← NativeMaterialJetAction.source_density] at paid
  exact paid.trans_eq (by ring)

theorem compensation_bound (v : PhysicalSpace) (direction : Fin 4) (color : Fin 3) :
    |(density v)⁻¹*cartanControl v direction color| ≤ 2*density v := by
  let u:=NativePauliCoframeAction.normalizedVelocity v
  let ratio:=(1-squared u)/denominator u
  have ratioBound:|ratio| ≤ 1 := by
    have same:ratio= -((squared u-1)/denominator u):=by dsimp only [ratio]; ring
    rw [same,abs_neg]
    exact ratio_bound u
  have inverse:(scale v)⁻¹ ≤ 1 := by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (scale_one v)
  have inv0:0 ≤ (scale v)⁻¹:=(inv_pos.mpr (scale_pos v)).le
  have control:cartanControl v=NativePauliControl.coefficients
      (fun i => 3/2*scale v^2*(1-squared u)/denominator u*u i) 0
      (NativeCartanConstitutive.isotropicCorrection (scale v) u) := by
    simpa only [cartanControl,NativeCartanConstitutive.response_eq,neg_smul,Complex.ofReal_pow] using
      NativeCartanConstitutive.response_control (scale v) u
  have s0:0 ≤ squared u:=Finset.sum_nonneg fun _ _ => sq_nonneg _
  cases direction using Fin.cases with
  | zero =>
    have original:(density v)⁻¹*cartanControl v 0 color=(3/2:ℝ)*(scale v)⁻¹*ratio*u color := by
      rw [control,← scale_cube]
      dsimp only [ratio]
      fin_cases color <;> simp [NativePauliControl.coefficients]
      all_goals field_simp [(scale_pos v).ne']
    rw [original,abs_mul,abs_mul,abs_mul,abs_of_nonneg inv0]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<3/2)]
    have product:(3/2:ℝ)*(scale v)⁻¹*|ratio| ≤ 3/2 := by
      nlinarith [mul_nonneg inv0 (sub_nonneg.mpr ratioBound)]
    have paid:=mul_le_mul product (component u color) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3/2)
    apply paid.trans
    rw [NativeMaterialJetAction.source_density]
    change (3/2:ℝ)*(1+squared u) ≤ 2*(2*(1+squared u))
    linarith
  | succ direction =>
    have original:(density v)⁻¹*cartanControl v direction.succ color=
        -(3/4:ℝ)*(scale v)⁻¹*ratio*(1+squared u)*(if direction=color then 1 else 0) := by
      rw [control,← scale_cube]
      dsimp only [ratio,NativeCartanConstitutive.isotropicCorrection]
      fin_cases direction <;> fin_cases color <;>
        simp [NativePauliControl.coefficients]
      all_goals field_simp [(scale_pos v).ne']
    rw [original]
    by_cases same:direction=color
    · rw [if_pos same,mul_one,abs_mul,abs_mul,abs_mul,abs_of_nonneg inv0,abs_of_nonneg (by linarith : 0 ≤ 1+squared u)]
      norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<3/4)]
      have product:(3/4:ℝ)*(scale v)⁻¹*|ratio| ≤ 3/4 := by
        nlinarith [mul_nonneg inv0 (sub_nonneg.mpr ratioBound)]
      have paid:=mul_le_mul_of_nonneg_right product (show 0 ≤ 1+squared u by linarith)
      apply paid.trans
      rw [NativeMaterialJetAction.source_density]
      change (3/4:ℝ)*(1+squared u) ≤ 2*(2*(1+squared u))
      linarith
    · simp only [if_neg same,mul_zero,abs_zero]
      positivity [density_pos v]

def jetSize (jet : Fin 4 → PhysicalSpace) : ℝ := ∑ direction,‖jet direction‖

theorem free_bound (v : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (direction : Fin 4) (color : Fin 3) :
    |freeCoefficients v jet direction color| ≤ jetSize jet := by
  have component:freeCoefficients v jet direction color^2 ≤
      ∑ d : Fin 4,∑ c : Fin 3,freeCoefficients v jet d c^2 :=
    (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ color)).trans
      (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ direction))
  have sum:=Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin 4))) (fun d _ => norm_nonneg (jet d))
  apply (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [sq_abs]
  change _ ≤ (∑ d : Fin 4,‖jet d‖)^2
  nlinarith [free_square v jet,Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 4))) (fun d _ => sq_nonneg ‖jet d‖)]

open PhysicsCore DiracExteriorMatterAction StageNineHolonomicField
open NativeWindowGreenTestForm (SpinFiber)

abbrev Full (E : Type*) := PiLp 2 (fun _ : MatterCoordinateIndex => E)

def matrixCost (L : Module.End ℂ DiracExteriorMatterCarrier) : ℝ :=
  ∑ output : MatterCoordinateIndex,∑ entry : Fin 4 × Fin 2,
    ‖matterCoordinateEquiv (L (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)) output‖

theorem matrixCost_nonnegative (L : Module.End ℂ DiracExteriorMatterCarrier) : 0 ≤ matrixCost L :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

def colorCost : ℝ := ∑ direction : Fin 4,∑ c : Fin 3,matrixCost (fixedColor direction c)
def cartanCost : ℝ := ∑ direction : Fin 4,∑ p : Fin 6,matrixCost (fixedCartan direction p)
def cap : ℝ := matrixCost LinearMap.id+colorCost+(cartanCost+19*colorCost)

theorem colorCost_nonnegative : 0 ≤ colorCost :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => matrixCost_nonnegative _

theorem cartanCost_nonnegative : 0 ≤ cartanCost :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => matrixCost_nonnegative _

theorem cap_nonnegative : 0 ≤ cap := by
  unfold cap
  exact add_nonneg (add_nonneg (matrixCost_nonnegative LinearMap.id) colorCost_nonnegative)
    (add_nonneg cartanCost_nonnegative (mul_nonneg (by norm_num : (0:ℝ) ≤ 19) colorCost_nonnegative))

section Lift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def lift (L : Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) : Full E :=
  WithLp.toLp 2 fun output => ∑ entry : Fin 4 × Fin 2,
    matterCoordinateEquiv (L (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)) output • v entry

theorem lift_norm (L : Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) : ‖lift L v‖ ≤ matrixCost L*‖v‖ := by
  have l1 (w : Full E) : ‖w‖ ≤ ∑ output : MatterCoordinateIndex,‖w output‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  apply (l1 (lift L v)).trans
  have first : (∑ output : MatterCoordinateIndex,‖lift L v output‖) ≤
      ∑ output : MatterCoordinateIndex,∑ entry : Fin 4 × Fin 2,
        ‖matterCoordinateEquiv (L (NativeWindowStageTenWholeFirstJet.materialBasis entry.1 entry.2)) output‖*‖v‖ := by
    apply Finset.sum_le_sum
    intro output _
    simp only [lift,PiLp.toLp_apply]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro entry _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v entry) (norm_nonneg _)
  simpa only [matrixCost,Finset.sum_mul] using first

theorem lift_add (L K : Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) :
    lift (L+K) v=lift L v+lift K v := by
  apply PiLp.ext
  intro output
  simp only [lift,PiLp.toLp_apply,PiLp.add_apply,LinearMap.add_apply,map_add,add_smul,Finset.sum_add_distrib]

theorem lift_smul (a : ℂ) (L : Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) : lift (a • L) v=a • lift L v := by
  apply PiLp.ext
  intro output
  simp only [lift,PiLp.toLp_apply,PiLp.smul_apply,LinearMap.smul_apply,map_smul,smul_eq_mul,mul_smul,Finset.smul_sum]

theorem lift_sum {ι : Type*} (F : Finset ι) (L : ι → Module.End ℂ DiracExteriorMatterCarrier) (v : SpinFiber E) :
    lift (∑ i∈F,L i) v=∑ i∈F,lift (L i) v := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply PiLp.ext
    intro output
    simp [lift]
  | @insert i F outside ih => simp only [Finset.sum_insert outside,lift_add,ih]

theorem color_norm (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (v : SpinFiber E) :
    ‖lift (color velocity coefficients) v‖ ≤
      (∑ direction : Fin 4,∑ c : Fin 3,|(density velocity)⁻¹*coefficients direction c| * matrixCost (fixedColor direction c))*‖v‖ := by
  rw [color_factor,bareColor_expansion,lift_smul]
  simp only [lift_sum,lift_smul,Finset.smul_sum,smul_smul,← Complex.ofReal_mul]
  apply (norm_sum_le _ _).trans
  have paid : (∑ direction : Fin 4,‖∑ c : Fin 3,(((density velocity)⁻¹*coefficients direction c : ℝ) : ℂ) • lift (fixedColor direction c) v‖) ≤
      ∑ direction : Fin 4,∑ c : Fin 3,|(density velocity)⁻¹*coefficients direction c| * (matrixCost (fixedColor direction c)*‖v‖) := by
    apply Finset.sum_le_sum
    intro direction _
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum fun c _ => by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (lift_norm (fixedColor direction c) v) (abs_nonneg _)
  simpa only [← mul_assoc,Finset.sum_mul] using paid

theorem cartan_norm (velocity : PhysicalSpace) (v : SpinFiber E) :
    ‖lift (cartan velocity) v‖ ≤
      (∑ direction : Fin 4,∑ p : Fin 6,|cartanCoefficient velocity direction p| * matrixCost (fixedCartan direction p))*‖v‖ := by
  rw [cartan_expansion]
  simp only [lift_sum,lift_smul]
  apply (norm_sum_le _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun direction _ =>
    (norm_sum_le (Finset.univ : Finset (Fin 6)) (fun p => (cartanCoefficient velocity direction p : ℂ) • lift (fixedCartan direction p) v)).trans
      (Finset.sum_le_sum fun p _ => show ‖(cartanCoefficient velocity direction p : ℂ) • lift (fixedCartan direction p) v‖ ≤
          |cartanCoefficient velocity direction p| * (matrixCost (fixedCartan direction p)*‖v‖) by
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (lift_norm (fixedCartan direction p) v) (abs_nonneg _)))
  simpa only [← mul_assoc,Finset.sum_mul] using paid

theorem color_bounded (velocity : PhysicalSpace) (coefficients : Fin 4 → Fin 3 → ℝ) (B : ℝ)
    (bound : ∀ d c,|(density velocity)⁻¹*coefficients d c| ≤ B) (v : SpinFiber E) :
    ‖lift (color velocity coefficients) v‖ ≤ B*colorCost*‖v‖ := by
  apply (color_norm velocity coefficients v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  simp only [colorCost,Finset.mul_sum]
  exact Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun c _ =>
    mul_le_mul_of_nonneg_right (bound d c) (matrixCost_nonnegative _)

theorem static_norm (velocity : PhysicalSpace) (v : SpinFiber E) :
    ‖lift (static velocity) v‖ ≤ (cartanCost+19*colorCost)*density velocity*‖v‖ := by
  have cartanPaid:‖lift (cartan velocity) v‖ ≤ density velocity*cartanCost*‖v‖ := by
    apply (cartan_norm velocity v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    simp only [cartanCost,Finset.mul_sum]
    exact Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_right (cartan_bound velocity d p) (matrixCost_nonnegative _)
  have compensationPaid:=color_bounded velocity (cartanControl velocity) (2*density velocity)
    (compensation_bound velocity) v
  have constitutivePaid:=color_bounded velocity (NativeConstitutiveColor.coefficients velocity) (17*density velocity)
    (constitutive_bound velocity) v
  rw [static,lift_add,lift_add]
  have first:=norm_add_le (lift (cartan velocity) v) (lift (color velocity (cartanControl velocity)) v)
  have last:=norm_add_le (lift (cartan velocity) v+lift (color velocity (cartanControl velocity)) v)
    (lift (color velocity (NativeConstitutiveColor.coefficients velocity)) v)
  nlinarith only [cartanPaid,compensationPaid,constitutivePaid,first,last]

theorem lower_bound (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (v : SpinFiber E) :
    ‖lift (NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet) v‖ ≤ cap*(density velocity+jetSize jet)*‖v‖ := by
  have spinPaid:‖lift (spin velocity jet) v‖ ≤ jetSize jet*matrixCost LinearMap.id*‖v‖ := by
    rw [spin_scalar,lift_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
    have coefficient:|(density velocity)⁻¹*(-(3/2:ℝ)*NativePauliJet.logDerivative
        (NativePauliCoframeAction.normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet jet) 0)| ≤ jetSize jet := by
      have component:‖jet 0‖ ≤ jetSize jet:=Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ 0)
      linarith [spin_bound velocity jet,norm_nonneg (jet 0)]
    exact (mul_le_mul coefficient (lift_norm LinearMap.id v) (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans_eq (by ring)
  have colorPaid:=color_bounded velocity (NativeBalancedMaterialJet.freeCoefficients velocity jet) (jetSize jet)
    (free_bound velocity jet) v
  have staticPaid:=static_norm velocity v
  rw [lower_split,lift_add,lift_add]
  have first:=norm_add_le (lift (spin velocity jet) v) (lift (color velocity (NativeBalancedMaterialJet.freeCoefficients velocity jet)) v)
  have last:=norm_add_le (lift (spin velocity jet) v+lift (color velocity (NativeBalancedMaterialJet.freeCoefficients velocity jet)) v)
    (lift (static velocity) v)
  have c0:=colorCost_nonnegative
  have k0:=cartanCost_nonnegative
  have m0:=matrixCost_nonnegative LinearMap.id
  have j0:0 ≤ jetSize jet:=Finset.sum_nonneg fun _ _ => norm_nonneg _
  have extraFirst:=mul_nonneg (mul_nonneg (add_nonneg m0 c0) (density_pos velocity).le) (norm_nonneg v)
  have extraLast:=mul_nonneg (mul_nonneg (add_nonneg k0 (mul_nonneg (by norm_num : (0:ℝ) ≤ 19) c0)) j0) (norm_nonneg v)
  dsimp only [cap]
  nlinarith only [spinPaid,colorPaid,staticPaid,first,last,extraFirst,extraLast]

theorem lower_square_bound (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace) (v : SpinFiber E) :
    ‖lift (NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet) v‖^2 ≤
      5*cap^2*(density velocity^2+(∑ direction : Fin 4,‖jet direction‖^2))*‖v‖^2 := by
  have sum:jetSize jet^2 ≤ 4*(∑ direction : Fin 4,‖jet direction‖^2) := by
    have paid:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4)) (fun _ => (1:ℝ)) (fun d => ‖jet d‖)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one,jetSize] using paid
  have coefficient:(density velocity+jetSize jet)^2 ≤ 5*(density velocity^2+∑ direction : Fin 4,‖jet direction‖^2) := by
    nlinarith only [sum,sq_nonneg (2*density velocity-jetSize jet/2)]
  have paid:=pow_le_pow_left₀ (norm_nonneg _) (lower_bound velocity jet v) 2
  simp only [mul_pow] at paid
  apply paid.trans
  calc
    _ ≤ cap^2*(5*(density velocity^2+∑ direction : Fin 4,‖jet direction‖^2))*‖v‖^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficient (sq_nonneg cap)) (sq_nonneg ‖v‖)
    _ = _ := by ring

end Lift

theorem lift_original (L : Module.End ℂ DiracExteriorMatterCarrier) (v : NativeWindowAbsoluteTimePhysicalMatter.Spinor) :
    lift L (WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => v entry.1 entry.2))=
      WithLp.toLp 2 (NativeWindowAbsoluteTimePhysicalMatter.extension L v) := by
  apply PiLp.ext
  intro output
  simp only [lift,NativeWindowAbsoluteTimePhysicalMatter.extension,PiLp.toLp_apply,Fintype.sum_prod_type]

theorem physical_lower_bound (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (v : NativeWindowAbsoluteTimePhysicalMatter.Spinor) :
    ‖(WithLp.toLp 2 (NativeWindowAbsoluteTimePhysicalMatter.extension
      (NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet) v) : Full NativeWindowAbsoluteTimeFourier.Fiber)‖ ≤
      cap*(density velocity+jetSize jet)*‖(WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => v entry.1 entry.2) : SpinFiber NativeWindowAbsoluteTimeFourier.Fiber)‖ := by
  rw [← lift_original]
  exact lower_bound velocity jet _

theorem physical_lower_square_bound (velocity : PhysicalSpace) (jet : Fin 4 → PhysicalSpace)
    (v : NativeWindowAbsoluteTimePhysicalMatter.Spinor) :
    ‖(WithLp.toLp 2 (NativeWindowAbsoluteTimePhysicalMatter.extension
      (NativeWindowAbsoluteTimePhysicalMatter.lower velocity jet) v) : Full NativeWindowAbsoluteTimeFourier.Fiber)‖^2 ≤
      5*cap^2*(density velocity^2+(∑ direction : Fin 4,‖jet direction‖^2))*
        ‖(WithLp.toLp 2 (fun entry : Fin 4 × Fin 2 => v entry.1 entry.2) : SpinFiber NativeWindowAbsoluteTimeFourier.Fiber)‖^2 := by
  rw [← lift_original]
  exact lower_square_bound velocity jet _

end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteLowerBound
