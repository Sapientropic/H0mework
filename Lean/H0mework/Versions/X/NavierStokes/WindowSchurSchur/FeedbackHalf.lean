import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.RieszControl
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeightedInverse

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointSpatialHalf
open NativeUnheatedTreeRieszKernel (Wave E)
open NativeUnheatedSexticLatticePower
open NativeUnheatedTreeRieszPermutations
noncomputable section

def kernel (strong : Bool) (p q : Wave) : ℝ :=
  if strong then density 2 p*density 1 q else density 2 p*density 1 (p+q)

theorem kernel_nonnegative (strong : Bool) (p q : Wave) : 0 ≤ kernel strong p q := by
  cases strong <;> simp only [kernel,Bool.false_eq_true,if_false,if_true] <;>
    positivity [density_positive 2 p,density_positive 1 q,density_positive 1 (p+q)]

private theorem cube_product (x y : ℝ) (x0 : 0 ≤ x) (y0 : 0 ≤ y) : x*y^2 ≤ x^3+y^3 := by
  have square := mul_nonneg (sq_nonneg (x-y)) (by linarith : 0 ≤ x+2*y)
  nlinarith only [square,mul_nonneg x0 (sq_nonneg x),mul_nonneg y0 (sq_nonneg y)]

theorem kernel_bound (strong : Bool) (p q : Wave) :
    kernel strong p q ≤ radical (p+q)*density 2 p*density 2 q+
      radical p*density 2 q*density 2 (p+q)+radical q*density 2 p*density 2 (p+q) := by
  have a := radical_positive p
  have b := radical_positive q
  have c := radical_positive (p+q)
  have first := cube_product (radical q) (radical (p+q)) b.le c.le
  have last := cube_product (radical (p+q)) (radical q) c.le b.le
  have ap : 0 ≤ radical p^3 := pow_nonneg a.le 3
  apply (mul_le_mul_iff_right₀ (show 0 < radical p^2*radical q^2*radical (p+q)^2 by positivity)).mp
  cases strong <;> simp only [kernel,Bool.false_eq_true,if_false,if_true,density] <;>
    field_simp [a.ne',b.ne',c.ne'] <;> nlinarith only [first,last,ap]

def term (strong : Bool) (L M T : E) (index : Wave × Wave) : ℝ :=
  kernel strong index.1 index.2*|L index.1| * |M index.2| * |T (index.1+index.2)|

theorem term_nonnegative (strong : Bool) (L M T : E) (index : Wave × Wave) :
    0 ≤ term strong L M T index := by
  unfold term
  positivity [kernel_nonnegative strong index.1 index.2]

theorem term_bound (strong : Bool) (L M T : E) (index : Wave × Wave) :
    term strong L M T index ≤ outputTerm L M T index+firstTerm L M T index+secondTerm L M T index := by
  have paid := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_bound strong index.1 index.2) (abs_nonneg (L index.1)))
    (abs_nonneg (M index.2))) (abs_nonneg (T (index.1+index.2)))
  exact paid.trans_eq (by unfold outputTerm firstTerm secondTerm; ring)

theorem summable (strong : Bool) (L M T : E) : Summable (term strong L M T) :=
  (((output_summable L M T).add (first_summable L M T)).add (second_summable L M T)).of_nonneg_of_le
    (term_nonnegative strong L M T) (term_bound strong L M T)

def cap : ℝ := 3*Real.sqrt NativeUnheatedRieszKernel.constant
theorem cap_nonnegative : 0 ≤ cap := by unfold cap; positivity

theorem bound (strong : Bool) (L M T : E) : (∑' index,term strong L M T index) ≤ cap*‖L‖*‖M‖*‖T‖ := by
  have paid := (summable strong L M T).tsum_le_tsum (term_bound strong L M T)
    (((output_summable L M T).add (first_summable L M T)).add (second_summable L M T))
  rw [((output_summable L M T).add (first_summable L M T)).tsum_add (second_summable L M T),
    (output_summable L M T).tsum_add (first_summable L M T)] at paid
  exact paid.trans ((add_le_add (add_le_add (output_bound L M T) (first_bound L M T))
    (second_bound L M T)).trans_eq (by unfold cap; ring))

def row (strong : Bool) (L M : E) (k : Wave) : ℝ := ∑' p,kernel strong p (k-p)*|L p| * |M (k-p)|

theorem row_nonnegative (strong : Bool) (L M : E) (k : Wave) : 0 ≤ row strong L M k :=
  tsum_nonneg fun p => by positivity [kernel_nonnegative strong p (k-p)]

theorem pair_summable (strong : Bool) (L M T : E) :
    Summable (fun x : Wave × Wave => kernel strong x.2 (x.1-x.2)*|L x.2| * |M (x.1-x.2)| * |T x.1|) := by
  have same (x : Wave × Wave) : kernel strong x.2 (x.1-x.2)*|L x.2| * |M (x.1-x.2)| * |T x.1|=
      term strong L M T (outputEquiv.symm x) := by simp [term,outputEquiv]
  simp_rw [same]
  exact outputEquiv.symm.summable_iff.mpr (summable strong L M T)

theorem row_summable (strong : Bool) (L M : E) (k : Wave) :
    Summable (fun p => kernel strong p (k-p)*|L p| * |M (k-p)|) := by
  have paid := (pair_summable strong L M (lp.single 2 k 1)).prod_factor k
  simpa only [lp.single_apply_self,abs_one,mul_one] using paid

theorem testing_bound (strong : Bool) (L M T : E) :
    (∑' k,row strong L M k*|T k|) ≤ cap*‖L‖*‖M‖*‖T‖ := by
  have same := (pair_summable strong L M T).tsum_prod
  have recognize (x : Wave × Wave) : kernel strong x.2 (x.1-x.2)*|L x.2| * |M (x.1-x.2)| * |T x.1|=
      term strong L M T (outputEquiv.symm x) := by simp [term,outputEquiv]
  simp only [tsum_mul_right] at same
  change _=(∑'k,row strong L M k*|T k|) at same
  rw [← same]
  simp_rw [recognize]
  rw [outputEquiv.symm.tsum_eq]
  exact bound strong L M T

def test (strong : Bool) (L M : E) (F : Finset Wave) : E := ∑ k∈F,lp.single 2 k (row strong L M k)

theorem test_apply (strong : Bool) (L M : E) (F : Finset Wave) (k : Wave) :
    test strong L M F k=if k∈F then row strong L M k else 0 := by
  classical
  simp only [test,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem test_square (strong : Bool) (L M : E) (F : Finset Wave) :
    ‖test strong L M F‖^2=∑ k∈F,row strong L M k^2 := by
  simpa only [test,ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
    lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (row strong L M) F

theorem row_square_bound (strong : Bool) (L M : E) (F : Finset Wave) :
    (∑ k∈F,row strong L M k^2) ≤ (cap*‖L‖*‖M‖)^2 := by
  classical
  have paid := testing_bound strong L M (test strong L M F)
  rw [tsum_eq_sum (s := F) (fun k outside => by simp only [test_apply,if_neg outside,abs_zero,mul_zero])] at paid
  have same : (∑ k∈F,row strong L M k*|test strong L M F k|)=∑ k∈F,row strong L M k^2 := by
    apply Finset.sum_congr rfl
    intro k inside
    rw [test_apply,if_pos inside,abs_of_nonneg (row_nonnegative strong L M k),pow_two]
  rw [same,← test_square] at paid
  have normed : ‖test strong L M F‖ ≤ cap*‖L‖*‖M‖ := by
    rcases (norm_nonneg (test strong L M F)).eq_or_lt with zero | positive
    · rw [← zero]; positivity [cap_nonnegative]
    · apply (mul_le_mul_iff_left₀ positive).mp
      rw [pow_two] at paid
      exact paid.trans_eq (by ring)
  rw [← test_square]
  exact pow_le_pow_left₀ (norm_nonneg _) normed 2

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWindowHistoryCreationGeometry (advection transport transport_row)
open NativeWindowFiniteGramFourier (fourierRead)

def input (F : Finset Wave) (n : ℕ) (a : Wave → ℂ) : E :=
  ∑ k∈F,lp.single 2 k (radical k^n*‖a k‖)

theorem input_apply (F : Finset Wave) (n : ℕ) (a : Wave → ℂ) (k : Wave) :
    input F n a k=if k∈F then radical k^n*‖a k‖ else 0 := by
  classical
  simp only [input,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]

theorem input_square (F : Finset Wave) (n : ℕ) (a : Wave → ℂ) :
    ‖input F n a‖^2=∑ k∈F,radical k^(2*n)*‖a k‖^2 := by
  have source := lp.norm_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (fun k => radical k^n*‖a k‖) F
  simpa only [input,ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,mul_pow,← pow_mul,Nat.mul_comm n 2] using source

def weight (strong : Bool) (k : Wave) : ℝ := if strong then 1 else density 1 k

theorem weight_nonnegative (strong : Bool) (k : Wave) : 0 ≤ weight strong k := by
  cases strong <;> simp only [weight,Bool.false_eq_true,if_false,if_true] <;> positivity [density_positive 1 k]

def inputOrder (strong : Bool) : ℕ := if strong then 3 else 2

theorem multiplier_bound (q : Wave) (j : Coordinate) :
    ‖NativePhysicalGradient.multiplier q j‖ ≤ (2*Real.pi)*radical q^2 := by
  have component : (q j : ℝ)^2 ≤ integerWaveNormSq q :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((q i : ℝ))) (Finset.mem_univ j)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [radical_positive q])).mp
  have same : ((2*Real.pi)*radical q^2)^2=(2*Real.pi)^2*mass q := by
    rw [mul_pow,← pow_mul,show (2 : ℕ)*2=4 from rfl,radical_fourth]
  rw [NativePhysicalGradient.multiplier_norm_sq,same]
  exact mul_le_mul_of_nonneg_left (component.trans (show integerWaveNormSq q ≤ mass q by unfold mass; linarith)) (sq_nonneg (2*Real.pi))

theorem input_term (strong : Bool) (F : Finset Wave) (a b : Wave → ℂ) (k q : Wave)
    (left : k-q∈F) (right : q∈F) :
    kernel strong (k-q) q*|input F 2 a (k-q)| * |input F (inputOrder strong) b q|=
      weight strong k*radical q^2*‖a (k-q)‖*‖b q‖ := by
  rw [input_apply,if_pos left,input_apply,if_pos right]
  rw [abs_of_nonneg (by positivity [radical_positive (k-q)]),abs_of_nonneg (by positivity [radical_positive q])]
  cases strong <;> simp only [kernel,weight,inputOrder,Bool.false_eq_true,if_false,if_true,sub_add_cancel,density,pow_one] <;>
    field_simp [(radical_positive (k-q)).ne',(radical_positive q).ne']

theorem shifted_summable (strong : Bool) (L M : E) (k : Wave) :
    Summable (fun q => kernel strong (k-q) q*|L (k-q)| * |M q|) := by
  have source := (Equiv.subLeft k).summable_iff.mpr (row_summable strong L M k)
  simpa only [Function.comp_def,Equiv.subLeft_apply,sub_sub_cancel] using source

theorem shifted_sum (strong : Bool) (L M : E) (k : Wave) :
    (∑' q,kernel strong (k-q) q*|L (k-q)| * |M q|)=row strong L M k := by
  have source := (Equiv.subLeft k).tsum_eq (fun p => kernel strong p (k-p)*|L p| * |M (k-p)|)
  simpa only [Equiv.subLeft_apply,sub_sub_cancel,row] using source

theorem advection_component (strong : Bool) (F : Finset Wave) (zero : 0∉F) (closed : FiniteModeNegClosed F)
    (u v : physicalSpace F) (i : Coordinate) (k : Wave) :
    weight strong k*‖fourierRead k (advection F zero closed u v i)‖ ≤
      (2*Real.pi)*∑ j : Coordinate,row strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) k := by
  rw [NativeWindowHistorySpatialTransport.advection_row,norm_neg]
  have triangle := norm_sum_le (Finset.univ : Finset Coordinate) (fun j => ∑ q∈F,
    if k-q∈F then u.1 (k-q) j*(NativePhysicalGradient.multiplier q j*v.1 q i) else 0)
  apply (mul_le_mul_of_nonneg_left triangle (weight_nonnegative strong k)).trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have rowTriangle := norm_sum_le F (fun q => if k-q∈F then u.1 (k-q) j*(NativePhysicalGradient.multiplier q j*v.1 q i) else 0)
  apply (mul_le_mul_of_nonneg_left rowTriangle (weight_nonnegative strong k)).trans
  rw [Finset.mul_sum]
  let L := input F 2 (fun p => u.1 p j)
  let T := input F (inputOrder strong) (fun q => v.1 q i)
  have each (q : Wave) (member : q∈F) :
      weight strong k*‖if k-q∈F then u.1 (k-q) j*(NativePhysicalGradient.multiplier q j*v.1 q i) else 0‖ ≤
        (2*Real.pi)*(kernel strong (k-q) q*|L (k-q)| * |T q|) := by
    by_cases inside : k-q∈F
    · rw [if_pos inside,norm_mul,norm_mul,input_term strong F _ _ k q inside member]
      have paid := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (multiplier_bound q j) (norm_nonneg (v.1 q i)))
        (mul_nonneg (weight_nonnegative strong k) (norm_nonneg (u.1 (k-q) j)))
      nlinarith only [paid]
    · rw [if_neg inside,norm_zero,mul_zero]
      positivity [kernel_nonnegative strong (k-q) q]
  have paid := Finset.sum_le_sum (s := F) each
  apply paid.trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2*Real.pi)
  rw [← shifted_sum strong L T k]
  exact (shifted_summable strong L T k).sum_le_tsum F (fun q _ => by positivity [kernel_nonnegative strong (k-q) q])

def moment (F : Finset Wave) (n : ℕ) (v : physicalSpace F) : ℝ :=
  ∑ i : Coordinate,‖input F n (fun k => v.1 k i)‖^2

theorem moment_nonnegative (F : Finset Wave) (n : ℕ) (v : physicalSpace F) : 0 ≤ moment F n v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem moment_original (F : Finset Wave) (n : ℕ) (v : physicalSpace F) :
    moment F n v=∑ k∈F,radical k^(2*n)*(∑ i : Coordinate,‖v.1 k i‖^2) := by
  simp only [moment,input_square]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

def outputSquare (strong : Bool) (F : Finset Wave) (v : physicalSpace F) : ℝ :=
  ∑ k∈F,weight strong k^2*(∑ i : Coordinate,‖v.1 k i‖^2)

theorem outputSquare_nonnegative (strong : Bool) (F : Finset Wave) (v : physicalSpace F) :
    0 ≤ outputSquare strong F v := Finset.sum_nonneg fun _ _ =>
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem sum_three (a : Coordinate → ℝ) : (∑j,a j)^2 ≤ 3*∑j,a j^2 := by
  have paid := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate) (fun _ => (1 : ℝ)) a
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one] using paid

theorem transport_bound (strong : Bool) (F : Finset Wave) (zero : 0∉F) (closed : FiniteModeNegClosed F)
    (nu : Viscosity) (u v : physicalSpace F) :
    outputSquare strong F (transport F zero closed nu u v) ≤
      (3*(2*Real.pi)^2*cap^2)*moment F 2 u*moment F (inputOrder strong) v := by
  have projection (k : Wave) (inside : k∈F) :
      (∑i : Coordinate,‖(transport F zero closed nu u v).1 k i‖^2) ≤
        ∑i : Coordinate,‖fourierRead k (advection F zero closed u v i)‖^2 := by
    have paid := ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness.transverseProjection_amplitudeSq_le
      k (fun h => zero (h ▸ inside)) (fun i => fourierRead k (advection F zero closed u v i))
    simpa only [transport_row,if_pos inside,ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry.complexCoordinateAmplitudeSq,Complex.normSq_eq_norm_sq] using paid
  have rowPaid (k : Wave) (i : Coordinate) :
      weight strong k^2*‖fourierRead k (advection F zero closed u v i)‖^2 ≤
        3*(2*Real.pi)^2*∑ j : Coordinate,
          row strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) k^2 := by
    have paid := pow_le_pow_left₀ (mul_nonneg (weight_nonnegative strong k) (norm_nonneg _))
      (advection_component strong F zero closed u v i k) 2
    rw [mul_pow,mul_pow] at paid
    have summed := mul_le_mul_of_nonneg_left (sum_three (fun j =>
      row strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) k)) (sq_nonneg (2*Real.pi))
    exact paid.trans (summed.trans_eq (by ring))
  calc
    outputSquare strong F (transport F zero closed nu u v) ≤
        ∑k∈F,∑i : Coordinate,weight strong k^2*‖fourierRead k (advection F zero closed u v i)‖^2 := by
      simp only [outputSquare,← Finset.mul_sum]
      exact Finset.sum_le_sum fun k inside => mul_le_mul_of_nonneg_left (projection k inside) (sq_nonneg _)
    _ ≤ ∑k∈F,∑i : Coordinate,3*(2*Real.pi)^2*∑j : Coordinate,
        row strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) k^2 :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i _ => rowPaid k i
    _ = 3*(2*Real.pi)^2*∑i : Coordinate,∑j : Coordinate,∑k∈F,
        row strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) k^2 := by
      simp only [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ 3*(2*Real.pi)^2*∑i : Coordinate,∑j : Coordinate,
        (cap*‖input F 2 (fun p => u.1 p j)‖*‖input F (inputOrder strong) (fun q => v.1 q i)‖)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        row_square_bound strong (input F 2 (fun p => u.1 p j)) (input F (inputOrder strong) (fun q => v.1 q i)) F) (by positivity)
    _ = _ := by
      simp only [mul_pow,← Finset.sum_mul,← Finset.mul_sum,moment]
      ring

open NativeWindowHistoryHeatDual (energy)

def energyCap (nu : Viscosity) : ℝ := 1+(nu.coeff*(2*Real.pi)^2)⁻¹

theorem energyCap_positive (nu : Viscosity) : 0 < energyCap nu := by unfold energyCap; positivity [nu.coeff_pos]

theorem weight_energy (nu : Viscosity) (k : Wave) :
    mass k ≤ energyCap nu*(1+nu.coeff*integerWaveViscousMultiplier k) := by
  have constant : 0 < nu.coeff*(2*Real.pi)^2 := by positivity [nu.coeff_pos]
  have cancel := mul_inv_cancel₀ constant.ne'
  have one : 0 ≤ (nu.coeff*(2*Real.pi)^2)⁻¹ := inv_nonneg.mpr constant.le
  have positive := mul_nonneg constant.le (integerWaveNormSq_nonneg k)
  have cancelRow := congrArg (fun x : ℝ => x*integerWaveNormSq k) cancel
  unfold mass energyCap integerWaveViscousMultiplier
  nlinarith only [cancelRow,one,positive]

theorem energy_original (nu : Viscosity) (F : Finset Wave) (zero : 0∉F) (v : physicalSpace F) :
    ‖coefficients F v‖^2+nu.coeff*curlPair F v.1 v.1=
      ∑ k∈F,(1+nu.coeff*integerWaveViscousMultiplier k)*(∑i : Coordinate,‖v.1 k i‖^2) := by
  have mass : ‖coefficients F v‖^2=∑ k∈F,∑i : Coordinate,‖v.1 k i‖^2 :=
    (real_inner_self_eq_norm_sq _).symm.trans (NativeWindowHistoryCreationGeometry.pairing_mass F v)
  rw [mass,NativeWindowHistoryCreationGeometry.curl_mass F zero]
  simp only [integerWaveViscousMultiplier,Finset.mul_sum,Finset.sum_add_distrib,add_mul,one_mul]
  ring

theorem moment_energy (nu : Viscosity) (M : ℕ) (v : physicalSpace (NativeWholeH1Mixed.modes M)) :
    moment (NativeWholeH1Mixed.modes M) 2 v ≤ energyCap nu*energy nu M v := by
  rw [moment_original]
  simp only [show 2*(2 : ℕ)=4 from rfl,radical_fourth]
  change _ ≤ energyCap nu*(‖coefficients (NativeWholeH1Mixed.modes M) v‖^2+
    nu.coeff*curlPair (NativeWholeH1Mixed.modes M) v.1 v.1)
  rw [energy_original nu _ (NativeWholeH1Mixed.modes_zero M),Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => (mul_le_mul_of_nonneg_right (weight_energy nu k)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans_eq (by ring)

theorem heat_weight (nu : Viscosity) (k : Wave) :
    radical k^6 ≤ energyCap nu^2*(density 1 k)^2*(1+nu.coeff*integerWaveViscousMultiplier k)^2 := by
  have original := pow_le_pow_left₀ (mass_positive k).le (weight_energy nu k) 2
  rw [mul_pow] at original
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (radical_positive k))).mp
  have first : radical k^6*radical k^2=mass k^2 := by
    rw [show radical k^6*radical k^2=(radical k^4)^2 by ring,radical_fourth]
  have last : energyCap nu^2*(density 1 k)^2*(1+nu.coeff*integerWaveViscousMultiplier k)^2*radical k^2=
      energyCap nu^2*(1+nu.coeff*integerWaveViscousMultiplier k)^2 := by
    simp only [density,pow_one,inv_pow]
    field_simp [(radical_positive k).ne']
  rw [mul_comm (radical k^2),first,mul_comm (radical k^2),last]
  exact original

theorem heat_gain (nu : Viscosity) (F : Finset Wave) (zero : 0∉F) (closed : FiniteModeNegClosed F)
    (z f : physicalSpace F)
    (equation : z+nu.coeff • NativeWindowOperatorGreen.laplacian F zero closed nu z=f) :
    moment F 3 z ≤ energyCap nu^2*outputSquare false F f := by
  have read (k : Wave) (i : Coordinate) : f.1 k i=(1+nu.coeff*integerWaveViscousMultiplier k) • z.1 k i := by
    have source := congrArg (fun v : physicalSpace F => v.1 k i) equation
    change z.1 k i+nu.coeff • (NativeWindowOperatorGreen.laplacian F zero closed nu z).1 k i=_ at source
    rw [NativeWindowOperatorGreen.laplacian_row,Pi.smul_apply,smul_smul] at source
    exact source.symm.trans (by simp only [add_smul,one_smul])
  rw [moment_original]
  simp only [show 2*(3 : ℕ)=6 from rfl,outputSquare,weight,Bool.false_eq_true,if_false,read,
    norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_right (heat_weight nu k) (sq_nonneg ‖z.1 k i‖)).trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointSpatialHalf
