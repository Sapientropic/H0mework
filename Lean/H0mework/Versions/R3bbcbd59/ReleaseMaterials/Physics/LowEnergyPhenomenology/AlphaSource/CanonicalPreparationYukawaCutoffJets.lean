import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaUncutDomain

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumUncutYukawa
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair GaussFockWeights
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open GaussNativePotential GaussYukawaCoefficient GaussRadialDomain
open PreparationVacuumYukawaTransport PreparationVacuumGradedTransport
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets
open PreparationVacuumNonlinearFieldCurve CanonicalGradedLocalCurrent
open Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators Distributions
local instance : NormedAlgebra ℝ Fiber:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _

def rate (f : Field289) (u : Parameter) : ℝ:=1-reciprocal (fieldCoordinateCurve f u.1 u.2)
def rateFirst (f : Field289) (u : Parameter) : ℝ:=fderiv ℝ (rate f) u (1,0)
def rateSecond (f : Field289) (u : Parameter) : ℝ:=fderiv ℝ (rateFirst f) u (1,0)

theorem rate_smooth (f : Field289) (u : Parameter) (inside : u.2∈physicalChart) : ContDiffAt ℝ ∞ (rate f) u :=
  contDiffAt_const.sub (reciprocal_smooth.contDiffAt.comp u (field_curve_smooth f u.1 ⟨u.2,inside⟩))

theorem rateFirst_smooth (f : Field289) (u : Parameter) (inside : u.2∈physicalChart) : ContDiffAt ℝ ∞ (rateFirst f) u :=
  ((rate_smooth f u inside).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem rateSecond_smooth (f : Field289) (u : Parameter) (inside : u.2∈physicalChart) : ContDiffAt ℝ ∞ (rateSecond f) u :=
  ((rateFirst_smooth f u inside).fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

theorem rate_derivative (f : Field289) (r : ℝ) (z : physicalChart) :
    HasDerivAt (fun s=>rate f (s,z.val)) (rateFirst f (r,z.val)) r :=by
  have h:=(rate_smooth f (r,z.val) z.property).differentiableAt (by simp) |>.hasFDerivAt
  convert! h.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r z.val)) using 1

theorem rateFirst_derivative (f : Field289) (r : ℝ) (z : physicalChart) :
    HasDerivAt (fun s=>rateFirst f (s,z.val)) (rateSecond f (r,z.val)) r :=by
  have h:=(rateFirst_smooth f (r,z.val) z.property).differentiableAt (by simp) |>.hasFDerivAt
  convert! h.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r z.val)) using 1

def compactSlope (f : Field289) (phi : Localizer) (z : SourceCoordinateSlice) : Fiber :=
  (phi z:ℂ) • slopeFiber f z

theorem compactFiber_affine (f : Field289) (phi : Localizer) (r : ℝ) (z : SourceCoordinateSlice) :
    compactFiber f phi (r,z)=compactFiber f phi (0,z)+r • compactSlope f phi z :=by
  unfold compactFiber compactSlope
  rw [uncutFiber_affine f r z,smul_add,smul_comm (phi z:ℂ) r]

theorem compactSlope_smooth (f : Field289) (phi : Localizer) : ContDiff ℝ ∞ (compactSlope f phi) :=by
  have eq : compactSlope f phi=fun z=>compactFiber f phi (1,z)-compactFiber f phi (0,z) :=by
    funext z;rw [compactFiber_affine f phi 1 z,one_smul,add_sub_cancel_left]
  rw [eq]
  exact ((compactFiber_smooth f phi).comp (contDiff_const.prodMk contDiff_id)).sub
    ((compactFiber_smooth f phi).comp (contDiff_const.prodMk contDiff_id))

theorem compactFiber_derivative (f : Field289) (phi : Localizer) (r : ℝ) (z : SourceCoordinateSlice) :
    HasDerivAt (fun s=>compactFiber f phi (s,z)) (compactSlope f phi z) r :=by
  have h:=((hasDerivAt_id r).smul_const (compactSlope f phi z)).const_add (compactFiber f phi (0,z))
  simpa only [id_eq,one_smul] using h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s=>compactFiber_affine f phi s z)

lemma geometric_step {E : Type*} [AddCommGroup E] [Module ℝ E] (W : E) (q : ℝ) (n : ℕ) :
    W-((1-q) • W+q • (W-q^(n+1) • W))=q^(n+2) • W :=by
  rw [show n+2=(n+1)+1 by omega,pow_succ]
  module

theorem cutFiber_residual (n : ℕ) (z : SourceCoordinateSlice) :
    sourceMap (scalarField z)-cutFiber n z=(1-reciprocal z)^(n+1) • sourceMap (scalarField z) :=by
  have base : normalized z=reciprocal z • sourceMap (scalarField z) :=by
    change sourceMap ((radius z)⁻¹ • scalarField z)=_
    exact sourceMap.map_smul _ _
  induction n with
  | zero=>
    change sourceMap (scalarField z)-normalized z=(1-reciprocal z)^(0+1) • sourceMap (scalarField z)
    rw [base,pow_one]
    simpa only [one_smul] using (sub_smul (1:ℝ) (reciprocal z) (sourceMap (scalarField z))).symm
  | succ n ih=>
    have h : cutFiber n z=sourceMap (scalarField z)-(1-reciprocal z)^(n+1) • sourceMap (scalarField z) :=by
      rw [←ih];abel
    change sourceMap (scalarField z)-(normalized z+((1-reciprocal z:ℝ):ℂ) • cutFiber n z)=_
    have castsmul : ((1-reciprocal z:ℝ):ℂ) • cutFiber n z=(1-reciprocal z) • cutFiber n z :=
      (RCLike.real_smul_eq_coe_smul (K:=ℂ) (1-reciprocal z) (cutFiber n z)).symm
    rw [base,castsmul,h]
    simpa only [sub_sub_cancel] using geometric_step (sourceMap (scalarField z)) (1-reciprocal z) n

theorem coefficient_residual (f : Field289) (phi : Localizer) (n : ℕ) (r : ℝ) (z : SourceCoordinateSlice) :
    compactFiber f phi (r,z)-coefficientJet f n phi 0 (r,z)=(rate f (r,z))^(n+1) • compactFiber f phi (r,z) :=by
  change (phi z:ℂ) • uncutFiber f r z-(phi z:ℂ) • cutFiber n (fieldCoordinateCurve f r z)=_
  calc
    _=(phi z:ℂ) • (uncutFiber f r z-cutFiber n (fieldCoordinateCurve f r z)) :=(smul_sub _ _ _).symm
    _=(phi z:ℂ) • ((rate f (r,z))^(n+1) • uncutFiber f r z) :=congrArg (fun A : Fiber=>(phi z:ℂ) • A) (cutFiber_residual n _)
    _=_ :=smul_comm _ _ _

def errorFirst (f : Field289) (phi : Localizer) (n : ℕ) (u : Parameter) : Fiber :=
  (((n+2:ℕ):ℝ)*(rate f u)^(n+1)*rateFirst f u) • compactFiber f phi u+
    (rate f u)^(n+2) • compactSlope f phi u.2

def errorSecond (f : Field289) (phi : Localizer) (n : ℕ) (u : Parameter) : Fiber :=
  (((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)*(rate f u)^n*(rateFirst f u)^2) • compactFiber f phi u+
    (((n+2:ℕ):ℝ)*(rate f u)^(n+1)*rateSecond f u) • compactFiber f phi u+
    (2*((n+2:ℕ):ℝ)*(rate f u)^(n+1)*rateFirst f u) • compactSlope f phi u.2

lemma scalar_power_first (q q' : ℝ→ℝ) (n : ℕ) (r : ℝ) (hq : HasDerivAt q (q' r) r) :
    HasDerivAt (fun s=>(q s)^(n+2)) (((n+2:ℕ):ℝ)*(q r)^(n+1)*q' r) r :=by
  convert! hq.pow (n+2) using 1

lemma scalar_power_coefficient (q q' : ℝ→ℝ) (q'' : ℝ) (n : ℕ) (r : ℝ)
    (hq : HasDerivAt q (q' r) r) (hq' : HasDerivAt q' q'' r) :
    HasDerivAt (fun s=>((n+2:ℕ):ℝ)*(q s)^(n+1)*q' s)
      (((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)*(q r)^n*(q' r)^2+((n+2:ℕ):ℝ)*(q r)^(n+1)*q'') r :=by
  have h:=((hq.pow (n+1)).const_mul ((n+2:ℕ):ℝ)).mul hq'
  convert! h using 1
  simp only [Pi.pow_apply,show n+1-1=n by omega]
  ring

theorem residual_first (f : Field289) (phi : Localizer) (n : ℕ) (r : ℝ) (z : physicalChart) :
    HasDerivAt (fun s=>(rate f (s,z.val))^(n+2) • compactFiber f phi (s,z.val)) (errorFirst f phi n (r,z.val)) r :=by
  have h:=(scalar_power_first (fun s=>rate f (s,z.val)) (fun s=>rateFirst f (s,z.val)) n r (rate_derivative f r z)).smul (compactFiber_derivative f phi r z.val)
  convert! h using 1
  exact add_comm _ _

theorem residual_second (f : Field289) (phi : Localizer) (n : ℕ) (r : ℝ) (z : physicalChart) :
    HasDerivAt (fun s=>errorFirst f phi n (s,z.val)) (errorSecond f phi n (r,z.val)) r :=by
  have h:=((scalar_power_coefficient (fun s=>rate f (s,z.val)) (fun s=>rateFirst f (s,z.val)) (rateSecond f (r,z.val)) n r (rate_derivative f r z) (rateFirst_derivative f r z)).smul
    (compactFiber_derivative f phi r z.val)).add
    ((scalar_power_first (fun s=>rate f (s,z.val)) (fun s=>rateFirst f (s,z.val)) n r (rate_derivative f r z)).smul_const (compactSlope f phi z.val))
  convert! h using 1
  unfold errorSecond
  module

theorem coefficient_first_residual (f : Field289) (phi : Localizer) (n : ℕ) (r : ℝ) (z : physicalChart) :
    compactSlope f phi z.val-coefficientJet f (n+1) phi 1 (r,z.val)=errorFirst f phi n (r,z.val) :=by
  have left:=(compactFiber_derivative f phi r z.val).sub (coefficientJet_derivative f (n+1) 0 phi r z.val)
  have right:=residual_first f phi n r z
  have same : (fun s=>compactFiber f phi (s,z.val)-coefficientJet f (n+1) phi 0 (s,z.val))=
      (fun s=>(rate f (s,z.val))^(n+2) • compactFiber f phi (s,z.val)) :=by
    funext s;exact coefficient_residual f phi (n+1) s z.val
  have left2 : HasDerivAt (fun s=>compactFiber f phi (s,z.val)-coefficientJet f (n+1) phi 0 (s,z.val))
      (compactSlope f phi z.val-coefficientJet f (n+1) phi 1 (r,z.val)) r :=by convert! left using 1
  rw [same] at left2
  exact left2.unique right

theorem coefficient_second_residual (f : Field289) (phi : Localizer) (n : ℕ) (r : ℝ) (z : physicalChart) :
    -coefficientJet f (n+1) phi 2 (r,z.val)=errorSecond f phi n (r,z.val) :=by
  have left:=(hasDerivAt_const r (compactSlope f phi z.val)).sub (coefficientJet_derivative f (n+1) 1 phi r z.val)
  have right:=residual_second f phi n r z
  have same : (fun s=>compactSlope f phi z.val-coefficientJet f (n+1) phi 1 (s,z.val))=(fun s=>errorFirst f phi n (s,z.val)) :=by
    funext s;exact coefficient_first_residual f phi n s z
  have left2 : HasDerivAt (fun s=>compactSlope f phi z.val-coefficientJet f (n+1) phi 1 (s,z.val))
      (-coefficientJet f (n+1) phi 2 (r,z.val)) r :=by convert! left using 1;simp only [zero_sub]
  rw [same] at left2
  exact left2.unique right

def controlVector (f : Field289) (phi : Localizer) (u : Parameter) : Fin 5→ℝ :=
  ![radius (fieldCoordinateCurve f u.1 u.2),‖compactFiber f phi u‖,‖compactSlope f phi u.2‖,|rateFirst f u|,|rateSecond f u|]

theorem controlVector_continuous (f : Field289) (phi : Localizer) (u : Parameter) (hz : u.2∈physicalChart) :
    ContinuousAt (controlVector f phi) u :=by
  apply continuousAt_pi.mpr;intro i
  fin_cases i
  · exact (radius_smooth.contDiffAt.comp u (field_curve_smooth f u.1 ⟨u.2,hz⟩)).continuousAt
  · exact (compactFiber_smooth f phi).continuous.continuousAt.norm
  · exact ((compactSlope_smooth f phi).continuous.continuousAt.comp continuous_snd.continuousAt).norm
  · exact (rateFirst_smooth f u hz).continuousAt.abs
  · exact (rateSecond_smooth f u hz).continuousAt.abs

theorem envelope_exists (f : Field289) (phi : Localizer) (center : ℝ) :
    ∃C : ℝ,2≤ C ∧ ∀r z,|r-center|≤1 → z∈tsupport phi →
      radius (fieldCoordinateCurve f r z)≤ C ∧ ‖compactFiber f phi (r,z)‖≤ C ∧
      ‖compactSlope f phi z‖≤ C ∧ |rateFirst f (r,z)|≤ C ∧ |rateSecond f (r,z)|≤ C :=by
  have hc : ContinuousOn (controlVector f phi) (Icc (center-1) (center+1) ×ˢ tsupport phi) :=by
    intro u hu;exact (controlVector_continuous f phi u (phi.tsupport_subset hu.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod phi.hasCompactSupport).exists_bound_of_continuousOn hc
  refine ⟨max 2 C,le_max_left _ _,?_⟩
  intro r z small inside
  have hr : r∈Icc (center-1) (center+1) :=by have h:=abs_le.mp small;constructor <;> linarith
  have h (i : Fin 5) : controlVector f phi (r,z) i ≤ max 2 C :=
    (le_abs_self _).trans ((norm_le_pi_norm (controlVector f phi (r,z)) i).trans ((hC (r,z) ⟨hr,inside⟩).trans (le_max_right _ _)))
  exact ⟨h 0,h 1,h 2,h 3,h 4⟩

def envelope (f : Field289) (phi : Localizer) (center : ℝ) : ℝ:=(envelope_exists f phi center).choose

theorem envelope_ge_two (f : Field289) (phi : Localizer) (center : ℝ) : 2≤ envelope f phi center :=
  (envelope_exists f phi center).choose_spec.1

theorem envelope_bounds (f : Field289) (phi : Localizer) (center r : ℝ) (z : SourceCoordinateSlice)
    (small : |r-center|≤1) (inside : z∈tsupport phi) :
    radius (fieldCoordinateCurve f r z)≤ envelope f phi center ∧ ‖compactFiber f phi (r,z)‖≤ envelope f phi center ∧
      ‖compactSlope f phi z‖≤ envelope f phi center ∧ |rateFirst f (r,z)|≤ envelope f phi center ∧ |rateSecond f (r,z)|≤ envelope f phi center :=
  (envelope_exists f phi center).choose_spec.2 r z small inside

def envelopeRate (f : Field289) (phi : Localizer) (center : ℝ) : ℝ:=1-(envelope f phi center)⁻¹

theorem envelopeRate_range (f : Field289) (phi : Localizer) (center : ℝ) :
    0≤ envelopeRate f phi center ∧ envelopeRate f phi center<1 :=by
  have h:=envelope_ge_two f phi center
  have positive : 0<envelope f phi center :=by linarith
  have inverse:=inv_le_one_of_one_le₀ (by linarith : 1≤ envelope f phi center)
  have ip:=inv_pos.mpr positive
  dsimp only [envelopeRate]
  constructor <;> linarith

theorem rate_control (f : Field289) (phi : Localizer) (center r : ℝ) (z : SourceCoordinateSlice)
    (small : |r-center|≤1) (inside : z∈tsupport phi) :
    0≤ rate f (r,z) ∧ rate f (r,z)≤ envelopeRate f phi center :=by
  have hy:=radius_pos (fieldCoordinateCurve f r z)
  have h:=one_le_radius (fieldCoordinateCurve f r z)
  have bound:=(envelope_bounds f phi center r z small inside).1
  have lo:=inv_le_one_of_one_le₀ h
  have hi:=inv_anti₀ hy bound
  dsimp only [rate,reciprocal,envelopeRate]
  constructor <;> linarith

lemma geometric_jet_decay (q C : ℝ) (hq : 0≤ q) (hlt : q<1) :
    Tendsto (fun n : ℕ=>((n+2:ℕ):ℝ)^2*q^n*C) atTop (𝓝 0) :=by
  have a:=tendsto_pow_const_mul_const_pow_of_lt_one 2 hq hlt
  have b:=tendsto_pow_const_mul_const_pow_of_lt_one 1 hq hlt
  have c:=tendsto_pow_atTop_nhds_zero_of_lt_one hq hlt
  have all:=((a.add (b.const_mul 4)).add (c.const_mul 4)).mul_const C
  convert! all using 1
  · funext n;simp only [Nat.cast_add,Nat.cast_ofNat,pow_one];ring
  · ring

def scalarBound (Q C : ℝ) (n : ℕ) (k : Fin 3) : ℝ :=
  ![Q^(n+2)*C,
    (((n+2:ℕ):ℝ)*Q^(n+1)*C)*C+Q^(n+2)*C,
    (((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)*Q^n*C^2)*C+
      (((n+2:ℕ):ℝ)*Q^(n+1)*C)*C+(2*((n+2:ℕ):ℝ)*Q^(n+1)*C)*C] k

theorem scalarBound_tendsto (Q C : ℝ) (hq : 0≤ Q) (hlt : Q<1) (k : Fin 3) :
    Tendsto (fun n=>scalarBound Q C n k) atTop (𝓝 0) :=by
  have a:=tendsto_pow_const_mul_const_pow_of_lt_one 2 hq hlt
  have b:=tendsto_pow_const_mul_const_pow_of_lt_one 1 hq hlt
  have c:=tendsto_pow_atTop_nhds_zero_of_lt_one hq hlt
  fin_cases k
  · convert! (c.mul_const (Q^2*C)) using 1
    · funext n;dsimp [scalarBound];rw [pow_add];ring
    · ring
  · have h:=((b.mul_const (Q*C^2)).add (c.mul_const (2*Q*C^2+Q^2*C)))
    convert! h using 1
    · funext n;dsimp [scalarBound];simp only [pow_add,Nat.cast_add,Nat.cast_ofNat,pow_one];ring
    · ring
  · have h:=((a.mul_const (C^3)).add (b.mul_const (3*C^3+3*Q*C^2))).add
      (c.mul_const (2*C^3+6*Q*C^2))
    convert! h using 1
    · funext n;dsimp [scalarBound];simp only [pow_add,Nat.cast_add,Nat.cast_ofNat,pow_one];ring
    · ring

lemma three_norm_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q q1 q2 Q C : ℝ) (n : ℕ) (W V : E) (hq : 0≤ q) (upper : q≤ Q)
    (hC : 0≤ C) (h1 : |q1|≤ C) (h2 : |q2|≤ C) (hW : ‖W‖≤ C) (hV : ‖V‖≤ C) :
    ‖q^(n+2) • W‖≤ scalarBound Q C n 0 ∧
    ‖(((n+2:ℕ):ℝ)*q^(n+1)*q1) • W+q^(n+2) • V‖≤ scalarBound Q C n 1 ∧
    ‖(((n+2:ℕ):ℝ)*((n+1:ℕ):ℝ)*q^n*q1^2) • W+
      (((n+2:ℕ):ℝ)*q^(n+1)*q2) • W+(2*((n+2:ℕ):ℝ)*q^(n+1)*q1) • V‖≤ scalarBound Q C n 2 :=by
  have hQ : 0≤ Q:=hq.trans upper
  have p (k : ℕ) : q^k≤ Q^k:=pow_le_pow_left₀ hq upper k
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_pow,abs_of_nonneg hq]
    exact mul_le_mul (p _) hW (norm_nonneg _) (pow_nonneg hQ _)
  constructor
  · apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg hq,abs_of_nonneg (show (0:ℝ)≤(n+2:ℕ) from Nat.cast_nonneg _)]
    dsimp [scalarBound]
    gcongr
  · apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg hq,
      abs_of_nonneg (show (0:ℝ)≤(n+2:ℕ) from Nat.cast_nonneg _),abs_of_nonneg (show (0:ℝ)≤(n+1:ℕ) from Nat.cast_nonneg _),abs_of_pos (by norm_num : (0:ℝ)<2)]
    dsimp [scalarBound]
    gcongr

def errorBound (f : Field289) (phi : Localizer) (center : ℝ) (n : ℕ) (k : Fin 3) : ℝ :=
  scalarBound (envelopeRate f phi center) (envelope f phi center) n k

theorem errorBound_tendsto (f : Field289) (phi : Localizer) (center : ℝ) (k : Fin 3) :
    Tendsto (fun n=>errorBound f phi center n k) atTop (𝓝 0) :=
  scalarBound_tendsto _ _ (envelopeRate_range f phi center).1 (envelopeRate_range f phi center).2 k

def uncutCoefficient (f : Field289) (phi : Localizer) (k : Fin 3) (u : Parameter) : Fiber :=
  match k.val with
  | 0=>compactFiber f phi u
  | 1=>compactSlope f phi u.2
  | _=>0

theorem uncutCoefficient_smooth (f : Field289) (phi : Localizer) (k : Fin 3) :
    ContDiff ℝ ∞ (uncutCoefficient f phi k) :=by
  fin_cases k
  · exact compactFiber_smooth f phi
  · exact (compactSlope_smooth f phi).comp contDiff_snd
  · exact contDiff_const

theorem uncutCoefficient_number (f : Field289) (phi : Localizer) (k : Fin 3) (u : Parameter) (w : ℕ→ℂ) :
    Commute (weight w) (uncutCoefficient f phi k u) :=by
  fin_cases k
  · exact (sourceMap_number (scalarField (fieldCoordinateCurve f u.1 u.2)) w).smul_right (phi u.2:ℂ)
  · exact (sourceMap_number ((fieldVector f u.2).2.1:Scalar) w).smul_right (phi u.2:ℂ)
  · exact Commute.zero_right _

theorem uncutCoefficient_zero (f : Field289) (phi : Localizer) (k : Fin 3) (r : ℝ) (z : SourceCoordinateSlice)
    (outside : z∉tsupport phi) : uncutCoefficient f phi k (r,z)=0 :=by
  fin_cases k
  · change (phi z:ℂ) • uncutFiber f r z=0
    rw [image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
    exact zero_smul ℂ (uncutFiber f r z)
  · change (phi z:ℂ) • slopeFiber f z=0
    rw [image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
    exact zero_smul ℂ (slopeFiber f z)
  · rfl

theorem coefficient_error_bound (f : Field289) (phi : Localizer) (center r : ℝ) (small : |r-center|≤1)
    (n : ℕ) (k : Fin 3) (z : physicalChart) :
    ‖uncutCoefficient f phi k (r,z.val)-coefficientJet f (n+1) phi k.val (r,z.val)‖≤ errorBound f phi center n k :=by
  have hC : 0≤envelope f phi center :=by have h:=envelope_ge_two f phi center;linarith
  have hQ:=(envelopeRate_range f phi center).1
  by_cases inside : z.val∈tsupport phi
  · have controls:=envelope_bounds f phi center r z.val small inside
    have rateBound:=rate_control f phi center r z.val small inside
    have bounds:=three_norm_bounds (rate f (r,z.val)) (rateFirst f (r,z.val)) (rateSecond f (r,z.val))
      (envelopeRate f phi center) (envelope f phi center) n (compactFiber f phi (r,z.val)) (compactSlope f phi z.val)
      rateBound.1 rateBound.2 hC controls.2.2.2.1 controls.2.2.2.2 controls.2.1 controls.2.2.1
    fin_cases k
    · change ‖compactFiber f phi (r,z.val)-coefficientJet f (n+1) phi 0 (r,z.val)‖≤ _
      rw [coefficient_residual];exact bounds.1
    · change ‖compactSlope f phi z.val-coefficientJet f (n+1) phi 1 (r,z.val)‖≤ _
      rw [coefficient_first_residual];exact bounds.2.1
    · change ‖0-coefficientJet f (n+1) phi 2 (r,z.val)‖≤ _
      rw [zero_sub,coefficient_second_residual];exact bounds.2.2
  · rw [uncutCoefficient_zero f phi k r z.val inside,coefficientJet_zero f (n+1) k.val phi r z.val inside,sub_self,norm_zero]
    fin_cases k <;> dsimp [errorBound,scalarBound] <;> positivity

def uncutJetOperator (f : Field289) (phi : Localizer) (k : Fin 3) (r : ℝ) : H →L[ℂ] H :=
  match k.val with
  | 0=>uncutOperator f phi r
  | 1=>uncutSlope f phi
  | _=>0

theorem uncutJetOperator_core (f : Field289) (phi : Localizer) (k : Fin 3) (r : ℝ) (a : QuantumTest) :
    uncutJetOperator f phi k r (embed a)=embed (localMultiplier (fun z=>uncutCoefficient f phi k (r,z))
      (fun _=>((uncutCoefficient_smooth f phi k).comp (contDiff_const.prodMk contDiff_id)).contDiffAt) a) :=by
  fin_cases k
  · exact uncutOperator_core f phi r a
  · change (uncutOperator f phi 1-uncutOperator f phi 0) (embed a)=_
    rw [sub_apply,uncutOperator_core,uncutOperator_core,←map_sub]
    apply congrArg embed;apply DFunLike.ext;intro z
    change compactFiber f phi (1,z) (a z)-compactFiber f phi (0,z) (a z)=compactSlope f phi z (a z)
    rw [compactFiber_affine f phi 1 z,one_smul,add_apply,add_sub_cancel_left]
  · change (0:H)=embed _
    rw [←map_zero embed]
    apply congrArg embed;apply DFunLike.ext;intro z
    rfl

theorem operator_error_bound (f : Field289) (phi : Localizer) (center r : ℝ) (small : |r-center|≤1)
    (n : ℕ) (k : Fin 3) :
    ‖uncutJetOperator f phi k r-jetOperator f (n+1) k.val phi r‖≤ errorBound f phi center n k :=by
  let E : SourceCoordinateSlice→Fiber:=fun z=>uncutCoefficient f phi k (r,z)-coefficientJet f (n+1) phi k.val (r,z)
  have smooth : ContDiff ℝ ∞ E:=((uncutCoefficient_smooth f phi k).sub
    (coefficientJet_smooth f (n+1) k.val phi)).comp (contDiff_const.prodMk contDiff_id)
  have commutes (z : physicalChart) (w : ℕ→ℂ) : Commute (weight w) (E z.val) :=
    (uncutCoefficient_number f phi k (r,z.val) w).sub_right (coefficientJet_number f (n+1) k.val phi (r,z.val) w)
  have nonnegative : 0≤errorBound f phi center n k :=by
    have hC : 0≤envelope f phi center :=by have h:=envelope_ge_two f phi center;linarith
    have hQ:=(envelopeRate_range f phi center).1
    fin_cases k <;> dsimp [errorBound,scalarBound] <;> positivity
  apply core_operator_bound _ _ nonnegative
  intro a
  have point (z : physicalChart) (v : FockFiber) : ‖E z.val v‖≤errorBound f phi center n k*‖v‖ :=
    ((E z.val).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (coefficient_error_bound f phi center r small n k z) (norm_nonneg v))
  have bound:=GaussBoundedMultiplier.action_bound E (fun _=>smooth.contDiffAt) commutes
    (errorBound f phi center n k) nonnegative point a
  have source : localMultiplier E (fun _=>smooth.contDiffAt) a=
      localMultiplier (fun z=>uncutCoefficient f phi k (r,z))
        (fun _=>((uncutCoefficient_smooth f phi k).comp (contDiff_const.prodMk contDiff_id)).contDiffAt) a-
      localMultiplier (fun z=>coefficientJet f (n+1) phi k.val (r,z))
        (fun _=>(jetTest f (n+1) k.val phi r).contDiff.contDiffAt) a :=by
    apply DFunLike.ext;intro z;rfl
  rw [source,map_sub] at bound
  simpa only [sub_apply,uncutJetOperator_core,jetOperator_core] using bound

theorem cutoffJets_uniform (f : Field289) (phi : Localizer) (center : ℝ) (k : Fin 3) :
    TendstoUniformlyOn (fun n r=>jetOperator f n k.val phi r) (uncutJetOperator f phi k)
      atTop (Icc (center-1) (center+1)) :=by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon positive
  have decay:=(errorBound_tendsto f phi center k).comp (tendsto_sub_atTop_nat 1)
  filter_upwards [eventually_ge_atTop 1,decay.eventually (gt_mem_nhds positive)] with n hn he
  intro r hr
  have small : |r-center|≤1:=abs_le.mpr (by constructor <;> linarith [hr.1,hr.2])
  have h:=operator_error_bound f phi center r small (n-1) k
  rw [Nat.sub_add_cancel hn] at h
  rw [dist_eq_norm]
  exact h.trans_lt he

theorem cutoffJets_limit (f : Field289) (phi : Localizer) (r : ℝ) (k : Fin 3) :
    Tendsto (fun n=>jetOperator f n k.val phi r) atTop (𝓝 (uncutJetOperator f phi k r)) :=
  (cutoffJets_uniform f phi r k).tendsto_at (by constructor <;> linarith)

theorem first_derivative_limit (f : Field289) (phi : Localizer) (r : ℝ) :
    Tendsto (fun n=>deriv (jetOperator f n 0 phi) r) atTop (𝓝 (deriv (uncutOperator f phi) r)) :=by
  have original (n : ℕ) : deriv (jetOperator f n 0 phi) r=jetOperator f n 1 phi r :=
    (jetOperator_derivative f n 0 phi r).deriv
  simp_rw [original,(uncutOperator_derivative f phi r).deriv]
  exact cutoffJets_limit f phi r 1

theorem second_derivative_limit (f : Field289) (phi : Localizer) (r : ℝ) :
    Tendsto (fun n=>deriv (deriv (jetOperator f n 0 phi)) r) atTop (𝓝 (deriv (deriv (uncutOperator f phi)) r)) :=by
  have original (n : ℕ) : deriv (jetOperator f n 0 phi)=jetOperator f n 1 phi :=
    funext fun s=>(jetOperator_derivative f n 0 phi s).deriv
  have next (n : ℕ) : deriv (jetOperator f n 1 phi) r=jetOperator f n 2 phi r :=
    (jetOperator_derivative f n 1 phi r).deriv
  have uncut : deriv (uncutOperator f phi)=fun _=>uncutSlope f phi :=
    funext fun s=>(uncutOperator_derivative f phi s).deriv
  simp_rw [original,next,uncut]
  rw [deriv_const]
  exact cutoffJets_limit f phi r 2

end LowEnergy.PreparationVacuumUncutYukawa
