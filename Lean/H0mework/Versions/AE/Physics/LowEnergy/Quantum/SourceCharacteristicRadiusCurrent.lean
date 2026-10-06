import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarVolumePressure
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCharacteristicRadiusCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare
open SourceScalarPairedTransport SourceLocalizedInverseFormPayment
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def orientation (negative : Bool) : ℝ := if negative then -Real.sqrt 6 else Real.sqrt 6
private theorem orientation_sq (negative : Bool) : orientation negative^2=6 := by
  cases negative <;> simp [orientation,Real.sq_sqrt (by norm_num : (0:ℝ)≤6)]

/-- Both characteristic clocks use the same original volume and scalar radius. -/
def characteristic (negative : Bool) (z : SourceCoordinateSlice) : ℝ :=
  Real.log (volume z)+orientation negative*radius z

private theorem characteristic_smooth (negative : Bool) (z : physicalChart) :
    ContDiffAt ℝ ∞ (characteristic negative) z.val :=
  (volume_smooth.contDiffAt.log (volume_pos z).ne').add (contDiffAt_const.mul radius_smooth.contDiffAt)

def characteristicAction (negative : Bool) : End := multiply (characteristic negative) (characteristic_smooth negative)

private def coframeGradient (i : Fin 6) (z : SourceCoordinateSlice) : ℝ := volumeGradient z i/volume z
private theorem coframe_gradient_smooth (i : Fin 6) (z : physicalChart) :
    ContDiffAt ℝ ∞ (coframeGradient i) z.val := by
  have hg : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice => volumeGradient x i) := by
    fin_cases i <;> dsimp [volumeGradient] <;> fun_prop
  exact hg.contDiffAt.div volume_smooth.contDiffAt (volume_pos z).ne'
private def coframeContact (i : Fin 6) : End := multiply (coframeGradient i) (coframe_gradient_smooth i)

private def nativeGradient (negative : Bool) (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  orientation negative*(inner ℝ (z.2.1 : Scalar) v.1/(4*radius z))
private theorem native_gradient_smooth (negative : Bool) (v : Ambient) : ContDiff ℝ ∞ (nativeGradient negative v) :=
  contDiff_const.mul (((scalarCoordinate.contDiff.inner ℝ contDiff_const).div
    (contDiff_const.mul radius_smooth) (fun z => mul_ne_zero (by norm_num) (radius_pos z).ne')))
private def nativeContact (negative : Bool) (v : Ambient) : End :=
  multiply (nativeGradient negative v) (fun _ => (native_gradient_smooth negative v).contDiffAt)

private theorem radius_derivative (z h : SourceCoordinateSlice) :
    fderiv ℝ radius z h=inner ℝ (z.2.1 : Scalar) (h.2.1 : Scalar)/(4*radius z) := by
  have hs := (((scalarCoordinate.hasFDerivAt (x := z)).norm_sq).mul_const (4⁻¹ : ℝ)).const_add 1
  simp only [←div_eq_mul_inv] at hs
  have hd := hs.sqrt (show 1+‖scalarCoordinate z‖^2/4≠0 by positivity)
  change HasFDerivAt radius _ z at hd
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul, two_smul]
  change (1/(2*radius z))*(4⁻¹*(inner ℝ (z.2.1 : Scalar) (h.2.1 : Scalar)+inner ℝ (z.2.1 : Scalar) (h.2.1 : Scalar)))=_
  ring

private theorem characteristic_derivative (negative : Bool) (z : physicalChart) (h : SourceCoordinateSlice) :
    fderiv ℝ (characteristic negative) z.val h=
      fderiv ℝ volume z.val h/volume z.val+
        orientation negative*(inner ℝ (z.val.2.1 : Scalar) (h.2.1 : Scalar)/(4*radius z.val)) := by
  have hl := (volume_smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt.log (volume_pos z).ne'
  have hr := (radius_smooth.differentiable (by simp) z.val).hasFDerivAt.const_mul (orientation negative)
  have he := hl.add hr
  change HasFDerivAt (characteristic negative) _ z.val at he
  rw [he.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,radius_derivative]
  ring

private theorem native_derivative (negative : Bool) (v : Ambient) (z : physicalChart) :
    fderiv ℝ (characteristic negative) z.val (direction v z.val)=nativeGradient negative v z.val := by
  rw [characteristic_derivative,volume_derivative]
  change (0*z.val.1 2*z.val.1 5+z.val.1 0*0*z.val.1 5+z.val.1 0*z.val.1 2*0)/volume z.val+
    orientation negative*(inner ℝ (z.val.2.1 : Scalar) ((inverseL z.val v).2.1 : Scalar)/(4*radius z.val))=_
  rw [inverse_radial]
  simp only [zero_mul,mul_zero,zero_add,zero_div,nativeGradient]

private theorem coframe_derivative (negative : Bool) (i : Fin 6) (z : physicalChart) :
    fderiv ℝ (characteristic negative) z.val (GaussCoframeCore.coframeDirection i)=coframeGradient i z.val := by
  rw [characteristic_derivative,volume_coordinate_derivative]
  change volumeGradient z.val i/volume z.val+orientation negative*(inner ℝ (z.val.2.1 : Scalar) 0/(4*radius z.val))=_
  simp only [inner_zero_right,zero_div,mul_zero,add_zero,coframeGradient]

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem first_order_contact (P : End) (v : SourceCoordinateSlice → SourceCoordinateSlice)
    (C : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hP : ∀ f z,P f z=(-Complex.I) • (fderiv ℝ f z (v z)+C z (f z)))
    (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hcd : ∀ z : physicalChart,fderiv ℝ c z.val (v z.val)=d z.val) :
    P*multiply c hc-multiply c hc*P=(-Complex.I) • multiply d hd := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hre : (multiply c hc f : SourceCoordinateSlice → FockFiber)=fun x => c x • f x := by
      funext x
      apply PiLp.ext
      intro word
      exact Complex.real_smul.symm
    have hh : fderiv ℝ (multiply c hc f) z (v z)=c z • fderiv ℝ f z (v z)+d z • f z := by
      rw [hre,fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (v z)+fderiv ℝ c z (v z) • f z=_
      rw [hcd ⟨z,hz⟩]
    change P (multiply c hc f) z-(c z : ℂ) • P f z=(-Complex.I) • ((d z : ℂ) • f z)
    rw [hP,hP,hh]
    change (-Complex.I) • (c z • fderiv ℝ f z (v z)+d z • f z+C z ((c z : ℂ) • f z))-
      (c z : ℂ) • ((-Complex.I) • (fderiv ℝ f z (v z)+C z (f z)))=_
    rw [map_smul]
    apply PiLp.ext
    intro word
    simp only [PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,Complex.real_smul]
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem transpose_contact (P A X D : End)
    (hP : P*X-X*P=(-Complex.I) • D)
    (hPair : ∀ f g,sourcePair f (A g)=sourcePair (P f) g)
    (hX : ∀ f g,sourcePair f (X g)=sourcePair (X f) g)
    (hD : ∀ f g,sourcePair f (D g)=sourcePair (D f) g) :
    A*X-X*A=(-Complex.I) • D := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  have hp := congrArg (fun T : End => sourcePair (T f) g) hP
  simp only [LinearMap.sub_apply,Module.End.mul_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_smul_left,map_neg,Complex.conj_I,neg_neg] at hp
  change sourcePair (P (X f)) g-sourcePair (X (P f)) g=Complex.I*sourcePair (D f) g at hp
  change sourcePair f (A (X g)-X (A g))=sourcePair f ((-Complex.I) • D g)
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right]
  change sourcePair f (A (X g))-sourcePair f (X (A g))=(-Complex.I)*sourcePair f (D g)
  rw [hPair,hX,hX,hPair,hD]
  linear_combination -hp

private theorem native_momentum_contact (negative : Bool) (v : Ambient) :
    covariantMomentum v*characteristicAction negative-characteristicAction negative*covariantMomentum v=
      (-Complex.I) • nativeContact negative v := by
  apply first_order_contact _ (direction v) (connection v)
    (fun f z => by change (-Complex.I) • (directional v f z+connection v z (f z))=_;rw [directional_apply];rfl)
    _ _ _ _ (native_derivative negative v)

private theorem native_adjoint_contact (negative : Bool) (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*characteristicAction negative-
      characteristicAction negative*GaussMomentumAdjoint.adjoint v=(-Complex.I) • nativeContact negative v :=
  transpose_contact _ _ _ _ (native_momentum_contact negative v) (GaussNativeForm.adjoint_pair v)
    (multiply_pair _ _) (multiply_pair _ _)

private theorem coframe_momentum_contact (negative : Bool) (i : Fin 6) :
    GaussCoframeCore.momentum i*characteristicAction negative-characteristicAction negative*GaussCoframeCore.momentum i=
      (-Complex.I) • coframeContact i := by
  apply first_order_contact _ (fun _ => GaussCoframeCore.coframeDirection i) (fun _ => 0)
    (fun f z => by change (-Complex.I) • GaussCoframeCore.derivative _ f z=_;rw [GaussCoframeCore.derivative_apply];simp)
    _ _ _ _ (coframe_derivative negative i)

private theorem coframe_adjoint_contact (negative : Bool) (i : Fin 6) :
    GaussCoframeCore.adjoint i*characteristicAction negative-characteristicAction negative*GaussCoframeCore.adjoint i=
      (-Complex.I) • coframeContact i :=
  transpose_contact _ _ _ _ (coframe_momentum_contact negative i) (GaussCoframeKinetic.adjoint_pair i)
    (multiply_pair _ _) (multiply_pair _ _)

private def current (X : End) : End →ₗ[ℂ] End where
  toFun A := A*X-X*A
  map_add' A B := by noncomm_ring
  map_smul' c A := by simp only [smul_mul_assoc,mul_smul_comm,smul_sub];rfl

private theorem current_mul (X A B : End) : current X (A*B)=A*current X B+current X A*B := by
  change (A*B)*X-X*(A*B)=A*(B*X-X*B)+(A*X-X*A)*B
  noncomm_ring

private theorem current_zero_of_commute {X A : End} (h : Commute A X) : current X A=0 := sub_eq_zero.mpr h.eq

private theorem current_real (negative : Bool) (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) :
    current (characteristicAction negative) (multiply c hc)=0 :=
  current_zero_of_commute (real_commute _ _ _ _)

private theorem current_quantum (negative : Bool) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    current (characteristicAction negative) (GaussQuantumMultiplier.action A hA)=0 := by
  apply current_zero_of_commute
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussQuantumMultiplier.quantized (A z) ((characteristic negative z : ℂ) • f z)=
    (characteristic negative z : ℂ) • GaussQuantumMultiplier.quantized (A z) (f z)
  exact map_smul _ _ _

private theorem current_native (negative : Bool) (v : Ambient) :
    current (characteristicAction negative) (covariantMomentum v)=(-Complex.I) • nativeContact negative v :=
  native_momentum_contact negative v
private theorem current_native_adjoint (negative : Bool) (v : Ambient) :
    current (characteristicAction negative) (GaussMomentumAdjoint.adjoint v)=(-Complex.I) • nativeContact negative v :=
  native_adjoint_contact negative v
private theorem current_coframe (negative : Bool) (i : Fin 6) :
    current (characteristicAction negative) (GaussCoframeCore.momentum i)=(-Complex.I) • coframeContact i :=
  coframe_momentum_contact negative i
private theorem current_coframe_adjoint (negative : Bool) (i : Fin 6) :
    current (characteristicAction negative) (GaussCoframeCore.adjoint i)=(-Complex.I) • coframeContact i :=
  coframe_adjoint_contact negative i

private theorem current_sandwich (X A B W D E : End)
    (hA : current X A=(-Complex.I) • D) (hB : current X B=(-Complex.I) • E)
    (hW : current X W=0) :
    current X (A*(W*B))=(-Complex.I) • (A*(W*E)+D*(W*B)) := by
  simp only [current_mul,hA,hB,hW,zero_mul,add_zero,mul_smul_comm,smul_mul_assoc,smul_add]

private def coframeFlux : End := ∑ i : Fin 6, ∑ j : Fin 6,
  (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*coframeContact j)+
  coframeContact i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j))

private def scalarFlux (negative : Bool) : End := ∑ a : ScalarIndex,
  (GaussMomentumAdjoint.adjoint (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*nativeContact negative (scalarDirection a))+
  nativeContact negative (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a)))

/-- The first current retains both formal momentum orders in every source column. -/
def characteristicCurrent (negative : Bool) : End :=
  (-Complex.I) • coframeFlux+(-Complex.I/2) • scalarFlux negative

private theorem coframe_kinetic_current (negative : Bool) :
    current (characteristicAction negative) GaussCoframeKinetic.kinetic=(-Complex.I) • coframeFlux := by
  unfold GaussCoframeKinetic.kinetic coframeFlux
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact current_sandwich _ _ _ _ _ _ (current_coframe_adjoint negative i)
    (current_coframe negative j) (current_real negative _ _)

private theorem scalar_kinetic_current (negative : Bool) :
    current (characteristicAction negative) scalarKinetic=(-Complex.I/2) • scalarFlux negative := by
  unfold scalarKinetic scalarFlux
  rw [map_smul,map_sum]
  have he : (∑ a : ScalarIndex,current (characteristicAction negative)
      (sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth))=
      (-Complex.I) • ∑ a : ScalarIndex,
        (GaussMomentumAdjoint.adjoint (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*nativeContact negative (scalarDirection a))+
        nativeContact negative (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection a))) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact current_sandwich _ _ _ _ _ _ (current_native_adjoint negative (scalarDirection a))
      (current_native negative (scalarDirection a)) (current_real negative _ _)
  rw [he,smul_smul]
  congr 1
  ring

private theorem gauge_contact_zero (negative : Bool) (i : Fin 3) (a : LieIndex) :
    nativeContact negative (gaugeDirection i a)=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((nativeGradient negative (gaugeDirection i a) z : ℝ) : ℂ) • f z=0
  simp [nativeGradient,gaugeDirection]

private theorem gauge_current (negative : Bool) :
    current (characteristicAction negative) gaugeKinetic=0 := by
  unfold gaugeKinetic sandwich
  simp only [map_smul,map_sum,←Module.End.mul_eq_comp,current_mul,current_native_adjoint,
    current_native,current_real,gauge_contact_zero,smul_zero,mul_zero,zero_mul,add_zero,Finset.sum_const_zero]

private theorem coframe_contact_off (i : Fin 6) (hi : i=1 ∨ i=3 ∨ i=4) : coframeContact i=0 := by
  rcases hi with rfl | rfl | rfl <;> apply LinearMap.ext <;> intro f <;> apply DFunLike.ext <;> intro z <;>
    change ((coframeGradient _ z : ℝ) : ℂ) • f z=0 <;> simp [coframeGradient,volumeGradient]

private theorem mixed_current (negative : Bool) (i : Fin 6) (a : Fin 7)
    (c : SourceCoordinateSlice → ℝ) (hc : ∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi : i=1 ∨ i=3 ∨ i=4) : current (characteristicAction negative) (GaussCoframeForm.mixed i a c hc)=0 := by
  unfold GaussCoframeForm.mixed GaussCoframeSpin.current
  simp only [map_smul,map_add,←Module.End.mul_eq_comp,current_mul,current_quantum,current_real,
    current_coframe,current_coframe_adjoint,coframe_contact_off i hi,smul_zero,mul_zero,zero_mul,add_zero]

private theorem lower_coframe_current (negative : Bool) :
    current (characteristicAction negative) GaussCoframeForm.coframeAction=
      current (characteristicAction negative) GaussCoframeKinetic.kinetic := by
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction
  rw [map_add,map_add,map_add,map_add,map_add,map_add,map_add,
    mixed_current negative 1 5 _ _ (Or.inl rfl),mixed_current negative 3 3 _ _ (Or.inr (Or.inl rfl)),
    mixed_current negative 3 4 _ _ (Or.inr (Or.inl rfl)),mixed_current negative 4 3 _ _ (Or.inr (Or.inr rfl))]
  simp only [map_sum,GaussCoframeForm.spinSquare,GaussCoframeForm.numberShift,GaussCoframeForm.number,
    GaussCoframeSpin.current,map_smul,map_add,←Module.End.mul_eq_comp,current_mul,current_quantum,
    current_real,mul_zero,zero_mul,add_zero,smul_zero,Finset.sum_const_zero]

/-- Full original Hamiltonian, including all source density transposes and local CAR terms. -/
theorem original_characteristic_current (negative : Bool) :
    diagonalAction*characteristicAction negative-characteristicAction negative*diagonalAction=
      characteristicCurrent negative := by
  change current (characteristicAction negative) diagonalAction=_
  unfold diagonalAction nativeAction
  rw [map_add,map_add,map_add,map_add,gauge_current,current_real,lower_coframe_current,
    coframe_kinetic_current,scalar_kinetic_current]
  unfold GaussMatterCore.matterAction
  simp only [map_sum,current_quantum,Finset.sum_const_zero,add_zero,characteristicCurrent]
  exact add_comm _ _

private theorem current_flux (X A B W D E : End)
    (hA : current X A=(-Complex.I) • D) (hB : current X B=(-Complex.I) • E)
    (hW : current X W=0) (hD : current X D=0) (hE : current X E=0) :
    current X (A*(W*E)+D*(W*B))=(-2*Complex.I) • (D*(W*E)) := by
  simp only [map_add,current_mul,hA,hB,hW,hD,hE,mul_zero,zero_mul,add_zero,zero_add,
    smul_mul_assoc,mul_smul_comm]
  module

private def coframeSquare : End := ∑ i : Fin 6, ∑ j : Fin 6,
  coframeContact i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*coframeContact j)
private def scalarSquare (negative : Bool) : End := ∑ a : ScalarIndex,
  nativeContact negative (scalarDirection a)*(multiply scalarWeight scalarWeight_smooth*nativeContact negative (scalarDirection a))

private theorem coframe_flux_current (negative : Bool) :
    current (characteristicAction negative) coframeFlux=(-2*Complex.I) • coframeSquare := by
  unfold coframeFlux coframeSquare
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact current_flux _ _ _ _ _ _ (current_coframe_adjoint negative i) (current_coframe negative j)
    (current_real negative _ _) (current_real negative _ _) (current_real negative _ _)

private theorem scalar_flux_current (negative : Bool) :
    current (characteristicAction negative) (scalarFlux negative)=(-2*Complex.I) • scalarSquare negative := by
  unfold scalarFlux scalarSquare
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact current_flux _ _ _ _ _ _ (current_native_adjoint negative (scalarDirection a))
    (current_native negative (scalarDirection a)) (current_real negative _ _)
    (current_real negative _ _) (current_real negative _ _)

private theorem double_current_squares (negative : Bool) :
    -(current (characteristicAction negative) (characteristicCurrent negative))=
      (2:ℂ) • coframeSquare+scalarSquare negative := by
  unfold characteristicCurrent
  rw [map_add,map_smul,map_smul,coframe_flux_current,scalar_flux_current,smul_smul,smul_smul]
  have h1 : (-Complex.I)*(-2*Complex.I)=(-2:ℂ) := by
    calc
      _=2*(Complex.I*Complex.I) := by ring
      _=_ := by rw [Complex.I_mul_I];ring
  have h2 : (-Complex.I/2)*(-2*Complex.I)=(-1:ℂ) := by
    calc
      _=Complex.I*Complex.I := by ring
      _=_ := Complex.I_mul_I
  rw [h1,h2]
  module

private theorem coframe_coefficient_square (z : physicalChart) :
    (∑ i : Fin 6, ∑ j : Fin 6,coframeGradient i z.val*
      GaussCoframeKinetic.coefficient i j z.val*coframeGradient j z.val)=3*sourceTime 0/(4*volume z.val) := by
  have hinner (i : Fin 6) : (∑ j : Fin 6,coframeGradient i z.val*
      GaussCoframeKinetic.coefficient i j z.val*coframeGradient j z.val)=
      (volumeGradient z.val i/volume z.val)*(sourceTime 0/4*z.val.1 i)/volume z.val := by
    calc
      _=(volumeGradient z.val i/volume z.val)*
          ((∑ j : Fin 6,GaussCoframeKinetic.coefficient i j z.val*volumeGradient z.val j)/volume z.val) := by
        simp only [coframeGradient,Finset.mul_sum,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=_ := by rw [coefficient_volume];ring
  simp_rw [hinner]
  simp [volumeGradient,Fin.sum_univ_succ]
  change _=3*sourceTime 0/(4*volume z.val)
  field_simp [(volume_pos z).ne']
  dsimp [volume]
  ring

private theorem native_gradient_square (negative : Bool) (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,(nativeGradient negative (scalarDirection a) z)^2)=
      3/2*(1-(reciprocal z)^2) := by
  have he (a : ScalarIndex) : nativeGradient negative (scalarDirection a) z=
      -orientation negative*directionWeight a z := by
    unfold nativeGradient scalarDirection directionWeight
    dsimp only
    ring
  simp_rw [he,mul_pow]
  rw [←Finset.mul_sum,neg_sq,orientation_sq,original_direction_square]
  ring

private theorem scalar_coefficient_square (negative : Bool) (z : SourceCoordinateSlice) :
    (∑ a : ScalarIndex,nativeGradient negative (scalarDirection a) z*scalarWeight z*
      nativeGradient negative (scalarDirection a) z)=
      -(3*sourceTime 0/2)*(volume z)⁻¹*(1-(reciprocal z)^2) := by
  have he (a : ScalarIndex) : nativeGradient negative (scalarDirection a) z*scalarWeight z*
      nativeGradient negative (scalarDirection a) z=scalarWeight z*(nativeGradient negative (scalarDirection a) z)^2 := by ring
  simp_rw [he]
  rw [←Finset.mul_sum,native_gradient_square]
  unfold scalarWeight
  ring

private theorem squares_return (negative : Bool) :
    (2:ℂ) • coframeSquare+scalarSquare negative=
      (3*(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*inverseAction*inverseAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z∈physicalChart
  · have hc : coframeSquare f z=
        ((∑ i : Fin 6, ∑ j : Fin 6,coframeGradient i z*GaussCoframeKinetic.coefficient i j z*coframeGradient j z : ℝ) : ℂ) • f z := by
      simp only [coframeSquare,LinearMap.sum_apply,sum_apply,Module.End.mul_apply,coframeContact,
        multiply_apply,smul_smul,←Complex.ofReal_mul,←Finset.sum_smul,←Complex.ofReal_sum,mul_assoc]
    have hs : scalarSquare negative f z=
        ((∑ a : ScalarIndex,nativeGradient negative (scalarDirection a) z*scalarWeight z*
          nativeGradient negative (scalarDirection a) z : ℝ) : ℂ) • f z := by
      simp only [scalarSquare,LinearMap.sum_apply,sum_apply,Module.End.mul_apply,nativeContact,
        multiply_apply,smul_smul,←Complex.ofReal_mul,←Finset.sum_smul,←Complex.ofReal_sum,mul_assoc]
    change (2:ℂ) • (coframeSquare f z)+scalarSquare negative f z=_
    rw [hc,hs,coframe_coefficient_square ⟨z,hz⟩,scalar_coefficient_square]
    change (2:ℂ) • ((↑(3*sourceTime 0/(4*volume z)) : ℂ) • f z)+
      ((((-(3*sourceTime 0/2)*(volume z)⁻¹*(1-(reciprocal z)^2)) : ℝ) : ℂ) • f z)=
        (3*(sourceTime 0 : ℂ)/2) • (((volume z)⁻¹ : ℝ) : ℂ) • ((reciprocal z : ℂ) • ((reciprocal z : ℂ) • f z))
    simp only [smul_smul,←add_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
      Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    congr 1
    ring
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

/-- The scalar and complete coframe principal currents cancel to this strictly positive local coefficient. -/
theorem original_characteristic_double_current (negative : Bool) :
    characteristicAction negative*(diagonalAction*characteristicAction negative-characteristicAction negative*diagonalAction)-
      (diagonalAction*characteristicAction negative-characteristicAction negative*diagonalAction)*characteristicAction negative=
      (3*(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*inverseAction*inverseAction) := by
  rw [original_characteristic_current]
  have he := (double_current_squares negative).trans (squares_return negative)
  simpa only [current,LinearMap.coe_mk,AddHom.coe_mk,neg_sub] using he

/-- The actual finite compression retains the complete original defect with its source sign. -/
theorem original_compression_double_current (negative : Bool) (F : Index) :
    characteristicAction negative*(compressionCore F*characteristicAction negative-characteristicAction negative*compressionCore F)-
      (compressionCore F*characteristicAction negative-characteristicAction negative*compressionCore F)*characteristicAction negative=
      (3*(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*inverseAction*inverseAction)-
      (characteristicAction negative*(defectAction F*characteristicAction negative-characteristicAction negative*defectAction F)-
        (defectAction F*characteristicAction negative-characteristicAction negative*defectAction F)*characteristicAction negative) := by
  rw [←original_characteristic_double_current negative]
  unfold defectAction
  noncomm_ring

end LowEnergy.SourceCharacteristicRadiusCurrent
