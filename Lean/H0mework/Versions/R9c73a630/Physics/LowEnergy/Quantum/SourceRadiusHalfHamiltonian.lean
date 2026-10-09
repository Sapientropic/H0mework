import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceRadiusHalfKinetic
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussRadialHamiltonian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusHalfHamiltonian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open GaussYukawaCoefficient GaussRadialDomain GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceRadiusBandGradient SourceRadiusHalfWindow SourceCoframeVolume
open scoped ContDiff InnerProductSpace Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
abbrev CoreEnd := QuantumTest →ₗ[ℂ] QuantumTest

private theorem half_smooth (m ell : ℕ) : ContDiff ℝ ∞ (halfCoefficient m ell) := by
  have hn (z : SourceCoordinateSlice) : 0 ≤ coefficient m ell z := by
    unfold coefficient SourceRadiusBandPolynomial.band
    exact Finset.sum_nonneg (fun j _ => pow_nonneg
      (sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))) _)
  exact ((contDiff_const.add (coefficient_smooth m ell)).sqrt (fun z => by
    have h := hn z;linarith)).sub contDiff_const

private theorem half_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (halfAction m ell g)=sourcePair (halfAction m ell f) g := multiply_pair _ _ _ _

private theorem half_real (m ell : ℕ) (f : QuantumTest) :
    (halfAction m ell f : SourceCoordinateSlice → FockFiber)=
      fun z => halfCoefficient m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem multiplier_commutes (m ell : ℕ)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) :
    Commute (localMultiplier A smooth) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (A z) (halfCoefficient m ell z : ℂ) (f z)

private theorem real_commutes (m ell : ℕ) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (multiply c smooth) (halfAction m ell) := multiplier_commutes _ _ _ _

private theorem paired_commutes (m ell : ℕ) (A B : CoreEnd)
    (pair : GaussCoframeForm.Paired B A) (hc : Commute A (halfAction m ell)) :
    Commute B (halfAction m ell) := by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (B (halfAction m ell g))=
    sourcePair f (halfAction m ell (B g))
  have he : A (halfAction m ell f)=halfAction m ell (A f) := LinearMap.congr_fun hc.eq f
  calc
    _=sourcePair (A f) (halfAction m ell g) := pair _ _
    _=sourcePair (halfAction m ell (A f)) g := half_pair _ _ _ _
    _=sourcePair (A (halfAction m ell f)) g := congrArg (fun q => sourcePair q g) he.symm
    _=sourcePair (halfAction m ell f) (B g) := (pair _ _).symm
    _=_ := (half_pair _ _ _ _).symm

private theorem half_coframe_derivative (m ell : ℕ) (z : SourceCoordinateSlice) (i : Fin 6) :
    fderiv ℝ (halfCoefficient m ell) z (GaussCoframeCore.coframeDirection i)=0 := by
  have hd := ((half_smooth m ell).differentiable (by simp)).differentiableAt (x := z) |>.hasFDerivAt
  have hc : HasDerivAt (fun r : ℝ => z+r • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (GaussCoframeCore.coframeDirection i) |>.const_add z
  have hh := hd.comp_hasDerivAt_of_eq 0 hc (by simp)
  have he : (fun r : ℝ => halfCoefficient m ell (z+r • GaussCoframeCore.coframeDirection i))=
      (fun _ => halfCoefficient m ell z) := by
    funext r
    simp [halfCoefficient,coefficient,SourceRadiusBandPolynomial.band,reciprocal,radius,GaussCoframeCore.coframeDirection]
  change HasDerivAt (fun r : ℝ => halfCoefficient m ell (z+r • GaussCoframeCore.coframeDirection i))
    (fderiv ℝ (halfCoefficient m ell) z (GaussCoframeCore.coframeDirection i)) 0 at hh
  rw [he] at hh
  exact hh.unique (hasDerivAt_const 0 _)

private theorem coframe_derivative (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i)) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoframeCore.derivative _ (halfAction m ell f) z=
    halfAction m ell (GaussCoframeCore.derivative _ f) z
  rw [GaussCoframeCore.derivative_apply,half_real,
    fderiv_fun_smul ((half_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change halfCoefficient m ell z • fderiv ℝ f z (GaussCoframeCore.coframeDirection i)+
    fderiv ℝ (halfCoefficient m ell) z (GaussCoframeCore.coframeDirection i) • f z=_
  rw [half_coframe_derivative,zero_smul,add_zero]
  change _=(halfCoefficient m ell z : ℂ) • GaussCoframeCore.derivative _ f z
  rw [GaussCoframeCore.derivative_apply]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem coframe_momentum (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.momentum i) (halfAction m ell) :=
  (coframe_derivative m ell i).smul_left (-Complex.I)

private theorem coframe_adjoint (m ell : ℕ) (i : Fin 6) :
    Commute (GaussCoframeCore.adjoint i) (halfAction m ell) :=
  paired_commutes m ell _ _ (GaussCoframeKinetic.adjoint_pair i) (coframe_momentum m ell i)

private theorem quantum_commutes (m ell : ℕ) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val) :
    Commute (GaussQuantumMultiplier.action A smooth) (halfAction m ell) := multiplier_commutes _ _ _ _

private theorem end_sum_commute {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (A : ι → R) (B : R)
    (h : ∀ i, Commute (A i) B) : Commute (∑ i, A i) B := by
  change (∑ i, A i)*B=B*(∑ i, A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (h i).eq)

private theorem end_smul_commute {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (c : ℂ) (A B : R) (h : Commute A B) : Commute (c • A) B := by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]

private theorem end_mul_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A*B) C := hA.mul_left hB

private theorem end_add_commute {R : Type*} [Ring R] (A B C : R)
    (hA : Commute A C) (hB : Commute B C) : Commute (A+B) C := hA.add_left hB

private theorem coframe_kinetic (m ell : ℕ) :
    Commute GaussCoframeKinetic.kinetic (halfAction m ell) := by
  change Commute (∑ i : Fin 6, ∑ j : Fin 6, GaussCoframeKinetic.term i j) (halfAction m ell)
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro j
  change Commute (GaussCoframeCore.adjoint i*(multiply (GaussCoframeKinetic.coefficient i j)
    (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)) (halfAction m ell)
  apply end_mul_commute (R := CoreEnd)
  · exact coframe_adjoint m ell i
  · apply end_mul_commute (R := CoreEnd)
    · exact real_commutes m ell _ _
    · exact coframe_momentum m ell j

private theorem coframe_current (m ell : ℕ) (a : Fin 7) :
    Commute (GaussCoframeSpin.current a) (halfAction m ell) := quantum_commutes _ _ _ _

private theorem coframe_mixed (m ell : ℕ) (i : Fin 6) (a : Fin 7) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commute (GaussCoframeForm.mixed i a c smooth) (halfAction m ell) := by
  change Commute ((1/2 : ℂ) • (GaussCoframeSpin.current a*(multiply c smooth*GaussCoframeCore.momentum i)+
    GaussCoframeCore.adjoint i*(multiply c smooth*GaussCoframeSpin.current a))) (halfAction m ell)
  apply end_smul_commute (R := CoreEnd)
  apply end_add_commute (R := CoreEnd)
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_current m ell a
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes m ell c smooth
      · exact coframe_momentum m ell i
  · apply end_mul_commute (R := CoreEnd)
    · exact coframe_adjoint m ell i
    · apply end_mul_commute (R := CoreEnd)
      · exact real_commutes m ell c smooth
      · exact coframe_current m ell a

private theorem coframe_commutes (m ell : ℕ) :
    Commute GaussCoframeForm.coframeAction (halfAction m ell) := by
  unfold GaussCoframeForm.coframeAction GaussCoframeForm.currentAction
    GaussCoframeForm.spinSquare GaussCoframeForm.numberShift
  apply end_add_commute (R := CoreEnd)
  · apply end_add_commute (R := CoreEnd)
    · apply end_add_commute (R := CoreEnd)
      · apply end_add_commute (R := CoreEnd)
        · exact coframe_kinetic m ell
        · apply end_add_commute (R := CoreEnd)
          · apply end_add_commute (R := CoreEnd)
            · apply end_add_commute (R := CoreEnd)
              · exact coframe_mixed _ _ _ _ _ _
              · exact coframe_mixed _ _ _ _ _ _
            · exact coframe_mixed _ _ _ _ _ _
          · exact coframe_mixed _ _ _ _ _ _
      · apply end_sum_commute (R := CoreEnd)
        intro a
        apply end_smul_commute (R := CoreEnd)
        change Commute (GaussCoframeSpin.current a*(multiply GaussCoframeForm.inverseVolume
          GaussCoframeForm.inverseVolume_smooth*GaussCoframeSpin.current a)) (halfAction m ell)
        apply end_mul_commute (R := CoreEnd)
        · exact coframe_current m ell a
        · apply end_mul_commute (R := CoreEnd)
          · exact real_commutes _ _ _ _
          · exact coframe_current m ell a
    · apply end_smul_commute (R := CoreEnd)
      change Commute (GaussCoframeForm.number*multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
        multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number) (halfAction m ell)
      apply end_add_commute (R := CoreEnd)
      · apply end_mul_commute (R := CoreEnd)
        · exact quantum_commutes _ _ _ _
        · exact real_commutes _ _ _ _
      · apply end_mul_commute (R := CoreEnd)
        · exact real_commutes _ _ _ _
        · exact quantum_commutes _ _ _ _
  · exact real_commutes _ _ _ _

private theorem matter_commutes (m ell : ℕ) :
    Commute GaussMatterCore.matterAction (halfAction m ell) := by
  unfold GaussMatterCore.matterAction
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro a
  exact quantum_commutes _ _ _ _

private theorem contact_pair (m ell : ℕ) (v : Ambient) (f g : QuantumTest) :
    sourcePair f (halfContact v m ell g)= -sourcePair (halfContact v m ell f) g := by
  rw [sourcePair_integral,sourcePair_integral,←MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  dsimp only
  rw [densityPair_sum,densityPair_sum,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro word _
  change _ * star (f z word) * (((-Complex.I)*(derivative v m ell z : ℂ))*
    ((chainFactor m ell z : ℂ)*g z word))=
    -(_ * star (((-Complex.I)*(derivative v m ell z : ℂ))*((chainFactor m ell z : ℂ)*f z word)) * g z word)
  simp only [star_mul,map_neg,Complex.star_def,Complex.conj_I,Complex.conj_ofReal,neg_neg]
  ring

theorem original_half_adjoint_contact (m ell : ℕ) (v : Ambient) (g : QuantumTest) :
    GaussMomentumAdjoint.adjoint v (halfAction m ell g)=
      halfAction m ell (GaussMomentumAdjoint.adjoint v g)+halfContact v m ell g := by
  apply SourceCoframeVolume.pair_ext
  intro f
  have h1 := GaussNativeForm.adjoint_pair v f (halfAction m ell g)
  have h2 := half_pair m ell (covariantMomentum v f) g
  have h3 := GaussNativeForm.adjoint_pair v (halfAction m ell f) g
  have h4 := half_pair m ell f (GaussMomentumAdjoint.adjoint v g)
  have h5 := contact_pair m ell v f g
  rw [original_half_native_contact] at h3
  change sourcePair (halfAction m ell f) (GaussMomentumAdjoint.adjoint v g)=
    inner ℂ (embed (halfAction m ell (covariantMomentum v f)+halfContact v m ell f)) (embed g) at h3
  rw [map_add,inner_add_left] at h3
  change sourcePair f (GaussMomentumAdjoint.adjoint v (halfAction m ell g))=
    inner ℂ (embed f) (embed (halfAction m ell (GaussMomentumAdjoint.adjoint v g)+halfContact v m ell g))
  rw [map_add,inner_add_right]
  change _=sourcePair f (halfAction m ell (GaussMomentumAdjoint.adjoint v g))+sourcePair f (halfContact v m ell g)
  rw [h1,h2,h4,h3,h5]
  unfold sourcePair
  ring

private theorem gauge_momentum (m ell : ℕ) (v : Ambient) (hv : v.1=0) : Commute (covariantMomentum v) (halfAction m ell) := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply,Module.End.mul_apply,original_half_native_contact]
  have hC : halfContact v m ell f=0 := by
    apply DFunLike.ext
    intro z
    change ((-Complex.I)*(derivative v m ell z : ℂ)) • ((chainFactor m ell z : ℂ) • f z)=0
    simp [derivative,GaussRadialMomentum.radialDerivative,hv]
  rw [hC,add_zero]

private theorem gauge_adjoint (m ell : ℕ) (v : Ambient) (hv : v.1=0) : Commute (GaussMomentumAdjoint.adjoint v) (halfAction m ell) :=
  paired_commutes m ell _ _ (GaussNativeForm.adjoint_pair v) (gauge_momentum m ell v hv)

private theorem gauge_commutes (m ell : ℕ) : Commute gaugeKinetic (halfAction m ell) := by
  unfold gaugeKinetic
  apply end_smul_commute (R := CoreEnd)
  apply end_sum_commute (R := CoreEnd)
  intro a
  apply end_sum_commute (R := CoreEnd)
  intro i
  apply end_sum_commute (R := CoreEnd)
  intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) (halfAction m ell)
  apply end_mul_commute (R := CoreEnd)
  · exact gauge_adjoint m ell (gaugeDirection i a) rfl
  · apply end_mul_commute (R := CoreEnd)
    · exact real_commutes m ell (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
    · exact gauge_momentum m ell (gaugeDirection j a) rfl

private theorem sandwich_law {R : Type*} [Ring R] (P W Q L C : R)
    (hP : P*L=L*P+C) (hQ : Q*L=L*Q+C) (hW : W*L=L*W) :
    (P*(W*Q))*L=L*(P*(W*Q))+(P*(W*C)+C*(W*Q)) := by
  calc
    _=P*(W*(Q*L)) := by noncomm_ring
    _=P*(W*(L*Q+C)) := by rw [hQ]
    _=P*((W*L)*Q+W*C) := by noncomm_ring
    _=(P*L)*(W*Q)+P*(W*C) := by rw [hW];noncomm_ring
    _=_ := by rw [hP];noncomm_ring

def radialTerm (m ell : ℕ) (v : Ambient) : CoreEnd :=
  GaussMomentumAdjoint.adjoint v*(multiply scalarWeight scalarWeight_smooth*halfContact v m ell)+
    halfContact v m ell*(multiply scalarWeight scalarWeight_smooth*covariantMomentum v)
def radialAction (m ell : ℕ) : CoreEnd := (1/2 : ℂ) • ∑ a : ScalarIndex,radialTerm m ell (scalarDirection a)

private theorem scalar_term (m ell : ℕ) (v : Ambient) :
    sandwich v v scalarWeight scalarWeight_smooth*halfAction m ell=
      halfAction m ell*sandwich v v scalarWeight scalarWeight_smooth+radialTerm m ell v :=
  sandwich_law _ _ _ _ _ (LinearMap.ext (original_half_adjoint_contact m ell v))
    (LinearMap.ext (original_half_native_contact v m ell)) (real_commutes m ell _ _).eq

theorem original_scalar_current (m ell : ℕ) :
    scalarKinetic*halfAction m ell=halfAction m ell*scalarKinetic+radialAction m ell := by
  simp only [scalarKinetic,radialAction,smul_mul_assoc,Finset.sum_mul,scalar_term,
    Finset.sum_add_distrib,←Finset.mul_sum,mul_smul_comm,smul_add]

/-- The entire original H0 current is generated by the native70 covariant contacts, with the literal negative weight. -/
theorem original_diagonal_current (m ell : ℕ) :
    diagonalAction*halfAction m ell=halfAction m ell*diagonalAction+radialAction m ell := by
  change (scalarKinetic+gaugeKinetic+multiply potential potential_smooth+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)*halfAction m ell=_
  simp only [add_mul,original_scalar_current,(gauge_commutes m ell).eq,
    (real_commutes m ell potential potential_smooth).eq,(coframe_commutes m ell).eq,(matter_commutes m ell).eq]
  change _=halfAction m ell*(scalarKinetic+gaugeKinetic+multiply potential potential_smooth+
    GaussCoframeForm.coframeAction+GaussMatterCore.matterAction)+radialAction m ell
  noncomm_ring

/-- Full Y and the independently generated Y-adjoint retain the same original radial current. -/
theorem original_full_current (m ell : ℕ) :
    GaussFullHamiltonian.fullAction*halfAction m ell=
      halfAction m ell*GaussFullHamiltonian.fullAction+radialAction m ell := by
  have hY : Commute GaussYukawaOperator.originalAction (halfAction m ell) := multiplier_commutes m ell _ _
  change (diagonalAction+GaussYukawaOperator.originalAction)*halfAction m ell=_
  rw [add_mul,original_diagonal_current,hY.eq]
  change _=halfAction m ell*(diagonalAction+GaussYukawaOperator.originalAction)+radialAction m ell
  noncomm_ring

theorem original_sharp_current (m ell : ℕ) :
    GaussFullHamiltonian.sharpAction*halfAction m ell=
      halfAction m ell*GaussFullHamiltonian.sharpAction+radialAction m ell := by
  have hY : Commute GaussFullHamiltonian.adjointAction (halfAction m ell) := multiplier_commutes m ell _ _
  change (diagonalAction+GaussFullHamiltonian.adjointAction)*halfAction m ell=_
  rw [add_mul,original_diagonal_current,hY.eq]
  change _=halfAction m ell*(diagonalAction+GaussFullHamiltonian.adjointAction)+radialAction m ell
  noncomm_ring

/-- Both ordered covariant legs remain in the source radial form. -/
theorem original_radial_form (m ell : ℕ) (v : Ambient) (f g : QuantumTest) :
    sourcePair f (radialTerm m ell v g)=
      sourcePair (covariantMomentum v f) (multiply scalarWeight scalarWeight_smooth (halfContact v m ell g))-
      sourcePair (halfContact v m ell f) (multiply scalarWeight scalarWeight_smooth (covariantMomentum v g)) := by
  change sourcePair f (GaussMomentumAdjoint.adjoint v
    (multiply scalarWeight scalarWeight_smooth (halfContact v m ell g))+
      halfContact v m ell (multiply scalarWeight scalarWeight_smooth (covariantMomentum v g)))=_
  simp only [sourcePair,map_add,inner_add_right]
  change sourcePair f (GaussMomentumAdjoint.adjoint v _)+sourcePair f (halfContact v m ell _)=_
  rw [GaussNativeForm.adjoint_pair,contact_pair,sub_eq_add_neg]
  rfl

end LowEnergy.SourceRadiusHalfHamiltonian
