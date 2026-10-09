import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaCutoffJets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumUncutYukawa
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumYukawaTransport PreparationVacuumGradedTransport PreparationVacuumFullFieldRiesz
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets
open CanonicalGradedLocalCurrent
open NativeHistoryGrade (Label projection)
open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph
open Filter Set
open scoped Topology InnerProductSpace BigOperators
local instance : Fintype Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H →L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] transportedCompression transportedCurrent transportedContact fieldCutoff
  retainer uncutOperator uncutSlope jetOperator CanonicalPhysicalYResolvent.finiteFull

/-- `some n` is the literal n-th source cutoff; `none` is its original uncut source coefficient. -/
def sourceYJet (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (k : Fin 3) (r : ℝ) : H →L[ℂ] H :=
  match o with
  | some n=>jetOperator f n k.val (finiteRetainer p F) r
  | none=>uncutJetOperator f (finiteRetainer p F) k r

def sourceGenerator (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  transportedCompression f p F r+sourceYJet f p F o 0 r-z • 1

def sourceResolvent (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  Ring.inverse (sourceGenerator f p F o z r)

def sourceCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (r : ℝ) : H →L[ℂ] H :=
  transportedCurrent f p F r+sourceYJet f p F o 1 r

def sourceContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) : H →L[ℂ] H :=
  transportedContact f p F+sourceYJet f p F o 2 0

theorem sourceY_first (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (r : ℝ) :
    HasDerivAt (sourceYJet f p F o 0) (sourceYJet f p F o 1 r) r :=by
  cases o with
  | none=>exact uncutOperator_derivative f (finiteRetainer p F) r
  | some n=>exact jetOperator_derivative f n 0 (finiteRetainer p F) r

theorem sourceY_second (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (r : ℝ) :
    HasDerivAt (sourceYJet f p F o 1) (sourceYJet f p F o 2 r) r :=by
  cases o with
  | none=>exact hasDerivAt_const r (uncutSlope f (finiteRetainer p F))
  | some n=>exact jetOperator_derivative f n 1 (finiteRetainer p F) r

theorem retainer_grade (p : PhysicalMomentum) (F : Index) : Commute GaussYukawaGrade.grade (retainer p F) :=by
  apply Commute.symm
  unfold GaussYukawaGrade.grade
  apply Commute.sum_right;intro g _
  exact (retainer_projection p F g).smul_right _

lemma product_raises {A : Type*} [Ring A] (G R Y : A) (hR : Commute G R) (hY : G*Y=Y*G+Y) :
    G*(R*Y)=(R*Y)*G+R*Y :=by
  rw [←mul_assoc,hR.eq,mul_assoc,hY,mul_add,mul_assoc]

theorem sourceY_raises (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (r : ℝ) :
    GaussYukawaGrade.grade*sourceYJet f p F o 0 r=
      sourceYJet f p F o 0 r*GaussYukawaGrade.grade+sourceYJet f p F o 0 r :=by
  cases o with
  | none=>exact uncutOperator_raises f (finiteRetainer p F) r
  | some n=>
    change GaussYukawaGrade.grade*jetOperator f n 0 (finiteRetainer p F) r=
      jetOperator f n 0 (finiteRetainer p F) r*GaussYukawaGrade.grade+jetOperator f n 0 (finiteRetainer p F) r
    rw [jetOperator_cutoff f n p F r]
    exact product_raises _ _ _ (retainer_grade p F) (fieldCutoff_raises f n r)

def sourceStep (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  -(Ring.inverse (movingDiagonal f p F z r)*sourceYJet f p F o 0 r)

def sourceSeries (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  (∑i∈Finset.range 57,(sourceStep f p F o z r)^i)*Ring.inverse (movingDiagonal f p F z r)

theorem sourceStep_nilpotent (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) : (sourceStep f p F o z r)^57=0 :=by
  apply raised_nilpotent
  have neutral : Commute GaussYukawaGrade.grade (movingDiagonal f p F z r) :=by
    unfold movingDiagonal transportedCompression
    exact (sourceAssembly_grade p F _).sub_right ((Commute.one_right _).smul_right z)
  exact negative_raises _ _ _ (inverse_commuting _ _ unit neutral).eq (sourceY_raises f p F o r)

theorem sourceSeries_inverse (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) :
    sourceSeries f p F o z r*sourceGenerator f p F o z r=1 ∧ sourceGenerator f p F o z r*sourceSeries f p F o z r=1 :=by
  have factor : sourceGenerator f p F o z r=movingDiagonal f p F z r*(1-sourceStep f p F o z r) :=
    (add_sub_reorder (transportedCompression f p F r) (sourceYJet f p F o 0 r) (z • 1)).trans
      (factor_add _ _ _ (Ring.mul_inverse_cancel _ unit))
  rw [factor]
  exact geometric_inverse _ _ _ 57 (Ring.inverse_mul_cancel _ unit) (Ring.mul_inverse_cancel _ unit)
    (sourceStep_nilpotent f p F o z r unit)

def sourceUnit (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) : (H →L[ℂ] H)ˣ :=
  ⟨sourceGenerator f p F o z r,sourceSeries f p F o z r,
    (sourceSeries_inverse f p F o z r unit).2,(sourceSeries_inverse f p F o z r unit).1⟩

theorem sourceResolvent_series (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) : sourceResolvent f p F o z r=sourceSeries f p F o z r :=
  Ring.inverse_unit (sourceUnit f p F o z r unit)

theorem sourceY_retained (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (r : ℝ)
    (x : H) (hx : x∈retainedSpace p F) : sourceYJet f p F o 0 r x∈retainedSpace p F :=by
  cases o with
  | none=>exact uncutOperator_retained f p F r x hx
  | some n=>
    have kept:=fieldCutoff_retained f n p F r x hx
    have eq:=(retainedSpace_iff p F _).mp kept
    change jetOperator f n 0 (finiteRetainer p F) r x∈retainedSpace p F
    rw [jetOperator_cutoff f n p F r,mul_apply_eq_comp,eq]
    exact kept

theorem sourceResolvent_retained (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (hz : z≠0)
    (r : ℝ) (unit : IsUnit (movingDiagonal f p F z r)) (x : H) (hx : x∈retainedSpace p F) :
    sourceResolvent f p F o z r x∈retainedSpace p F :=by
  have step (y : H) (hy : y∈retainedSpace p F) : sourceStep f p F o z r y∈retainedSpace p F :=
    (retainedSpace p F).neg_mem (movingDiagonal_retained f p F z hz r unit _ (sourceY_retained f p F o r y hy))
  have powers (m : ℕ) (y : H) (hy : y∈retainedSpace p F) : ((sourceStep f p F o z r)^m) y∈retainedSpace p F :=by
    induction m with
    | zero=>simpa only [pow_zero,one_apply_eq_self] using hy
    | succ m ih=>rw [pow_succ',mul_apply_eq_comp];exact step _ ih
  rw [sourceResolvent_series f p F o z r unit]
  simp only [sourceSeries,mul_apply_eq_comp,sum_apply]
  exact (retainedSpace p F).sum_mem fun i _=>powers i _ (movingDiagonal_retained f p F z hz r unit x hx)

theorem uncut_resolvent_domain (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z≠0)
    (r : ℝ) (unit : IsUnit (movingDiagonal f p F z r)) (x : H) (hx : x∈retainedSpace p F) :
    ∃hy : sourceResolvent f p F none z r x∈(movedClosedY f r).domain,
      transportedCompression f p F r (sourceResolvent f p F none z r x)+
        (movedClosedY f r) ⟨sourceResolvent f p F none z r x,hy⟩-
        z • sourceResolvent f p F none z r x=x :=by
  obtain ⟨hy,readback⟩:=uncutOperator_domain f p F r _ (sourceResolvent_retained f p F none z hz r unit x hx)
  refine ⟨hy,?_⟩
  rw [readback]
  have h:=congrArg (fun A : H →L[ℂ] H=>A x) (sourceSeries_inverse f p F none z r unit).2
  rw [←sourceResolvent_series f p F none z r unit] at h
  exact h

theorem sourceResolvent_cut (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z≠0)
    (r : ℝ) (unit : IsUnit (movingDiagonal f p F z r)) (x : H) (hx : x∈retainedSpace p F) :
    sourceResolvent f p F (some n) z r x=trueResolvent f p F n z r x :=by
  have kept:=trueResolvent_retained f p F n z hz r unit x hx
  have right:=congrArg (fun A : H →L[ℂ] H=>A x) (movingSeries_inverse f p F n z r unit).2
  rw [←trueResolvent_series f p F n z r unit] at right
  have same : sourceGenerator f p F (some n) z r (trueResolvent f p F n z r x)=x :=by
    change transportedCompression f p F r _+jetOperator f n 0 (finiteRetainer p F) r _-z • _=x
    rw [jetOperator_cutoff f n p F r,mul_apply_eq_comp,(retainedSpace_iff p F _).mp (fieldCutoff_retained f n p F r _ kept)]
    exact right
  have left:=congrArg (fun A : H →L[ℂ] H=>A (trueResolvent f p F n z r x))
    (sourceSeries_inverse f p F (some n) z r unit).1
  rw [←sourceResolvent_series f p F (some n) z r unit] at left
  change sourceResolvent f p F (some n) z r (sourceGenerator f p F (some n) z r (trueResolvent f p F n z r x))=_ at left
  rwa [same] at left

theorem sourceGenerator_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (sourceGenerator f p F o z) (sourceCurrent f p F o r) r :=
  (transportedCompression_derivative_near f p F).mono fun r hr=>
    (hr.add (sourceY_first f p F o r)).sub_const (z • 1)

theorem sourceCurrent_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) :
    HasDerivAt (sourceCurrent f p F o) (sourceContact f p F o) 0 :=by
  convert! (transportedCurrent_second f p F).add (sourceY_second f p F o 0) using 1

def sourceInsertion (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  sourceResolvent f p F o z r*sourceCurrent f p F o r*sourceResolvent f p F o z r

theorem sourceResolvent_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (sourceResolvent f p F o z) (-sourceInsertion f p F o z r) r :=by
  filter_upwards [movingDiagonal_units f p F z hz,sourceGenerator_derivative f p F o z] with r hu hd
  exact inverse_curve_derivative _ r _ hd (sourceUnit f p F o z r hu).isUnit

def sourceInverseContact (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) : H →L[ℂ] H :=
  -(sourceResolvent f p F o z 0*sourceContact f p F o*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*sourceCurrent f p F o 0*sourceResolvent f p F o z 0*sourceCurrent f p F o 0*sourceResolvent f p F o z 0-
    sourceResolvent f p F o z 0*sourceCurrent f p F o 0*sourceResolvent f p F o z 0*sourceCurrent f p F o 0*sourceResolvent f p F o z 0)

theorem sourceInsertion_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) :
    HasDerivAt (fun r=> -sourceInsertion f p F o z r) (sourceInverseContact f p F o z) 0 :=by
  have R:=(sourceResolvent_derivative f p F o z hz).self_of_nhds
  have product:=(R.mul (sourceCurrent_derivative f p F o)).mul R
  simp only [Pi.mul_apply,sourceInsertion] at product
  have algebra:=inverse_insertion_algebra (sourceResolvent f p F o z 0) (sourceCurrent f p F o 0) (sourceContact f p F o)
  convert! (product.congr_deriv algebra.symm).neg using 1

def observedResponse (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (sourceResolvent f p F o z r (completedLeg right b t (sourceProfile epsilon precision)))

def observedJets (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (observedResponse epsilon precision f p F o z left right a s b t) where
  first r:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    ((-sourceInsertion f p F o z r) (completedLeg right b t (sourceProfile epsilon precision)))
  second:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (sourceInverseContact f p F o z (completedLeg right b t (sourceProfile epsilon precision)))
  derivative_near:=(sourceResolvent_derivative f p F o z hz).mono fun _r hr=>
    paired_derivative hr (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  second_derivative:=paired_derivative (sourceInsertion_derivative f p F o z hz)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))

theorem observed_cut_readback (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    observedResponse epsilon precision f p F (some n) z left right a s b t=ᶠ[𝓝 0]
      truePreparedResponse epsilon precision f p F n z left right a s b t :=by
  filter_upwards [movingDiagonal_units f p F z hz] with r hr
  exact congrArg (fun y : H=>inner ℂ (completedLeg left a s (sourceProfile epsilon precision)) y)
    (sourceResolvent_cut f p F n z (fun h=>hz (by rw [h];rfl)) r hr _ (profileLeg_retained epsilon precision p F right b t))

theorem sourceY_limit (f : Field289) (p : PhysicalMomentum) (F : Index) (k : Fin 3) (r : ℝ) :
    Tendsto (fun n=>sourceYJet f p F (some n) k r) atTop (𝓝 (sourceYJet f p F none k r)) :=
  cutoffJets_limit f (finiteRetainer p F) r k

theorem sourceResolvent_limit (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) :
    Tendsto (fun n=>sourceResolvent f p F (some n) z r) atTop (𝓝 (sourceResolvent f p F none z r)) :=by
  have coefficients:=((sourceY_limit f p F 0 r).const_add (transportedCompression f p F r)).sub_const (z • 1)
  have inverse:=(hasFDerivAt_ringInverse (𝕜:=ℝ) (sourceUnit f p F none z r unit)).continuousAt.tendsto
  exact inverse.comp coefficients

theorem sourceCurrent_limit (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    Tendsto (fun n=>sourceCurrent f p F (some n) r) atTop (𝓝 (sourceCurrent f p F none r)) :=
  (sourceY_limit f p F 1 r).const_add (transportedCurrent f p F r)

theorem sourceContact_limit (f : Field289) (p : PhysicalMomentum) (F : Index) :
    Tendsto (fun n=>sourceContact f p F (some n)) atTop (𝓝 (sourceContact f p F none)) :=
  (sourceY_limit f p F 2 0).const_add (transportedContact f p F)

theorem sourceInsertion_limit (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    Tendsto (fun n=>sourceInsertion f p F (some n) z 0) atTop (𝓝 (sourceInsertion f p F none z 0)) :=by
  have R:=sourceResolvent_limit f p F z 0 (movingDiagonal_units f p F z hz).self_of_nhds
  exact (R.mul (sourceCurrent_limit f p F 0)).mul R

theorem sourceContactInsertion_limit (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    Tendsto (fun n=>sourceInverseContact f p F (some n) z) atTop (𝓝 (sourceInverseContact f p F none z)) :=by
  have R:=sourceResolvent_limit f p F z 0 (movingDiagonal_units f p F z hz).self_of_nhds
  have J:=sourceCurrent_limit f p F 0
  have K:=sourceContact_limit f p F
  exact (((R.mul K).mul R).sub ((((R.mul J).mul R).mul J).mul R) |>.sub ((((R.mul J).mul R).mul J).mul R)).neg

lemma paired_limit {ι : Type*} {l : Filter ι} {A : ι→H →L[ℂ] H} {B : H →L[ℂ] H}
    (h : Tendsto A l (𝓝 B)) (x y : H) : Tendsto (fun i=>inner ℂ x (A i y)) l (𝓝 (inner ℂ x (B y))) :=
  ((continuous_const.inner ((continuous_id.clm_apply continuous_const))).continuousAt.tendsto).comp h

theorem observed_uncut_limit (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>truePreparedResponse epsilon precision f p F n z left right a s b t 0) atTop
      (𝓝 (observedResponse epsilon precision f p F none z left right a s b t 0)) :=by
  have h:=paired_limit (sourceResolvent_limit f p F z 0 (movingDiagonal_units f p F z hz).self_of_nhds)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  exact h.congr' (Filter.Eventually.of_forall fun n=>(observed_cut_readback epsilon precision f p F n z hz left right a s b t).self_of_nhds)

theorem observed_first_exchange (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>deriv (truePreparedResponse epsilon precision f p F n z left right a s b t) 0) atTop
      (𝓝 (deriv (observedResponse epsilon precision f p F none z left right a s b t) 0)) :=by
  have values (o : Option ℕ) :=(observedJets epsilon precision f p F o z hz left right a s b t).actual.1.deriv
  have source (n : ℕ) :=(observed_cut_readback epsilon precision f p F n z hz left right a s b t).deriv_eq
  simp_rw [←source,values]
  exact paired_limit (sourceInsertion_limit f p F z hz).neg _ _

theorem observed_second_exchange (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>deriv (deriv (truePreparedResponse epsilon precision f p F n z left right a s b t)) 0) atTop
      (𝓝 (deriv (deriv (observedResponse epsilon precision f p F none z left right a s b t)) 0)) :=by
  have values (o : Option ℕ) :=(observedJets epsilon precision f p F o z hz left right a s b t).actual.2.deriv
  have source (n : ℕ) :=(observed_cut_readback epsilon precision f p F n z hz left right a s b t).deriv.deriv_eq
  simp_rw [←source,values]
  exact paired_limit (sourceContactInsertion_limit f p F z hz) _ _

theorem observed_uncut_domain (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (z : ℂ) (hz : z.im≠0) (right : Bool) (b t : Fin 2) :
    ∀ᶠr in 𝓝 (0:ℝ),∃hy : sourceResolvent f p F none z r
        (completedLeg right b t (sourceProfile epsilon precision))∈(movedClosedY f r).domain,
      transportedCompression f p F r (sourceResolvent f p F none z r (completedLeg right b t (sourceProfile epsilon precision)))+
        (movedClosedY f r) ⟨sourceResolvent f p F none z r (completedLeg right b t (sourceProfile epsilon precision)),hy⟩-
        z • sourceResolvent f p F none z r (completedLeg right b t (sourceProfile epsilon precision))=
        completedLeg right b t (sourceProfile epsilon precision) :=
  (movingDiagonal_units f p F z hz).mono fun r hr=>uncut_resolvent_domain f p F z
    (fun h=>hz (by rw [h];rfl)) r hr _ (profileLeg_retained epsilon precision p F right b t)

theorem observed_uncut_limit_near (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    ∀ᶠr in 𝓝 (0:ℝ),Tendsto (fun n=>truePreparedResponse epsilon precision f p F n z left right a s b t r) atTop
      (𝓝 (observedResponse epsilon precision f p F none z left right a s b t r)) :=by
  filter_upwards [movingDiagonal_units f p F z hz] with r hr
  have h:=paired_limit (sourceResolvent_limit f p F z r hr)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  apply h.congr'
  exact Filter.Eventually.of_forall fun n=>congrArg (fun y : H=>inner ℂ (completedLeg left a s (sourceProfile epsilon precision)) y)
    (sourceResolvent_cut f p F n z (fun eq=>hz (by rw [eq];rfl)) r hr _ (profileLeg_retained epsilon precision p F right b t))

def observedCurvature (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  observedResponse epsilon precision (readerReal sourceMomentum row) p F o z left right a s b t r+
    Complex.I*(observedResponse epsilon precision (readerImag sourceMomentum row) p F o z left right a s b t r-
      observedResponse epsilon precision (readerImag sourceMomentum row) p F o z left right a s b t 0)

def observedCurvatureJets (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (o : Option ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (observedCurvature epsilon precision sourceMomentum row p F o z left right a s b t) :=
  (observedJets epsilon precision (readerReal sourceMomentum row) p F o z hz left right a s b t).add
    (TwoJets.scale Complex.I ((observedJets epsilon precision (readerImag sourceMomentum row) p F o z hz left right a s b t).sub
      (constantPairJets (observedResponse epsilon precision (readerImag sourceMomentum row) p F o z left right a s b t 0))))

theorem curvature_cut_readback (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    observedCurvature epsilon precision sourceMomentum row p F (some n) z left right a s b t=ᶠ[𝓝 0]
      trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t :=by
  have hr:=observed_cut_readback epsilon precision (readerReal sourceMomentum row) p F n z hz left right a s b t
  have hi:=observed_cut_readback epsilon precision (readerImag sourceMomentum row) p F n z hz left right a s b t
  filter_upwards [hr,hi] with r er ei
  change observedResponse epsilon precision (readerReal sourceMomentum row) p F (some n) z left right a s b t r+
    Complex.I*(observedResponse epsilon precision (readerImag sourceMomentum row) p F (some n) z left right a s b t r-
      observedResponse epsilon precision (readerImag sourceMomentum row) p F (some n) z left right a s b t 0)=_
  rw [er,ei,hi.self_of_nhds]
  rfl

theorem curvature_uncut_limit (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t 0) atTop
      (𝓝 (observedCurvature epsilon precision sourceMomentum row p F none z left right a s b t 0)) :=by
  simpa only [trueCurvatureResponse,observedCurvature,sub_self,mul_zero,add_zero] using
    observed_uncut_limit epsilon precision (readerReal sourceMomentum row) p F z hz left right a s b t

theorem curvature_first_exchange (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>deriv (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t) 0) atTop
      (𝓝 (deriv (observedCurvature epsilon precision sourceMomentum row p F none z left right a s b t) 0)) :=by
  have read (n : ℕ):=(curvature_cut_readback epsilon precision sourceMomentum row p F n z hz left right a s b t).deriv_eq
  have value (o : Option ℕ):=(observedCurvatureJets epsilon precision sourceMomentum row p F o z hz left right a s b t).actual.1.deriv
  simp_rw [←read,value]
  have R:=paired_limit (sourceInsertion_limit (readerReal sourceMomentum row) p F z hz).neg
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  have I:=paired_limit (sourceInsertion_limit (readerImag sourceMomentum row) p F z hz).neg
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  exact R.add ((I.sub tendsto_const_nhds).const_mul Complex.I)

theorem curvature_second_exchange (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    Tendsto (fun n=>deriv (deriv (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t)) 0) atTop
      (𝓝 (deriv (deriv (observedCurvature epsilon precision sourceMomentum row p F none z left right a s b t)) 0)) :=by
  have read (n : ℕ):=(curvature_cut_readback epsilon precision sourceMomentum row p F n z hz left right a s b t).deriv.deriv_eq
  have value (o : Option ℕ):=(observedCurvatureJets epsilon precision sourceMomentum row p F o z hz left right a s b t).actual.2.deriv
  simp_rw [←read,value]
  have R:=paired_limit (sourceContactInsertion_limit (readerReal sourceMomentum row) p F z hz)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  have I:=paired_limit (sourceContactInsertion_limit (readerImag sourceMomentum row) p F z hz)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))
  exact R.add ((I.sub tendsto_const_nhds).const_mul Complex.I)

end LowEnergy.PreparationVacuumUncutYukawa
