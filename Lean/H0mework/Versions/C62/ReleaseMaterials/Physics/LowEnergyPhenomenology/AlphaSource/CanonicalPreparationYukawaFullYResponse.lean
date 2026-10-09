import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaLocalJets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumYukawaTransport
open GaussCoreHilbert GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumGradedTransport PreparationVacuumFullFieldRiesz PreparationVacuumMixedFieldReturn
open PreparationVacuumFieldConstraintResponse PreparationVacuumSourceActionJets
open NativeHistoryGrade (Label projection)
open CanonicalPhysicalYResolvent FullYSourceCutoffVolterra
open PreparationVacuumPreparedCurrent PreparationVacuumNativeClosure
open Filter Set
open scoped Topology InnerProductSpace BigOperators
local instance : Fintype Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) :=NormedAlgebra.restrictScalars ℝ ℂ _

attribute [local irreducible] projection GaussYukawaGrade.grade transportedCompression transportedCurrent transportedContact
  fieldCutoff localY jetOperator retainer finiteFull

lemma frame_rankOne (p : PhysicalMomentum) (F : Index) (g : Label) (i j : PhysicalBasisIndex p F) :
    InnerProductSpace.rankOne ℂ (physicalFrame p F (g,i)) (physicalFrame p F (g,j))=
      projection g*InnerProductSpace.rankOne ℂ (physicalBasis p F i).val (physicalBasis p F j).val*projection g := by
  apply ContinuousLinearMap.ext;intro x
  simp only [physicalFrame,mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul]
  exact congrArg (fun c : ℂ=>c • projection g (physicalBasis p F i).val)
    (NativeHistoryGrade.projection_symmetric g (physicalBasis p F j).val x)

lemma sandwich_commutes {A : Type*} [Ring A] [Algebra ℂ A] (G P T : A) (c : ℂ)
    (left : G*P=c • P) (right : P*G=c • P) : Commute G (P*T*P) :=by
  change G*(P*T*P)=(P*T*P)*G
  calc
    _=(G*P)*T*P :=by simp only [mul_assoc]
    _=(c • P)*T*P :=congrArg (fun S=>S*T*P) left
    _=c • (P*T*P) :=by rw [smul_mul_assoc,smul_mul_assoc]
    _=(P*T)*(c • P) :=(mul_smul_comm c (P*T) P).symm
    _=(P*T)*(P*G) :=congrArg (fun S=>(P*T)*S) right.symm
    _=_ :=(mul_assoc (P*T) P G).symm

lemma sandwich_grade (g : Label) (A : H →L[ℂ] H) :
    Commute GaussYukawaGrade.grade (projection g*A*projection g) :=
  sandwich_commutes _ _ _ (g.2.val:ℂ) (GaussYukawaInteraction.source_grade_right g)
    (GaussYukawaInteraction.source_grade_left g)

lemma sourceAssembly_grade (p : PhysicalMomentum) (F : Index) (entries : PhysicalBasisIndex p F→PhysicalBasisIndex p F→ℂ) :
    Commute GaussYukawaGrade.grade (sourceAssembly p F entries) := by
  unfold sourceAssembly
  apply Commute.sum_right;intro g _
  apply Commute.sum_right;intro i _
  apply Commute.sum_right;intro j _
  rw [frame_rankOne]
  exact (sandwich_grade g _).smul_right _

lemma inverse_commuting {A : Type*} [MonoidWithZero A] (G D : A) (h : IsUnit D) (c : Commute G D) :
    Commute G (Ring.inverse D) := by
  have l:=Ring.inverse_mul_cancel D h
  have r:=Ring.mul_inverse_cancel D h
  change G*Ring.inverse D=Ring.inverse D*G
  calc
    _=(Ring.inverse D*D)*(G*Ring.inverse D) :=by rw [l,one_mul]
    _=Ring.inverse D*(D*G)*Ring.inverse D :=by simp only [mul_assoc]
    _=Ring.inverse D*(G*D)*Ring.inverse D :=by rw [c.eq]
    _=(Ring.inverse D*G)*(D*Ring.inverse D) :=by simp only [mul_assoc]
    _=Ring.inverse D*G :=by rw [r,mul_one]

lemma raised_nilpotent (N : H →L[ℂ] H)
    (raises : GaussYukawaGrade.grade*N=N*GaussYukawaGrade.grade+N) : N^57=0 := by
  have h:=FiniteGradeAlgebra.words_zero GaussYukawaGrade.grade projection
    (fun g : Label=>(g.2.val:ℤ)) NativeHistoryGrade.projection_resolution
    (fun g=>by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_left g)
    (fun g=>by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_right g)
    0 56 (fun g=>by have h:=g.2.isLt;constructor <;> omega)
    (List.replicate 57 N) (fun T h=>by obtain ⟨_,rfl⟩:=List.mem_replicate.mp h;exact raises) (by simp)
  simpa only [List.prod_replicate] using h

def movingDiagonal (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  transportedCompression f p F r-z • 1

def movingStep (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  -(Ring.inverse (movingDiagonal f p F z r)*fieldCutoff f n r)

lemma movingStep_nilpotent (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) : (movingStep f p F n z r)^57=0 := by
  apply raised_nilpotent
  have neutral:=sourceAssembly_grade p F (fun i j=>transportedForm f p (bareTest p F i) (bareTest p F j) r)
  have diag : Commute GaussYukawaGrade.grade (movingDiagonal f p F z r) :=by
    unfold movingDiagonal transportedCompression
    exact neutral.sub_right ((Commute.one_right _).smul_right z)
  exact negative_raises _ _ _ (inverse_commuting _ _ unit diag).eq (fieldCutoff_raises f n r)

def trueGenerator (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  transportedCompression f p F r+fieldCutoff f n r-z • 1

def trueResolvent (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  Ring.inverse (trueGenerator f p F n z r)

def movingSeries (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  (∑i∈Finset.range 57,(movingStep f p F n z r)^i)*Ring.inverse (movingDiagonal f p F z r)

lemma factor_add {A : Type*} [Ring A] (D U Y : A) (right : D*U=1) :
    D+Y=D*(1-(-(U*Y))) :=by
  rw [sub_neg_eq_add,mul_add,mul_one,←mul_assoc,right,one_mul]

lemma add_sub_reorder {A : Type*} [AddCommGroup A] (C Y Z : A) : C+Y-Z=C-Z+Y :=by abel

lemma moving_factor (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) :
    trueGenerator f p F n z r=movingDiagonal f p F z r*(1-movingStep f p F n z r) :=
  (add_sub_reorder (transportedCompression f p F r) (fieldCutoff f n r) (z • 1)).trans
    (factor_add _ _ _ (Ring.mul_inverse_cancel _ unit))

lemma geometric_inverse {A : Type*} [Ring A] (D U N : A) (m : ℕ)
    (left : U*D=1) (right : D*U=1) (nil : N^m=0) :
    ((∑i∈Finset.range m,N^i)*U)*(D*(1-N))=1 ∧ (D*(1-N))*((∑i∈Finset.range m,N^i)*U)=1 :=by
  constructor
  · calc
      _=(∑i∈Finset.range m,N^i)*(U*D)*(1-N) :=by simp only [mul_assoc]
      _=1 :=by rw [left,mul_one,geom_sum_mul_neg,nil,sub_zero]
  · calc
      _=D*((1-N)*(∑i∈Finset.range m,N^i))*U :=by simp only [mul_assoc]
      _=1 :=by rw [mul_neg_geom_sum,nil,sub_zero,mul_one,right]

lemma movingSeries_inverse (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) :
    movingSeries f p F n z r*trueGenerator f p F n z r=1 ∧
    trueGenerator f p F n z r*movingSeries f p F n z r=1 := by
  rw [moving_factor f p F n z r unit]
  exact geometric_inverse _ _ _ 57 (Ring.inverse_mul_cancel _ unit) (Ring.mul_inverse_cancel _ unit)
    (movingStep_nilpotent f p F n z r unit)

lemma trueResolvent_series (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) : trueResolvent f p F n z r=movingSeries f p F n z r := by
  have h:=movingSeries_inverse f p F n z r unit
  let u : (H →L[ℂ] H)ˣ:=⟨trueGenerator f p F n z r,movingSeries f p F n z r,h.2,h.1⟩
  exact Ring.inverse_unit u

lemma movingDiagonal_units (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z.im≠0) :
    ∀ᶠr in 𝓝 (0:ℝ),IsUnit (movingDiagonal f p F z r) := by
  let u : (H →L[ℂ] H)ˣ:=⟨CanonicalPhysicalSpatial.compression p F-z • 1,
    CanonicalPhysicalResolvent.finiteResolvent p F z,
    FullYSourceResolventGraphSplice.resolvent_right _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z hz,
    FullYSourceResolventGraphSplice.resolvent_left _ (CanonicalPhysicalSpatial.compression_selfAdjoint p F) z hz⟩
  have h : movingDiagonal f p F z 0=(u:H →L[ℂ] H) :=by unfold movingDiagonal;rw [transportedCompression_zero f p F]
  have near : ∀ᶠA : H →L[ℂ] H in 𝓝 (movingDiagonal f p F z 0),IsUnit A :=by rw [h];exact Units.nhds u
  exact ((transportedCompression_first f p F).sub_const (z • 1)).continuousAt.eventually near

lemma movingDiagonal_retained (f : Field289) (p : PhysicalMomentum) (F : Index) (z : ℂ) (hz : z≠0) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) (x : H) (hx : x∈retainedSpace p F) :
    Ring.inverse (movingDiagonal f p F z r) x∈retainedSpace p F := by
  let v:=Ring.inverse (movingDiagonal f p F z r) x
  have equation:=congrArg (fun A : H →L[ℂ] H=>A x) (Ring.mul_inverse_cancel _ unit)
  change transportedCompression f p F r v-z • v=x at equation
  have range : transportedCompression f p F r v∈retainedSpace p F :=by
    apply (retainedSpace_iff p F _).mpr
    unfold transportedCompression
    exact congrArg (fun A : H →L[ℂ] H=>A v) (retainer_assembly p F _)
  have scaled : z • v∈retainedSpace p F :=by
    have e : z • v=transportedCompression f p F r v-x :=by rw [←equation];abel
    rw [e];exact (retainedSpace p F).sub_mem range hx
  exact ((retainedSpace p F).smul_mem_iff hz).mp scaled

lemma trueResolvent_retained (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z≠0) (r : ℝ)
    (unit : IsUnit (movingDiagonal f p F z r)) (x : H) (hx : x∈retainedSpace p F) :
    trueResolvent f p F n z r x∈retainedSpace p F := by
  have step (y : H) (hy : y∈retainedSpace p F) : movingStep f p F n z r y∈retainedSpace p F :=
    (retainedSpace p F).neg_mem (movingDiagonal_retained f p F z hz r unit _ (fieldCutoff_retained f n p F r y hy))
  have powers (m : ℕ) (y : H) (hy : y∈retainedSpace p F) : ((movingStep f p F n z r)^m) y∈retainedSpace p F :=by
    induction m with
    | zero=>simpa only [pow_zero,one_apply_eq_self] using hy
    | succ m ih=>rw [pow_succ',mul_apply_eq_comp];exact step _ ih
  rw [trueResolvent_series f p F n z r unit]
  simp only [movingSeries,mul_apply_eq_comp,sum_apply]
  exact (retainedSpace p F).sum_mem fun i _=>powers i _ (movingDiagonal_retained f p F z hz r unit x hx)

def smoothGenerator (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  transportedCompression f p F r+localY f n p F r-z • 1

def smoothResolvent (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  Ring.inverse (smoothGenerator f p F n z r)

def fullCurrent (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (r : ℝ) : H →L[ℂ] H :=
  transportedCurrent f p F r+jetOperator f n 1 (finiteRetainer p F) r

def fullContact (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) : H →L[ℂ] H :=
  transportedContact f p F+jetOperator f n 2 (finiteRetainer p F) 0

lemma smoothGenerator_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (smoothGenerator f p F n z) (fullCurrent f p F n r) r :=
  (transportedCompression_derivative_near f p F).mono fun r hr=>
    (hr.add (localY_derivative f n p F r)).sub_const (z • 1)

lemma fullCurrent_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) :
    HasDerivAt (fullCurrent f p F n) (fullContact f p F n) 0 := by
  convert! (transportedCurrent_second f p F).add (jetOperator_derivative f n 1 (finiteRetainer p F) 0) using 1

lemma smoothGenerator_zero (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) :
    smoothGenerator f p F n z 0=CanonicalPhysicalSpatial.compression p F+cutoff n-z • 1 :=by
  rw [smoothGenerator,transportedCompression_zero f p F,localY_zero f n p F]

lemma smoothResolvent_zero (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    smoothResolvent f p F n z 0=finiteFull p F n z :=by
  rw [smoothResolvent,smoothGenerator_zero]
  exact Ring.inverse_unit (originalFullUnit p F n z hz)

lemma smoothGenerator_units (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    ∀ᶠr in 𝓝 (0:ℝ),IsUnit (smoothGenerator f p F n z r) :=by
  have available : ∀ᶠA : H →L[ℂ] H in 𝓝 (smoothGenerator f p F n z 0),IsUnit A :=by
    rw [smoothGenerator_zero];exact Units.nhds (originalFullUnit p F n z hz)
  exact (smoothGenerator_derivative f p F n z).self_of_nhds.continuousAt.eventually available

lemma smoothResolvent_source (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0)
    (x : H) (hx : x∈retainedSpace p F) :
    (fun r=>smoothResolvent f p F n z r x)=ᶠ[𝓝 0] fun r=>trueResolvent f p F n z r x :=by
  filter_upwards [movingDiagonal_units f p F z hz,smoothGenerator_units f p F n z hz] with r hd hs
  have nz : z≠0 :=fun h=>hz (by rw [h];rfl)
  have kept:=trueResolvent_retained f p F n z nz r hd x hx
  have right:=congrArg (fun A : H →L[ℂ] H=>A x) (movingSeries_inverse f p F n z r hd).2
  rw [←trueResolvent_series f p F n z r hd] at right
  change trueGenerator f p F n z r (trueResolvent f p F n z r x)=x at right
  have same : smoothGenerator f p F n z r (trueResolvent f p F n z r x)=x :=by
    simpa only [smoothGenerator,trueGenerator,sub_apply,add_apply,localY_source f n p F r _ kept] using right
  have left:=congrArg (fun A : H →L[ℂ] H=>A (trueResolvent f p F n z r x))
    (Ring.inverse_mul_cancel _ hs)
  change smoothResolvent f p F n z r (smoothGenerator f p F n z r (trueResolvent f p F n z r x))=trueResolvent f p F n z r x at left
  rwa [same] at left

def fullInsertion (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (r : ℝ) : H →L[ℂ] H :=
  smoothResolvent f p F n z r*fullCurrent f p F n r*smoothResolvent f p F n z r

lemma smoothResolvent_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    ∀ᶠr in 𝓝 (0:ℝ),HasDerivAt (smoothResolvent f p F n z) (-fullInsertion f p F n z r) r :=by
  filter_upwards [smoothGenerator_units f p F n z hz,smoothGenerator_derivative f p F n z] with r hu hd
  exact inverse_curve_derivative _ r _ hd hu

def fullResolventContact (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) : H →L[ℂ] H :=
  -(finiteFull p F n z*fullContact f p F n*finiteFull p F n z-
    finiteFull p F n z*fullCurrent f p F n 0*finiteFull p F n z*fullCurrent f p F n 0*finiteFull p F n z-
    finiteFull p F n z*fullCurrent f p F n 0*finiteFull p F n z*fullCurrent f p F n 0*finiteFull p F n z)

lemma fullInsertion_derivative (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    HasDerivAt (fun r=> -fullInsertion f p F n z r) (fullResolventContact f p F n z) 0 :=by
  have R:=(smoothResolvent_derivative f p F n z hz).self_of_nhds
  have J:=fullCurrent_derivative f p F n
  have product:=(R.mul J).mul R
  simp only [Pi.mul_apply,fullInsertion,smoothResolvent_zero f p F n z hz] at product
  have algebra:=inverse_insertion_algebra (finiteFull p F n z) (fullCurrent f p F n 0) (fullContact f p F n)
  convert! (product.congr_deriv algebra.symm).neg using 1

open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph

lemma profileLeg_retained (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (F : Index)
    (addition : Bool) (a s : Fin 2) :
    completedLeg addition a s (sourceProfile epsilon precision)∈retainedSpace p F :=
  sourceLeg_retained p F addition a s (sourceCausalState epsilon precision).point.val

def truePreparedResponse (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (trueResolvent f p F n z r (completedLeg right b t (sourceProfile epsilon precision)))

def truePreparedJets (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (truePreparedResponse epsilon precision f p F n z left right a s b t) where
  first r:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    ((-fullInsertion f p F n z r) (completedLeg right b t (sourceProfile epsilon precision)))
  second:=inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
    (fullResolventContact f p F n z (completedLeg right b t (sourceProfile epsilon precision)))
  derivative_near:=by
    have same:=smoothResolvent_source f p F n z hz _ (profileLeg_retained epsilon precision p F right b t)
    filter_upwards [smoothResolvent_derivative f p F n z hz,same.eventually_nhds] with r hd he
    apply (paired_derivative hd (completedLeg left a s (sourceProfile epsilon precision))
      (completedLeg right b t (sourceProfile epsilon precision))).congr_of_eventuallyEq
    exact he.mono fun r hr=>congrArg (fun y : H=>inner ℂ (completedLeg left a s (sourceProfile epsilon precision)) y) hr.symm
  second_derivative:=paired_derivative (fullInsertion_derivative f p F n z hz)
    (completedLeg left a s (sourceProfile epsilon precision)) (completedLeg right b t (sourceProfile epsilon precision))

theorem truePreparedResponse_first (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (truePreparedResponse epsilon precision f p F n z left right a s b t)
      (-inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        ((finiteFull p F n z*fullCurrent f p F n 0*finiteFull p F n z)
          (completedLeg right b t (sourceProfile epsilon precision)))) 0 :=by
  have h:=(truePreparedJets epsilon precision f p F n z hz left right a s b t).actual.1
  simpa only [truePreparedJets,fullInsertion,smoothResolvent_zero f p F n z hz,neg_apply,inner_neg_right] using h

def trueCurvatureResponse (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (left right : Bool) (a s b t : Fin 2) (r : ℝ) : ℂ :=
  truePreparedResponse epsilon precision (readerReal sourceMomentum row) p F n z left right a s b t r+
    Complex.I*(truePreparedResponse epsilon precision (readerImag sourceMomentum row) p F n z left right a s b t r-
      truePreparedResponse epsilon precision (readerImag sourceMomentum row) p F n z left right a s b t 0)

def trueCurvatureJets (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    TwoJets (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t) :=
  (truePreparedJets epsilon precision (readerReal sourceMomentum row) p F n z hz left right a s b t).add
    (TwoJets.scale Complex.I ((truePreparedJets epsilon precision (readerImag sourceMomentum row) p F n z hz left right a s b t).sub
      (constantPairJets (truePreparedResponse epsilon precision (readerImag sourceMomentum row) p F n z left right a s b t 0))))

theorem trueResolvent_zero (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) :
    trueResolvent f p F n z 0=finiteFull p F n z :=by
  rw [trueResolvent,trueGenerator,transportedCompression_zero f p F,fieldCutoff_zero f n]
  exact Ring.inverse_unit (originalFullUnit p F n z hz)

theorem truePreparedResponse_zero (epsilon : ℝ) (precision : 0<epsilon) (f : Field289) (p : PhysicalMomentum)
    (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    truePreparedResponse epsilon precision f p F n z left right a s b t 0=
      inner ℂ (completedLeg left a s (sourceProfile epsilon precision))
        (finiteFull p F n z (completedLeg right b t (sourceProfile epsilon precision))) :=by
  rw [truePreparedResponse,trueResolvent_zero f p F n z hz]

def fullCurrentPrice (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) : ℝ :=
  currentMatrixPrice f p F+‖(jetTest f n 1 (finiteRetainer p F) 0 : BoundedContinuousFunction SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice Fiber)‖

theorem fullCurrent_price (f : Field289) (p : PhysicalMomentum) (F : Index) (n : ℕ) :
    ‖fullCurrent f p F n 0‖≤fullCurrentPrice f p F n :=by
  apply (norm_add_le _ _).trans
  apply add_le_add (transportedCurrent_price f p F)
  unfold jetOperator
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

def trueVertex (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ) : H →L[ℂ] H :=
  finiteFull (p+k) F n z*fullCurrent f p F n 0*finiteFull p F n w

theorem trueVertex_price (f : Field289) (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) :
    ‖trueVertex f p k F n z w‖≤normBound n z*fullCurrentPrice f p F n*normBound n w :=
  triple_price _ _ _ _ _ _ (finiteFull_bound (p+k) F n z hz) (fullCurrent_price f p F n) (finiteFull_bound p F n w hw)

theorem trueCurvatureResponse_two_jets (epsilon : ℝ) (precision : 0<epsilon) (sourceMomentum : Fin 4→ℂ) (row : Fin 36)
    (p : PhysicalMomentum) (F : Index) (n : ℕ) (z : ℂ) (hz : z.im≠0) (left right : Bool) (a s b t : Fin 2) :
    HasDerivAt (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t)
      ((trueCurvatureJets epsilon precision sourceMomentum row p F n z hz left right a s b t).first 0) 0 ∧
    HasDerivAt (deriv (trueCurvatureResponse epsilon precision sourceMomentum row p F n z left right a s b t))
      (trueCurvatureJets epsilon precision sourceMomentum row p F n z hz left right a s b t).second 0 :=
  (trueCurvatureJets epsilon precision sourceMomentum row p F n z hz left right a s b t).actual

end LowEnergy.PreparationVacuumYukawaTransport
