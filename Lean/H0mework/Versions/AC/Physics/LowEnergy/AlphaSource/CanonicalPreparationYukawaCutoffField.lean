import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTransportedGraded

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumYukawaTransport
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussYukawaCoefficient GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussNativePotential GaussFockWeights GaussYukawaGrade GaussBoundedMultiplier
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldConstraintResponse PreparationVacuumGradedTransport
open FullYSourceCutoffVolterra
open scoped Topology ContDiff InnerProductSpace BigOperators

-- The literal original finite geometric recursion, before Hilbert completion.
def cutFiber : ℕ → SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber :=
  Nat.rec normalized (fun _ previous z=>normalized z+((1-reciprocal z:ℝ):ℂ) • previous z)

theorem cutFiber_smooth (n : ℕ) : ContDiff ℝ ∞ (cutFiber n) := by
  induction n with
  | zero=>exact normalized_smooth
  | succ n ih=>
    exact normalized_smooth.add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub reciprocal_smooth)).smul ih)

theorem cutFiber_number (n : ℕ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (weight w) (cutFiber n z) := by
  induction n with
  | zero=>exact normalized_commutes z w
  | succ n ih=>exact (normalized_commutes z w).add_right (ih.smul_right _)

theorem cutFiber_bound (n : ℕ) (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖cutFiber n z v‖≤(n+1:ℕ)*bound*‖v‖ := by
  have hq : 0≤1-reciprocal z := sub_nonneg.mpr (inv_le_one_of_one_le₀ (one_le_radius z))
  have hq1 : 1-reciprocal z≤1 := sub_le_self _ (inv_pos.mpr (radius_pos z)).le
  induction n with
  | zero=>
    change ‖normalized z v‖≤((0+1:ℕ):ℝ)*bound*‖v‖
    simpa only [Nat.zero_add,Nat.cast_one,one_mul] using normalized_bound z v
  | succ n ih=>
    change ‖normalized z v+((1-reciprocal z:ℝ):ℂ) • (cutFiber n z v)‖≤_
    have norm : ‖((1-reciprocal z:ℝ):ℂ)‖≤1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq] using hq1
    have small : ‖((1-reciprocal z:ℝ):ℂ) • (cutFiber n z v)‖≤‖cutFiber n z v‖ := by
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) norm
    have h:=(norm_add_le (normalized z v) (((1-reciprocal z:ℝ):ℂ) • (cutFiber n z v))).trans
      (add_le_add (normalized_bound z v) (small.trans ih))
    push_cast at h ⊢
    nlinarith

def cutAction (n : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (cutFiber n) (fun _=>(cutFiber_smooth n).contDiffAt)

theorem cutAction_apply (n : ℕ) (a : QuantumTest) (z : SourceCoordinateSlice) :
    cutAction n a z=cutFiber n z (a z) := rfl

theorem original_cutoff_core (n : ℕ) (a : QuantumTest) : cutoff n (embed a)=embed (cutAction n a) := by
  induction n with
  | zero=>exact GaussYukawaOperator.bounded_core a
  | succ n ih=>
    change GaussYukawaOperator.bounded (embed a)+(cutoff n (embed a)-inverseRadius (cutoff n (embed a)))=_
    rw [GaussYukawaOperator.bounded_core,ih,inverse_core,←map_sub,←map_add]
    apply congrArg embed
    apply DFunLike.ext; intro z
    change normalized z (a z)+(cutFiber n z (a z)-(reciprocal z:ℂ) • (cutFiber n z (a z)))=
      (normalized z+((1-reciprocal z:ℝ):ℂ) • cutFiber n z) (a z)
    simp only [add_apply,smul_apply,Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]

theorem cutFiber_grade (n : ℕ) (z : SourceCoordinateSlice) (v : FockFiber) :
    fiberGrade (cutFiber n z v)=cutFiber n z (fiberGrade v)+cutFiber n z v := by
  induction n with
  | zero=>exact fiber_source_grade (normalizedScalar z) v
  | succ n ih=>
    change fiberGrade ((normalized z+((1-reciprocal z:ℝ):ℂ) • cutFiber n z) v)=
      (normalized z+((1-reciprocal z:ℝ):ℂ) • cutFiber n z) (fiberGrade v)+
      (normalized z+((1-reciprocal z:ℝ):ℂ) • cutFiber n z) v
    simp only [add_apply,smul_apply,map_add,map_smul,ih]
    have base : fiberGrade (normalized z v)=normalized z (fiberGrade v)+normalized z v := fiber_source_grade (normalizedScalar z) v
    rw [base]
    simp only [smul_add]
    abel

def fieldCutoff (f : Field289) (n : ℕ) (r : ℝ) : H →L[ℂ] H :=
  extension (fun z=>cutFiber n (fieldCoordinateCurve f r z))
    (fun z=>(cutFiber_smooth n).contDiffAt.comp z.val
      ((field_curve_smooth f r z).comp z.val (contDiff_const.prodMk contDiff_id).contDiffAt))
    (fun z w=>cutFiber_number n (fieldCoordinateCurve f r z.val) w)
    ((n+1:ℕ)*bound) (mul_nonneg (Nat.cast_nonneg _) bound_nonneg)
    (fun z v=>cutFiber_bound n (fieldCoordinateCurve f r z.val) v)

def fieldCutoffAction (f : Field289) (n : ℕ) (r : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z=>cutFiber n (fieldCoordinateCurve f r z))
    (fun z=>(cutFiber_smooth n).contDiffAt.comp z.val
      ((field_curve_smooth f r z).comp z.val (contDiff_const.prodMk contDiff_id).contDiffAt))

theorem fieldCutoff_core (f : Field289) (n : ℕ) (r : ℝ) (a : QuantumTest) :
    fieldCutoff f n r (embed a)=embed (fieldCutoffAction f n r a) :=
  extension_core _ _ _ _ _ _ a

theorem fieldCutoff_norm (f : Field289) (n : ℕ) (r : ℝ) : ‖fieldCutoff f n r‖≤(n+1:ℕ)*bound :=
  extension_norm _ _ _ _ _ _

theorem fieldCutoff_zero (f : Field289) (n : ℕ) : fieldCutoff f n 0=cutoff n := by
  apply GaussYukawaGrade.core_ext
  intro a
  rw [fieldCutoff_core,original_cutoff_core]
  apply congrArg embed
  apply DFunLike.ext; intro z
  change cutFiber n (fieldCoordinateCurve f 0 z) (a z)=cutFiber n z (a z)
  rw [curve_zero]

theorem fieldCutoff_raises (f : Field289) (n : ℕ) (r : ℝ) :
    GaussYukawaGrade.grade*fieldCutoff f n r=fieldCutoff f n r*GaussYukawaGrade.grade+fieldCutoff f n r := by
  apply GaussYukawaGrade.core_ext
  intro a
  change GaussYukawaGrade.grade (fieldCutoff f n r (embed a))=fieldCutoff f n r (GaussYukawaGrade.grade (embed a))+fieldCutoff f n r (embed a)
  rw [fieldCutoff_core,grade_core,grade_core,fieldCutoff_core,←map_add]
  apply congrArg embed
  apply DFunLike.ext; intro z
  exact cutFiber_grade n (fieldCoordinateCurve f r z) (a z)

theorem cutoff_density_transport (f : Field289) (n : ℕ) (r : ℝ) (z : physicalChart)
    (hx : fieldCoordinateCurve f r z.val∈physicalChart) (a b : FockFiber) :
    PreparationVacuumSourceActionJets.pairSample (fieldCoordinateCurve f r z.val)
      (transportFiber f z.val r a) (cutFiber n (fieldCoordinateCurve f r z.val) (transportFiber f z.val r b))=
    PreparationVacuumSourceActionJets.pairSample z.val a (cutFiber n (fieldCoordinateCurve f r z.val) b) := by
  have commute:=(cutFiber_number n (fieldCoordinateCurve f r z.val) (fun N=>halfRatio f N z.val r)).eq
  have moved:=congrArg (fun A : FockFiber →L[ℂ] FockFiber=>A b) commute
  change transportFiber f z.val r (cutFiber n (fieldCoordinateCurve f r z.val) b)=
    cutFiber n (fieldCoordinateCurve f r z.val) (transportFiber f z.val r b) at moved
  rw [←moved]
  exact pair_transport f z r hx a _

open CanonicalGradedSpatialSource
open NativeHistoryGrade (Label projection)
local instance : Fintype Label:=Fintype.ofFinite _

def fieldStep (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (n : ℕ) (r : ℝ) (z : ℂ) : H →L[ℂ] H :=
  -(CanonicalPhysicalResolvent.finiteResolvent p F z*fieldCutoff f n r)

theorem negative_raises {A : Type*} [Ring A] (G R Y : A) (hR : G*R=R*G) (hY : G*Y=Y*G+Y) :
    G*(-(R*Y))=(-(R*Y))*G+(-(R*Y)) := by
  rw [mul_neg,←mul_assoc,hR,mul_assoc,hY]
  simp only [mul_add,neg_add,neg_mul,mul_assoc]

theorem fieldStep_raises (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (r : ℝ) (z : ℂ) (hz : z.im≠0) :
    GaussYukawaGrade.grade*fieldStep f p F n r z=fieldStep f p F n r z*GaussYukawaGrade.grade+fieldStep f p F n r z :=
  negative_raises _ _ _ (CanonicalPhysicalYResolvent.resolvent_grade p F z hz).eq (fieldCutoff_raises f n r)

theorem fieldStep_full57 (f : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (r : ℝ) (z : ℂ) (hz : z.im≠0) : (fieldStep f p F n r z)^57=0 := by
  have h:=FiniteGradeAlgebra.words_zero GaussYukawaGrade.grade projection
    (fun g : Label=>(g.2.val:ℤ)) NativeHistoryGrade.projection_resolution
    (fun g=>by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_left g)
    (fun g=>by simpa only [Int.cast_natCast] using GaussYukawaInteraction.source_grade_right g)
    0 56 (fun g=>by have h:=g.2.isLt;constructor <;>omega)
    (List.replicate 57 (fieldStep f p F n r z))
    (fun T member=>by obtain ⟨_,rfl⟩:=List.mem_replicate.mp member;exact fieldStep_raises f p F n r z hz)
    (by simp)
  simpa only [List.prod_replicate] using h

end LowEnergy.PreparationVacuumYukawaTransport
