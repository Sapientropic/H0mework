import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationYukawaFullYResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumUncutYukawa
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussFockPair GaussFockWeights
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeCenterMagnetic
open GaussQuantumMultiplier
open GaussNativePotential GaussYukawaCoefficient GaussRadialDomain GaussYukawaOperator
open PreparationVacuumYukawaTransport PreparationVacuumGradedTransport
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn PreparationVacuumSourceActionJets
open CanonicalGradedLocalCurrent PreparationVacuumFullFieldRiesz
open Filter Set
open scoped Topology ContDiff InnerProductSpace BigOperators Distributions LinearPMap
abbrev Fiber:=PreparationVacuumYukawaTransport.Fiber
local instance : NormedAlgebra ℝ Fiber:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H):=NormedAlgebra.restrictScalars ℝ ℂ _

def uncutFiber (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : Fiber :=
  sourceMap (scalarField (fieldCoordinateCurve f r z))

def slopeFiber (f : Field289) (z : SourceCoordinateSlice) : Fiber :=
  sourceMap ((fieldVector f z).2.1 : Scalar)

theorem uncutFiber_affine (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) :
    uncutFiber f r z=uncutFiber f 0 z+r • slopeFiber f z :=by
  unfold uncutFiber slopeFiber
  rw [curve_zero]
  have fields : scalarField (fieldCoordinateCurve f r z)=scalarField z+r • ((fieldVector f z).2.1:Scalar) :=by
    change vacuum+((z.2.1:Scalar)+r • ((fieldVector f z).2.1:Scalar))=(vacuum+(z.2.1:Scalar))+r • ((fieldVector f z).2.1:Scalar)
    exact (add_assoc _ _ _).symm
  rw [fields,map_add,map_smul]

theorem uncutFiber_smooth (f : Field289) (u : Parameter) (hz : u.2∈physicalChart) :
    ContDiffAt ℝ ∞ (fun v : Parameter=>uncutFiber f v.1 v.2) u :=
  sourceMap.contDiff.contDiffAt.comp u (scalarField_smooth.contDiffAt.comp u (field_curve_smooth f u.1 ⟨u.2,hz⟩))

theorem slopeFiber_smooth (f : Field289) (z : physicalChart) : ContDiffAt ℝ ∞ (slopeFiber f) z.val :=
  sourceMap.contDiff.contDiffAt.comp z.val
    (SourceQuantumScalarChart.scalarSlice.subtypeL.contDiff.contDiffAt.comp z.val (fieldVector_smooth f z).snd.fst)

theorem sourceMap_number (v : Scalar) (w : ℕ→ℂ) : Commute (weight w) (sourceMap v) :=by
  rw [source_map_return]
  exact weight_commute w _

def uncutAction (f : Field289) (r : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (uncutFiber f r) (fun z=>(uncutFiber_smooth f (r,z.val) z.property).comp z.val
    (contDiff_const.prodMk contDiff_id).contDiffAt)

def compactFiber (f : Field289) (phi : Localizer) (u : Parameter) : Fiber :=
  (phi u.2:ℂ) • uncutFiber f u.1 u.2

theorem compactFiber_smooth (f : Field289) (phi : Localizer) : ContDiff ℝ ∞ (compactFiber f phi) :=by
  apply contDiff_iff_contDiffAt.mpr;intro u
  by_cases inside : u.2∈tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u (phi.contDiff.contDiffAt.comp u contDiffAt_snd)).smul
      (uncutFiber_smooth f u (phi.tsupport_subset inside))
  · apply (contDiffAt_const (c:=(0:Fiber))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isClosed_tsupport phi |>.isOpen_compl.mem_nhds inside)] with v hv
    simp only [compactFiber,image_eq_zero_of_notMem_tsupport hv,Complex.ofReal_zero]
    exact zero_smul ℂ (uncutFiber f v.1 v.2)

def uncutTest (f : Field289) (phi : Localizer) (r : ℝ) : 𝓓(physicalChart,Fiber) where
  toFun z:=compactFiber f phi (r,z)
  contDiff':=(compactFiber_smooth f phi).comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport':=by
    apply phi.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside
    apply hz
    simp only [compactFiber,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
    exact zero_smul ℂ (uncutFiber f r z)
  tsupport_subset':=by
    apply Set.Subset.trans _ phi.tsupport_subset
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz;by_contra outside
    apply hz
    simp only [compactFiber,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
    exact zero_smul ℂ (uncutFiber f r z)

def uncutOperator (f : Field289) (phi : Localizer) (r : ℝ) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun z=>compactFiber f phi (r,z))
    (fun _=>(uncutTest f phi r).contDiff.contDiffAt)
    (fun z w=>(sourceMap_number (scalarField (fieldCoordinateCurve f r z.val)) w).smul_right (phi z.val:ℂ))
    ‖(uncutTest f phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber)‖ (by exact norm_nonneg (uncutTest f phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber))
    (fun z v=>((compactFiber f phi (r,z.val)).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((uncutTest f phi r : BoundedContinuousFunction SourceCoordinateSlice Fiber).norm_coe_le_norm z.val) (norm_nonneg v)))

theorem uncutOperator_core (f : Field289) (phi : Localizer) (r : ℝ) (a : QuantumTest) :
    uncutOperator f phi r (embed a)=embed (localMultiplier (fun z=>compactFiber f phi (r,z))
      (fun _=>(uncutTest f phi r).contDiff.contDiffAt) a) :=GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a

def uncutSlope (f : Field289) (phi : Localizer) : H →L[ℂ] H :=uncutOperator f phi 1-uncutOperator f phi 0

theorem uncutOperator_affine (f : Field289) (phi : Localizer) (r : ℝ) :
    uncutOperator f phi r=uncutOperator f phi 0+r • uncutSlope f phi :=by
  apply GaussYukawaGrade.core_ext;intro a
  simp only [uncutSlope,add_apply,sub_apply,smul_apply,uncutOperator_core]
  have linear (a b : QuantumTest) : embed (a+r • b)=embed a+r • embed b :=by
    exact (embed.restrictScalars ℝ).map_add a (r • b) |>.trans
      (congrArg (fun v=>embed a+v) ((embed.restrictScalars ℝ).map_smul r b))
  rw [←map_sub,←linear]
  apply congrArg embed;apply DFunLike.ext;intro z
  change ((phi z:ℂ) • uncutFiber f r z) (a z)=
    ((phi z:ℂ) • uncutFiber f 0 z) (a z)+r •
      (((phi z:ℂ) • uncutFiber f 1 z) (a z)-((phi z:ℂ) • uncutFiber f 0 z) (a z))
  rw [uncutFiber_affine f r z,uncutFiber_affine f 1 z]
  simp only [one_smul,smul_add,add_apply,smul_apply,add_sub_cancel_left,smul_comm (phi z:ℂ) r]

theorem uncutOperator_derivative (f : Field289) (phi : Localizer) (r : ℝ) :
    HasDerivAt (uncutOperator f phi) (uncutSlope f phi) r :=by
  have h:=(hasDerivAt_id r).smul_const (uncutSlope f phi)
  have generated:=h.const_add (uncutOperator f phi 0)
  simpa only [id_eq,one_smul] using generated.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s=>uncutOperator_affine f phi s))

/-- The original reciprocal-radius graph, pulled back along the same source curve. -/
def movedReciprocal (f : Field289) (r : ℝ) (z : SourceCoordinateSlice) : Fiber :=
  inverseFiber (fieldCoordinateCurve f r z)

theorem movedReciprocal_smooth (f : Field289) (r : ℝ) (z : physicalChart) :
    ContDiffAt ℝ ∞ (movedReciprocal f r) z.val :=inverse_smooth.contDiffAt.comp z.val
      ((field_curve_smooth f r z).comp z.val (contDiff_const.prodMk contDiff_id).contDiffAt)

def movedInverse (f : Field289) (r : ℝ) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (movedReciprocal f r) (movedReciprocal_smooth f r)
    (fun z w=>inverse_commutes (fieldCoordinateCurve f r z.val) w) 1 zero_le_one
    (fun z v=>inverse_bound (fieldCoordinateCurve f r z.val) v)

def movedRadiusAction (f : Field289) (r : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussNativeForm.multiply (fun z=>radius (fieldCoordinateCurve f r z)) (fun z=>radius_smooth.contDiffAt.comp z.val
    ((field_curve_smooth f r z).comp z.val (contDiff_const.prodMk contDiff_id).contDiffAt))

theorem movedInverse_core (f : Field289) (r : ℝ) (a : QuantumTest) :
    movedInverse f r (embed a)=embed (localMultiplier (movedReciprocal f r) (movedReciprocal_smooth f r) a) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ a

theorem movedInverse_radius (f : Field289) (r : ℝ) (a : QuantumTest) :
    movedInverse f r (embed (movedRadiusAction f r a))=embed a :=by
  rw [movedInverse_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change (reciprocal (fieldCoordinateCurve f r z):ℂ) • ((radius (fieldCoordinateCurve f r z):ℂ) • a z)=a z
  rw [smul_smul,reciprocal,Complex.ofReal_inv,inv_mul_cancel₀ (by exact_mod_cast (radius_pos (fieldCoordinateCurve f r z)).ne'),one_smul]

theorem movedInverse_dense (f : Field289) (r : ℝ) : DenseRange (movedInverse f r) :=by
  apply GaussHistoryHilbert.fockTestDomain_dense.mono
  intro x hx
  obtain ⟨a,ha⟩:=embed_surjective_core ⟨x,hx⟩
  exact ⟨embed (movedRadiusAction f r a),(movedInverse_radius f r a).trans ha⟩

theorem movedInverse_pair (f : Field289) (r : ℝ) (x y : H) :
    inner ℂ (movedInverse f r x) y=inner ℂ x (movedInverse f r y) :=by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨a,rfl⟩:=coreEquiv.surjective a
  obtain ⟨b,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (movedInverse f r (embed a)) (embed b)=inner ℂ (embed a) (movedInverse f r (embed b))
  rw [movedInverse_core,movedInverse_core]
  exact (GaussNativeForm.multiply_pair (fun z=>reciprocal (fieldCoordinateCurve f r z))
    (fun z=>reciprocal_smooth.contDiffAt.comp z.val
      ((field_curve_smooth f r z).comp z.val (contDiff_const.prodMk contDiff_id).contDiffAt)) a b).symm

theorem movedInverse_injective (f : Field289) (r : ℝ) : Function.Injective (movedInverse f r) :=by
  suffices zero : ∀x : H,movedInverse f r x=0 → x=0 by
    intro x y h;apply sub_eq_zero.mp;apply zero;rw [map_sub,h,sub_self]
  intro x hx
  have eq : inner ℂ x x=0 :=(movedInverse_dense f r).induction_on (p:=fun y=>inner ℂ x y=0) x
    (isClosed_eq (continuous_const.inner continuous_id) continuous_const) (fun y=>by
      rw [←movedInverse_pair f r x y,hx,inner_zero_left])
  exact (inner_self_eq_zero (𝕜:=ℂ)).mp eq

def movedGraph (f : Field289) (r : ℝ) : Submodule ℂ (H×H) where
  carrier:={xy | fieldCutoff f 0 r xy.1=movedInverse f r xy.2}
  zero_mem':=by simp
  add_mem':=by intro x y hx hy;change fieldCutoff f 0 r (x.1+y.1)=movedInverse f r (x.2+y.2);rw [map_add,map_add,hx,hy]
  smul_mem':=by intro c x hx;change fieldCutoff f 0 r (c • x.1)=movedInverse f r (c • x.2);rw [map_smul,map_smul,hx]

theorem movedGraph_closed (f : Field289) (r : ℝ) : IsClosed (movedGraph f r:Set (H×H)) :=
  isClosed_eq ((fieldCutoff f 0 r).continuous.comp continuous_fst) ((movedInverse f r).continuous.comp continuous_snd)

theorem movedGraph_zero (f : Field289) (r : ℝ) (xy : H×H) (h : xy∈movedGraph f r) (zero : xy.1=0) : xy.2=0 :=by
  apply movedInverse_injective f r
  change fieldCutoff f 0 r xy.1=movedInverse f r xy.2 at h
  rw [zero,map_zero] at h
  rw [map_zero]
  exact h.symm

def movedClosedY (f : Field289) (r : ℝ) : H →ₗ.[ℂ] H :=(movedGraph f r).toLinearPMap

theorem movedClosedY_graph (f : Field289) (r : ℝ) : (movedClosedY f r).graph=movedGraph f r :=
  (movedGraph f r).toLinearPMap_graph_eq (movedGraph_zero f r)

theorem movedInverse_zero (f : Field289) : movedInverse f 0=inverseRadius :=by
  apply GaussYukawaGrade.core_ext;intro a
  rw [movedInverse_core,inverse_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change inverseFiber (fieldCoordinateCurve f 0 z) (a z)=(reciprocal z:ℂ) • a z
  rw [curve_zero];rfl

theorem movedGraph_source (f : Field289) : movedGraph f 0=GaussRadialDomain.graph :=by
  ext xy
  change fieldCutoff f 0 0 xy.1=movedInverse f 0 xy.2 ↔ bounded xy.1=inverseRadius xy.2
  rw [fieldCutoff_zero,movedInverse_zero]
  rfl

theorem movedClosedY_source (f : Field289) : movedClosedY f 0=closedY :=
  congrArg Submodule.toLinearPMap (movedGraph_source f)

theorem moved_original_core (f : Field289) (r : ℝ) (a : QuantumTest) :
    (embed a,embed (uncutAction f r a))∈movedGraph f r :=by
  change fieldCutoff f 0 r (embed a)=movedInverse f r (embed (uncutAction f r a))
  rw [fieldCutoff_core,movedInverse_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change sourceMap ((radius (fieldCoordinateCurve f r z))⁻¹ • scalarField (fieldCoordinateCurve f r z)) (a z)=
    (reciprocal (fieldCoordinateCurve f r z):ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (a z)
  rw [map_smul,smul_apply]
  rfl

theorem movedClosedY_dense (f : Field289) (r : ℝ) : Dense ((movedClosedY f r).domain:Set H) :=by
  apply GaussHistoryHilbert.fockTestDomain_dense.mono
  intro x hx
  obtain ⟨a,ha⟩:=embed_surjective_core ⟨x,hx⟩
  exact Submodule.mem_map.mpr ⟨(embed a,embed (uncutAction f r a)),moved_original_core f r a,ha⟩

open CanonicalGradedSpatialSource

theorem uncutOperator_graph_identity (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    movedInverse f r*uncutOperator f (finiteRetainer p F) r=fieldCutoff f 0 r*retainer p F :=by
  apply GaussYukawaGrade.core_ext;intro a
  change movedInverse f r (uncutOperator f (finiteRetainer p F) r (embed a))=
    fieldCutoff f 0 r (retainer p F (embed a))
  rw [uncutOperator_core,movedInverse_core,retainer_core,fieldCutoff_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change (reciprocal (fieldCoordinateCurve f r z):ℂ) •
    ((finiteRetainer p F z:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (a z))=
    sourceMap ((radius (fieldCoordinateCurve f r z))⁻¹ • scalarField (fieldCoordinateCurve f r z))
      ((finiteRetainer p F z:ℂ) • a z)
  rw [map_smul,sourceMap.map_smul,smul_apply]
  exact smul_comm _ _ _

theorem uncutOperator_domain (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ)
    (x : H) (hx : x∈retainedSpace p F) :
    ∃h : x∈(movedClosedY f r).domain,(movedClosedY f r) ⟨x,h⟩=uncutOperator f (finiteRetainer p F) r x :=by
  have eq:=congrArg (fun A : H →L[ℂ] H=>A x) (uncutOperator_graph_identity f p F r)
  change movedInverse f r (uncutOperator f (finiteRetainer p F) r x)=fieldCutoff f 0 r (retainer p F x) at eq
  rw [(retainedSpace_iff p F x).mp hx] at eq
  have graph : (x,uncutOperator f (finiteRetainer p F) r x)∈(movedClosedY f r).graph :=by
    rw [movedClosedY_graph];exact eq.symm
  obtain ⟨u,hu,hvalue⟩:=(movedClosedY f r).mem_graph_iff.mp graph
  change (u:H)=x at hu
  refine ⟨hu ▸ u.property,?_⟩
  exact (congrArg (fun v : (movedClosedY f r).domain=>(movedClosedY f r) v) (Subtype.ext hu.symm)).trans hvalue

theorem uncutOperator_retainer (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ) :
    Commute (retainer p F) (uncutOperator f (finiteRetainer p F) r) :=by
  apply GaussYukawaGrade.core_ext;intro a
  change retainer p F (uncutOperator f (finiteRetainer p F) r (embed a))=
    uncutOperator f (finiteRetainer p F) r (retainer p F (embed a))
  rw [uncutOperator_core,retainer_core,retainer_core,uncutOperator_core]
  apply congrArg embed;apply DFunLike.ext;intro z
  change (finiteRetainer p F z:ℂ) • ((compactFiber f (finiteRetainer p F) (r,z)) (a z))=
    (compactFiber f (finiteRetainer p F) (r,z)) ((finiteRetainer p F z:ℂ) • a z)
  exact (map_smul _ _ _).symm

theorem uncutOperator_retained (f : Field289) (p : PhysicalMomentum) (F : Index) (r : ℝ)
    (x : H) (hx : x∈retainedSpace p F) : uncutOperator f (finiteRetainer p F) r x∈retainedSpace p F :=by
  apply (retainedSpace_iff p F _).mpr
  have eq:=congrArg (fun A : H →L[ℂ] H=>A x) (uncutOperator_retainer f p F r).eq
  change retainer p F (uncutOperator f (finiteRetainer p F) r x)=uncutOperator f (finiteRetainer p F) r (retainer p F x) at eq
  rwa [(retainedSpace_iff p F x).mp hx] at eq

theorem uncutOperator_raises (f : Field289) (phi : Localizer) (r : ℝ) :
    GaussYukawaGrade.grade*uncutOperator f phi r=uncutOperator f phi r*GaussYukawaGrade.grade+uncutOperator f phi r :=by
  apply GaussYukawaGrade.core_ext;intro a
  change GaussYukawaGrade.grade (uncutOperator f phi r (embed a))=
    uncutOperator f phi r (GaussYukawaGrade.grade (embed a))+uncutOperator f phi r (embed a)
  rw [uncutOperator_core,GaussYukawaGrade.grade_core,GaussYukawaGrade.grade_core,uncutOperator_core,←map_add]
  apply congrArg embed;apply DFunLike.ext;intro z
  change GaussYukawaGrade.fiberGrade ((phi z:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (a z))=
    (phi z:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (GaussYukawaGrade.fiberGrade (a z))+
    (phi z:ℂ) • sourceMap (scalarField (fieldCoordinateCurve f r z)) (a z)
  rw [map_smul,GaussYukawaGrade.fiber_source_grade,smul_add]

open PreparationVacuumSourcePreparedResponse GaussComposite GaussComposite.SourceGraph

theorem preparedLeg_domain (epsilon : ℝ) (precision : 0<epsilon) (f : Field289)
    (p : PhysicalMomentum) (F : Index) (r : ℝ) (addition : Bool) (a s : Fin 2) :
    ∃h : completedLeg addition a s (sourceProfile epsilon precision)∈(movedClosedY f r).domain,
      (movedClosedY f r) ⟨completedLeg addition a s (sourceProfile epsilon precision),h⟩=
        uncutOperator f (finiteRetainer p F) r (completedLeg addition a s (sourceProfile epsilon precision)) :=
  uncutOperator_domain f p F r _ (profileLeg_retained epsilon precision p F addition a s)

end LowEnergy.PreparationVacuumUncutYukawa
