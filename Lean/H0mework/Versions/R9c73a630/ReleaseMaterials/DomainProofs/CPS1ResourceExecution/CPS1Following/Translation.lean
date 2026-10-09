import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Continuous
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.LAlanineMolecularControl.Scratch.LAlanineSpatialControl.TranslationDifferentiability

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

abbrev Point := CPS1ElectronicSource.Point
abbrev SpatialLp := CPS1ElectronicSource.SpatialLp
abbrev SpinSpace := CPS1ElectronicSource.SpinSpace

open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis.SpatialControl

def spatialTranslate (centre : Point) : SpatialLp →ₗᵢ[ℂ] SpatialLp :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Point => x-centre) (sub_preserving centre)

theorem spatial_translate_zero (field : SpatialLp) : spatialTranslate 0 field = field := by
  change Lp.compMeasurePreserving (fun x : Point => x-0) (sub_preserving 0) field = field
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving field (sub_preserving (0 : Point))] with x source
  simpa only [Function.comp_def,sub_zero] using source

theorem spatial_translate_add (first second : Point) (field : SpatialLp) :
    spatialTranslate first (spatialTranslate second field) = spatialTranslate (first+second) field := by
  change Lp.compMeasurePreserving (fun x : Point => x-first) _
    (Lp.compMeasurePreserving (fun x : Point => x-second) _ field) =
    Lp.compMeasurePreserving (fun x : Point => x-(first+second)) (sub_preserving (first+second)) field
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving field
      ((sub_preserving second).comp (sub_preserving first)),
    Lp.coeFn_compMeasurePreserving field (sub_preserving (first+second))] with x firstSource secondSource
  rw [firstSource,secondSource]
  change field ((x-first)-second) = field (x-(first+second))
  congr 1
  abel

def spatialTranslation (centre : Point) : SpatialLp ≃ₗᵢ[ℂ] SpatialLp :=
  LinearIsometryEquiv.ofSurjective (spatialTranslate centre) (by
    intro field
    refine ⟨spatialTranslate (-centre) field,?_⟩
    rw [spatial_translate_add,add_neg_cancel,spatial_translate_zero])

def translate (centre : Point) : SpinSpace ≃ₗᵢ[ℂ] SpinSpace :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool => spatialTranslation centre)

theorem translate_apply (centre : Point) (field : SpinSpace) (spin : Bool) :
    translate centre field spin = spatialTranslate centre (field spin) := rfl

theorem translate_zero (field : SpinSpace) : translate 0 field = field := by
  ext1 spin
  exact spatial_translate_zero (field spin)

theorem translate_add (first second : Point) (field : SpinSpace) :
    translate first (translate second field) = translate (first+second) field := by
  ext1 spin
  exact spatial_translate_add first second (field spin)

theorem translate_inverse (centre : Point) (field : SpinSpace) :
    translate (-centre) (translate centre field) = field := by
  rw [translate_add,neg_add_cancel,translate_zero]

theorem translate_norm (centre : Point) (field : SpinSpace) :
    ‖translate centre field‖ = ‖field‖ := (translate centre).norm_map field

theorem translate_inner (centre : Point) (first second : SpinSpace) :
    inner ℂ (translate centre first) (translate centre second) = inner ℂ first second :=
  (translate centre).inner_map_map first second

theorem translate_orthonormal {index : Type*} (centre : Point) (fields : index → SpinSpace)
    (orthogonal : Orthonormal ℂ fields) :
    Orthonormal ℂ (fun i => translate centre (fields i)) :=
  (translate centre).toLinearIsometry.orthonormal_comp_iff.mpr orthogonal

theorem translate_fields {n m : Type*} [Fintype n] (centre : Point)
    (basis : n → SpinSpace) (occupied : Matrix n m ℂ) (slot : m) :
    CPS1ElectronicEvolution.fields (fun i => translate centre (basis i)) occupied slot =
      translate centre (CPS1ElectronicEvolution.fields basis occupied slot) := by
  simp only [CPS1ElectronicEvolution.fields,map_sum,map_smul]

theorem translate_gram {index : Type*} (centre : Point) (fields : index → SpinSpace)
    (first second : index) :
    inner ℂ (translate centre (fields first)) (translate centre (fields second)) =
      inner ℂ (fields first) (fields second) := translate_inner centre _ _

theorem translate_slater {electrons : Nat} (centre : Point) (fields : Fin electrons → SpinSpace) :
    CPS1ElectronicEvolution.slaterDual (fun slot => translate centre (fields slot))
      (CPS1ElectronicEvolution.slater (fun slot => translate centre (fields slot))) =
      CPS1ElectronicEvolution.slaterDual fields (CPS1ElectronicEvolution.slater fields) := by
  simp only [CPS1ElectronicEvolution.slaterDual,CPS1ElectronicEvolution.slater,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  apply congrArg Matrix.det
  ext i j
  change inner ℂ (translate centre (fields j)) (translate centre (fields i)) =
    inner ℂ (fields j) (fields i)
  exact translate_inner centre _ _

variable {frame : CPS1Recycling.Frame}

def movingBasis (state : CPS1ElectronicSource.State frame) (centre : Point)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) : SpinSpace :=
  translate centre (CPS1ElectronicSource.basis state.geometry mode)

def movingFields (state : CPS1ElectronicSource.State frame) (centre : Point)
    (slot : CPS1ElectronicSource.ElectronIndex state.geometry) : SpinSpace :=
  translate centre (CPS1ElectronicEvolution.fields (CPS1ElectronicSource.basis state.geometry) state.occupied slot)

theorem moving_basis_orthonormal (state : CPS1ElectronicSource.State frame) (centre : Point) :
    Orthonormal ℂ (movingBasis state centre) :=
  translate_orthonormal centre _ (CPS1ElectronicEvolution.Source.basis_orthonormal state.geometry)

theorem moving_fields_gram (state : CPS1ElectronicSource.State frame) (centre : Point)
    (first second : CPS1ElectronicSource.ElectronIndex state.geometry) :
    inner ℂ (movingFields state centre first) (movingFields state centre second) =
      (state.occupied.conjTranspose * state.occupied) first second := by
  rw [movingFields,movingFields,translate_inner]
  exact CPS1ElectronicEvolution.field_gram _ (CPS1ElectronicEvolution.Source.basis_orthonormal state.geometry) _ _ _


open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel

def realEmbedding : RealField →L[ℝ] SpatialLp := Complex.ofRealCLM.compLpL 2 volume

theorem real_embedding_primitive (centre : Point) (mode : Nat) (jet : Fin 3 → Nat) :
    realEmbedding (shiftedField [CPS1ElectronicSource.primitive mode]
      (CPS1ElectronicSource.primitive_positive mode) jet centre) =
      CPS1ElectronicSource.orbitalField centre mode jet := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM
      (shiftedField [CPS1ElectronicSource.primitive mode] (CPS1ElectronicSource.primitive_positive mode) jet centre),
    (shifted_memLp [CPS1ElectronicSource.primitive mode] (CPS1ElectronicSource.primitive_positive mode) jet centre).coeFn_toLp,
    CPS1ElectronicSource.orbital_field_source centre mode jet] with x embedded source target
  change (shiftedField [CPS1ElectronicSource.primitive mode]
    (CPS1ElectronicSource.primitive_positive mode) jet centre) x =
    orbital [CPS1ElectronicSource.primitive mode] jet (x-centre) at source
  rw [source] at embedded
  exact embedded.trans target.symm

theorem primitive_curve_derivative (mode : Nat) (jet : Fin 3 → Nat) (centre : ℝ → Point)
    (velocity : Point) (time : ℝ) (motion : HasDerivAt centre velocity time) :
    HasDerivAt (fun t => CPS1ElectronicSource.orbitalField (centre t) mode jet)
      (-(∑ axis : Fin 3, velocity axis • CPS1ElectronicSource.orbitalField (centre time) mode (raise jet axis))) time := by
  have paid := realEmbedding.hasFDerivAt.comp_hasDerivAt time
    (shifted_field_curve_derivative [CPS1ElectronicSource.primitive mode]
      (CPS1ElectronicSource.primitive_positive mode) jet centre velocity time motion)
  simpa only [Function.comp_def,real_embedding_primitive,map_neg,map_sum,map_smul] using paid

theorem spatial_zero_synthesis (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) :
    CPS1ElectronicSource.spatialField 0 n mode jet =
      ∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
        CPS1ElectronicSource.orbitalField 0 primitive.val jet := by
  apply Lp.ext
  have each (primitive : Fin n) :
      (fun x : Point => (CPS1ElectronicSource.coefficients 0 n primitive mode •
        CPS1ElectronicSource.orbitalField 0 primitive.val jet) x) =ᵐ[volume]
        fun x => CPS1ElectronicSource.coefficients 0 n primitive mode *
          CPS1ElectronicSource.orbitalValue 0 primitive.val jet x := by
    filter_upwards [Lp.coeFn_smul (CPS1ElectronicSource.coefficients 0 n primitive mode)
        (CPS1ElectronicSource.orbitalField 0 primitive.val jet),
      CPS1ElectronicSource.orbital_field_source 0 primitive.val jet] with x scalar source
    simpa only [Pi.smul_apply,smul_eq_mul,source] using scalar
  filter_upwards [(CPS1ElectronicSource.spatial_memLp 0 n mode jet).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun primitive : Fin n =>
      CPS1ElectronicSource.coefficients 0 n primitive mode • CPS1ElectronicSource.orbitalField 0 primitive.val jet),
    Filter.eventually_all.mpr each] with x source summed scalar
  exact source.trans (summed.trans (Finset.sum_congr rfl (fun primitive _ => scalar primitive))).symm

theorem spatial_translate_primitive (centre origin : Point) (mode : Nat) (jet : Fin 3 → Nat) :
    spatialTranslate centre (CPS1ElectronicSource.orbitalField origin mode jet) =
      CPS1ElectronicSource.orbitalField (centre+origin) mode jet := by
  change Lp.compMeasurePreserving (fun x : Point => x-centre) (sub_preserving centre)
    ((CPS1ElectronicSource.orbital_memLp origin mode jet).toLp _) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun x => by
    change CPS1ElectronicSource.orbitalValue origin mode jet (x-centre) =
      CPS1ElectronicSource.orbitalValue (centre+origin) mode jet x
    unfold CPS1ElectronicSource.orbitalValue
    congr 1
    abel

def movingSpatial (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) : SpatialLp :=
  spatialTranslate centre (CPS1ElectronicSource.spatialField 0 n mode jet)

theorem moving_spatial_synthesis (centre : Point) (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat) :
    movingSpatial centre n mode jet =
      ∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
        CPS1ElectronicSource.orbitalField centre primitive.val jet := by
  simp only [movingSpatial,spatial_zero_synthesis,map_sum,map_smul,spatial_translate_primitive,add_zero]

theorem moving_spatial_curve (n : Nat) (mode : Fin n) (jet : Fin 3 → Nat)
    (centre : ℝ → Point) (velocity : Point) (time : ℝ) (motion : HasDerivAt centre velocity time) :
    HasDerivAt (fun t => movingSpatial (centre t) n mode jet)
      (-(∑ axis : Fin 3, velocity axis • movingSpatial (centre time) n mode (raise jet axis))) time := by
  have paid : HasDerivAt (fun t => ∑ primitive : Fin n,
      CPS1ElectronicSource.coefficients 0 n primitive mode •
        CPS1ElectronicSource.orbitalField (centre t) primitive.val jet)
      (∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
        (-(∑ axis : Fin 3, velocity axis •
          CPS1ElectronicSource.orbitalField (centre time) primitive.val (raise jet axis)))) time := by
    have source := HasDerivAt.sum (u := Finset.univ) (fun primitive (_ : primitive ∈ Finset.univ) =>
      (primitive_curve_derivative primitive.val jet centre velocity time motion).const_smul
        (CPS1ElectronicSource.coefficients 0 n primitive mode))
    have functions : (∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
        fun t => CPS1ElectronicSource.orbitalField (centre t) primitive.val jet) =
        fun t => ∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
          CPS1ElectronicSource.orbitalField (centre t) primitive.val jet := by
      funext t
      simp only [Finset.sum_apply,Pi.smul_apply]
    rw [functions] at source
    exact source
  have sameRate : (-(∑ axis : Fin 3, velocity axis • movingSpatial (centre time) n mode (raise jet axis))) =
      ∑ primitive : Fin n, CPS1ElectronicSource.coefficients 0 n primitive mode •
        (-(∑ axis : Fin 3, velocity axis •
          CPS1ElectronicSource.orbitalField (centre time) primitive.val (raise jet axis))) := by
    simp only [moving_spatial_synthesis,smul_neg,Finset.sum_neg_distrib,Finset.smul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro primitive _
    apply Finset.sum_congr rfl
    intro axis _
    exact smul_comm _ _ _
  rw [sameRate]
  simpa only [moving_spatial_synthesis] using paid

def spinInjection (spin : Bool) : SpatialLp →L[ℝ] SpinSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Bool => SpatialLp)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Bool => SpatialLp) spin)

theorem spin_injection_apply (spin : Bool) (field : SpatialLp) :
    spinInjection spin field = PiLp.single 2 spin field := rfl

def basisJet (state : CPS1ElectronicSource.State frame) (jet : Fin 3 → Nat)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) : SpinSpace :=
  PiLp.single 2 mode.2 (CPS1ElectronicSource.spatialField 0
    (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) mode.1 jet)

def basisRate (state : CPS1ElectronicSource.State frame) (centre velocity : Point)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) : SpinSpace :=
  -(∑ axis : Fin 3, velocity axis • translate centre (basisJet state (raise 0 axis) mode))

theorem moving_basis_source (state : CPS1ElectronicSource.State frame) (centre : Point)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) :
    movingBasis state centre mode = spinInjection mode.2 (movingSpatial centre
      (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) mode.1 0) := by
  change translate centre (PiLp.single 2 mode.2 (CPS1ElectronicSource.normalizedField 0 _ mode.1)) = _
  rw [translate,LinearIsometryEquiv.piLpCongrRight_single]
  rw [spin_injection_apply,← CPS1ElectronicSource.spatial_field_normalized]
  rfl

theorem translate_basis_jet (state : CPS1ElectronicSource.State frame) (centre : Point)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) (jet : Fin 3 → Nat) :
    translate centre (basisJet state jet mode) = spinInjection mode.2 (movingSpatial centre
      (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) mode.1 jet) := by
  change translate centre (PiLp.single 2 mode.2 _) = _
  rw [translate,LinearIsometryEquiv.piLpCongrRight_single]
  rfl

theorem moving_basis_curve (state : CPS1ElectronicSource.State frame)
    (centre : ℝ → Point) (velocity : Point) (time : ℝ) (motion : HasDerivAt centre velocity time)
    (mode : CPS1ElectronicSource.SpinIndex state.geometry) :
    HasDerivAt (fun t => movingBasis state (centre t) mode) (basisRate state (centre time) velocity mode) time := by
  have paid := (spinInjection mode.2).hasFDerivAt.comp_hasDerivAt time
    (moving_spatial_curve (CPS1ElectronicSource.spatialModes frame state.geometry.originJoint) mode.1 0
      centre velocity time motion)
  simpa only [Function.comp_def,moving_basis_source,basisRate,translate_basis_jet,map_neg,map_sum,map_smul] using paid

theorem translate_slater_map {electrons : Nat} (centre : Point) (fields : Fin electrons → SpinSpace) :
    exteriorPower.map electrons (translate centre).toLinearEquiv.toLinearMap
      (CPS1ElectronicEvolution.slater fields) =
      CPS1ElectronicEvolution.slater (fun slot => translate centre (fields slot)) :=
  exteriorPower.map_apply_ιMulti _ _

end
end CPS1Following
