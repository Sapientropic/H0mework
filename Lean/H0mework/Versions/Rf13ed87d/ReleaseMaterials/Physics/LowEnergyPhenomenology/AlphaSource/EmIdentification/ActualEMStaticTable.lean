import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMStaticCurrent
open LowEnergy LowEnergy.PreparationVacuumOriginalGreenFeedback
open PreparationVacuumMixedPrincipal PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticPoleResponse
open PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalPoleSheet PreparationVacuumMixedControl
set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCarrierOwn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumWholeOrigin
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource Stage10
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] emInsertion
namespace StaticTable

def readerTerms : List SourceTerm := [
 ⟨0,15,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,⟨0,16,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,⟨0,20,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
 ⟨1,27,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,⟨1,28,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,⟨1,32,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
 ⟨2,39,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,⟨2,40,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,⟨2,44,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,
 ⟨3,51,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩,⟨3,52,⟨0,0,0,0⟩,⟨⟨1/2,0⟩,⟨0,0⟩⟩⟩,⟨3,56,⟨0,0,0,0⟩,⟨⟨-1/2,0⟩,⟨0,0⟩⟩⟩]
def transposeTerms (ts : List SourceTerm) : List SourceTerm := ts.map fun t=>⟨t.column,t.row,t.powers,t.coefficient⟩
def change0 := fastNormalizeTerms (productTerms readerTerms (originTerms originalChangeTerms))
def change1 := fastNormalizeTerms (productTerms readerTerms (degreeTerms (positiveTerms originalChangeTerms) 1))
def response := fastNormalizeTerms (productTerms change0 fullInverseTerms)
def force := fastNormalizeTerms (productTerms (degreeTerms (positiveTerms activeTerms) 1) fullKernelTerms)
def jet := fastNormalizeTerms (productTerms change1 fullKernelTerms ++ negativeTerms (productTerms response force))
def contact := fastNormalizeTerms (productTerms (productTerms change0 (originTerms contactInverseTerms)) (transposeTerms change0))
def regular := fastNormalizeTerms (contact ++ productTerms (columnTerms activeFlag response) (transposeTerms change0))
def directional := fastNormalizeTerms (productTerms (productTerms jet staticInverseTerms) (transposeTerms jet))


def jetTerms : List SourceTerm := [
 ⟨0,0,⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,1,⟨1,0,0,0⟩,⟨⟨(-8/11:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨3,0,⟨1,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(5/72:ℚ)⟩⟩⟩,
 ⟨1,1,⟨0,1,0,0⟩,⟨⟨(-49/67:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨1,0,⟨0,1,0,0⟩,⟨⟨(-1/4:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨2,0,⟨0,0,1,0⟩,⟨⟨(-1/4:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨2,1,⟨0,0,1,0⟩,⟨⟨(-49/67:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,0,⟨0,0,0,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-5/72:ℚ)⟩⟩⟩,
 ⟨3,1,⟨0,0,0,1⟩,⟨⟨(-46/67:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨3,0,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩]

def regularTerms : List SourceTerm := [
 ⟨0,0,⟨0,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-36823/448800:ℚ)⟩⟩⟩,
 ⟨3,3,⟨0,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(1699/96480:ℚ)⟩⟩⟩,
 ⟨1,1,⟨0,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-20357/328032:ℚ)⟩⟩⟩,
 ⟨2,2,⟨0,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-20357/328032:ℚ)⟩⟩⟩]

def directionalTerms : List SourceTerm := [
 ⟨2,2,⟨0,0,2,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-605677/1206000:ℚ)⟩⟩⟩,
 ⟨1,1,⟨0,2,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-605677/1206000:ℚ)⟩⟩⟩,
 ⟨1,3,⟨1,1,0,0⟩,⟨⟨(3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨1,0,⟨1,1,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-49891/99000:ℚ)⟩⟩⟩,
 ⟨3,1,⟨1,1,0,0⟩,⟨⟨(3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨3,3,⟨2,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-1/96:ℚ)⟩⟩⟩,
 ⟨3,0,⟨2,0,0,0⟩,⟨⟨(3/40:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,1,⟨1,1,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-49891/99000:ℚ)⟩⟩⟩,
 ⟨0,0,⟨2,0,0,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-277801/544500:ℚ)⟩⟩⟩,
 ⟨0,3,⟨2,0,0,0⟩,⟨⟨(3/40:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨2,1,⟨0,1,1,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-605677/1206000:ℚ)⟩⟩⟩,
 ⟨2,0,⟨1,0,1,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-49891/99000:ℚ)⟩⟩⟩,
 ⟨2,3,⟨1,0,1,0⟩,⟨⟨(3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨1,2,⟨0,1,1,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-605677/1206000:ℚ)⟩⟩⟩,
 ⟨3,2,⟨1,0,1,0⟩,⟨⟨(3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,2,⟨1,0,1,0⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-49891/99000:ℚ)⟩⟩⟩,
 ⟨3,3,⟨0,0,0,2⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-137677/301500:ℚ)⟩⟩⟩,
 ⟨3,0,⟨0,0,0,2⟩,⟨⟨(-3/40:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,3,⟨0,0,0,2⟩,⟨⟨(-3/40:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,0,⟨0,0,0,2⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-1/96:ℚ)⟩⟩⟩,
 ⟨3,1,⟨0,1,0,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-287177/603000:ℚ)⟩⟩⟩,
 ⟨3,3,⟨1,0,0,1⟩,⟨⟨(3/20:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨3,0,⟨1,0,0,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-187003/396000:ℚ)⟩⟩⟩,
 ⟨0,1,⟨0,1,0,1⟩,⟨⟨(-3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨0,3,⟨1,0,0,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-187003/396000:ℚ)⟩⟩⟩,
 ⟨0,0,⟨1,0,0,1⟩,⟨⟨(-3/20:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨1,3,⟨0,1,0,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-287177/603000:ℚ)⟩⟩⟩,
 ⟨1,0,⟨0,1,0,1⟩,⟨⟨(-3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨3,2,⟨0,0,1,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-287177/603000:ℚ)⟩⟩⟩,
 ⟨0,2,⟨0,0,1,1⟩,⟨⟨(-3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩,
 ⟨2,3,⟨0,0,1,1⟩,⟨⟨(0:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(-287177/603000:ℚ)⟩⟩⟩,
 ⟨2,0,⟨0,0,1,1⟩,⟨⟨(-3/80:ℚ),(0:ℚ)⟩,⟨(0:ℚ),(0:ℚ)⟩⟩⟩]

set_option maxHeartbeats 2400000 in
private theorem jet_certificate : jet=jetTerms := by decide +kernel
set_option maxHeartbeats 2400000 in
private theorem regular_certificate : regular=regularTerms := by decide +kernel
set_option maxHeartbeats 2400000 in
private theorem contact_certificate : contact=[] := by decide +kernel
private theorem directional_certificate :
    fastNormalizeTerms (productTerms (productTerms jetTerms staticInverseTerms) (transposeTerms jetTerms))=directionalTerms := by
  decide +kernel

private theorem transpose_value (ts : List SourceTerm) (v : Fin 4→ℂ) :
    sourceMatrix (transposeTerms ts) v=(sourceMatrix ts v).transpose := by
  induction ts with
  | nil=>rfl
  | cons t ts ih=>
    simp only [transposeTerms,List.map_cons,sourceMatrix_cons,Matrix.transpose_add] at ih ⊢
    rw [ih]
    simp only [SourceTerm.matrix,Matrix.transpose_single]

private theorem origin_value (ts : List SourceTerm) (v : Fin 4→ℂ) :
    sourceMatrix (originTerms ts) v=sourceMatrix ts 0 := by
  calc
    _=sourceMatrix (originTerms ts) 0 := by
      simpa only [degreeTensor,degreeTerms,originTerms,zero_smul,pow_zero,one_smul] using
        (degreeTensor_scaled ts 0 (0:ℂ) v).symm
    _=sourceMatrix ts 0 := originTerms_generated ts

private def index (mu : Fin 4) : Fin 289 := ⟨mu.val,by omega⟩
private def reader : Matrix (Fin 289) (Fin 289) ℂ := sourceMatrix readerTerms 0

private theorem reader_constant (v : Fin 4→ℂ) : sourceMatrix readerTerms v=reader := by
  norm_num [reader,readerTerms,sourceMatrix,SourceTerm.matrix,Powers.value]

set_option maxHeartbeats 2400000 in
private theorem reader_entry (mu : Fin 4) (j : Fin 289) : reader (index mu) j=emInsertion j mu := by
  have projected:=em_projection_coordinates (Pi.single j (1:ℂ)) mu
  rw [Matrix.mulVec_single_one] at projected
  change emInsertion j mu=_ at projected
  rw [projected]
  fin_cases mu <;> norm_num [reader,readerTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    index,gaugeSlot,coefficientValue,Powers.value,Pi.single_apply,eq_comm,Fin.ext_iff]
  all_goals split_ifs <;> ring

private theorem reader_mul (M : Matrix (Fin 289) (Fin 289) ℂ) (mu : Fin 4) (j : Fin 289) :
    (reader*M) (index mu) j=(emInsertion.transpose*M) mu j := by
  simp only [Matrix.mul_apply,reader_entry,Matrix.transpose_apply]

private theorem reader_pair (M : Matrix (Fin 289) (Fin 289) ℂ) (mu nu : Fin 4) :
    (reader*M*reader.transpose) (index mu) (index nu)=(emInsertion.transpose*M*emInsertion) mu nu := by
  simp only [Matrix.mul_apply,reader_entry,Matrix.transpose_apply]

private theorem change0_value (v : Fin 4→ℂ) : sourceMatrix change0 v=reader*originalChange 0 := by
  simp only [change0,fastNormalizeTerms_value,productTerms_value,origin_value,reader_constant,originalChange]

private theorem jet_value (v : Fin 4→ℂ) : sourceMatrix jetTerms v=
    reader*(sourceLinearPart originalChangeTerms v*fullKernelFrame-
      originalChange 0*fullInverse*sourceLinearPart activeTerms v*fullKernelFrame) := by
  rw [←jet_certificate]
  simp only [jet,change1,response,force,fastNormalizeTerms_value,sourceMatrix_append,negativeTerms_value,
    productTerms_value,change0_value,reader_constant,fullInverse_generated,fullKernel_generated,
    sourceLinearPart,degreeTensor]
  noncomm_ring

private theorem jet_row (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) :
    sourceMatrix jetTerms v (index mu) j=emStaticJet v mu j := by
  rw [jet_value,reader_mul]
  simp only [emStaticJet,sourceChargedNativeFrameJet,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,
    slowFastFrame_inverse_right,fullKernel_five]

private theorem regular_value (v : Fin 4→ℂ) : sourceMatrix regularTerms v=
    reader*(originalChange 0*contactInverse 0*(originalChange 0).transpose+
      originalChange 0*fullInverse*activeProjection*(originalChange 0).transpose)*reader.transpose := by
  rw [←regular_certificate]
  simp only [regular,contact,response,fastNormalizeTerms_value,sourceMatrix_append,productTerms_value,
    change0_value,origin_value,columnTerms_value,fullInverse_generated,transpose_value,Matrix.transpose_mul,
    contactInverse,activeProjection]
  noncomm_ring

private theorem regular_row (v : Fin 4→ℂ) (mu nu : Fin 4) :
    sourceMatrix regularTerms v (index mu) (index nu)=emStaticRegularOrigin mu nu := by
  rw [regular_value,reader_pair]
  simp only [emStaticRegularOrigin,originalReadback,neg_zero,Matrix.mulVec_add,
    Matrix.mulVec_mulVec,Pi.add_apply,Matrix.mul_add,Matrix.add_mul,Matrix.add_apply,Matrix.mul_assoc]
  simp only [←Matrix.mul_assoc]
  rfl

private theorem jet_five (v : Fin 4→ℂ) : sourceMatrix jetTerms v*fiveProjection=sourceMatrix jetTerms v := by
  have certificate : fastNormalizeTerms (productTerms jetTerms fiveProjectionTerms++negativeTerms jetTerms)=[] := by decide +kernel
  have result:=normalization_equal _ _ certificate v
  have constant : sourceMatrix fiveProjectionTerms v=fiveProjection := by
    norm_num [fiveProjection,fiveProjectionTerms,sourceMatrix,SourceTerm.matrix,Powers.value]
  simpa only [productTerms_value,constant] using result

private theorem jet_padded (v : Fin 4→ℂ) :
    sourceMatrix jetTerms v*paddedStaticInverse=sourceMatrix jetTerms v*staticInverse := by
  rw [paddedStaticInverse,Matrix.mul_add,Matrix.mul_sub,Matrix.mul_one,jet_five,sub_self,add_zero]

private theorem directional_value (v : Fin 4→ℂ) : sourceMatrix directionalTerms v=
    sourceMatrix jetTerms v*paddedStaticInverse*(sourceMatrix jetTerms v).transpose := by
  rw [←directional_certificate,fastNormalizeTerms_value,productTerms_value,productTerms_value,transpose_value,jet_padded]
  have constant : sourceMatrix staticInverseTerms v=staticInverse := by
    norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value]
  rw [constant]

private theorem directional_row (v : Fin 4→ℂ) (mu nu : Fin 4) :
    sourceMatrix directionalTerms v (index mu) (index nu)=
      dotProduct (emStaticJet v mu) (paddedStaticInverse*ᵥemStaticJet v nu) := by
  rw [directional_value,Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,jet_row,Matrix.mulVec,dotProduct]

end StaticTable

set_option maxHeartbeats 2400000 in
/-- The entire first static frame, including all five original columns, generates exactly these two EM columns. -/
theorem em_static_jet_complete (v : Fin 4→ℂ) (mu : Fin 4) (j : Fin 289) :
    emStaticJet v mu j=(Pi.single 0 (emLiteralA v mu)+Pi.single 1 (emLiteralB v mu):Fin 289→ℂ) j := by
  rw [←StaticTable.jet_row]
  by_cases h0 : j=0
  · subst j
    fin_cases mu <;> norm_num [StaticTable.jetTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      StaticTable.index,coefficientValue,Powers.value,Pi.single_apply,emLiteralA,emLiteralB,Fin.ext_iff] <;> ring
  by_cases h1 : j=1
  · subst j
    fin_cases mu <;> norm_num [StaticTable.jetTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      StaticTable.index,coefficientValue,Powers.value,Pi.single_apply,emLiteralA,emLiteralB,Fin.ext_iff]
  have j0 : j.val≠0 := fun same=>h0 (Fin.ext same)
  have j1 : j.val≠1 := fun same=>h1 (Fin.ext same)
  fin_cases mu <;> norm_num [StaticTable.jetTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
    StaticTable.index,coefficientValue,Powers.value,Pi.single_apply,emLiteralA,emLiteralB,Fin.ext_iff,j0,j1,Ne.symm j0,Ne.symm j1]

/-- The native algebraic contact projection vanishes at zero; the complete regular term is computed separately. -/
theorem em_static_native_contact_zero (mu nu : Fin 4) :
    (emInsertion.transpose*originalChange 0*contactInverse 0*(originalChange 0).transpose*emInsertion) mu nu=0 := by
  have result:=congrArg (fun ts=>sourceMatrix ts (0:Fin 4→ℂ)) StaticTable.contact_certificate
  simp only [StaticTable.contact,fastNormalizeTerms_value,productTerms_value,StaticTable.change0_value,
    StaticTable.origin_value,StaticTable.transpose_value,Matrix.transpose_mul,sourceMatrix_nil] at result
  have paired:=congrFun (congrFun result (StaticTable.index mu)) (StaticTable.index nu)
  change _=(0:ℂ) at paired
  have regroup : (StaticTable.reader*originalChange 0)*contactInverse 0*
      ((originalChange 0).transpose*StaticTable.reader.transpose)=
      StaticTable.reader*(originalChange 0*contactInverse 0*(originalChange 0).transpose)*StaticTable.reader.transpose := by
    simp only [Matrix.mul_assoc]
  change ((StaticTable.reader*originalChange 0)*contactInverse 0*
      ((originalChange 0).transpose*StaticTable.reader.transpose)) _ _=0 at paired
  rw [regroup,StaticTable.reader_pair] at paired
  simpa only [Matrix.mul_assoc] using paired

/-- All sixteen regular-origin entries, including the full complementary inverse. -/
theorem em_static_regular_explicit : emStaticRegularOrigin=
    Matrix.diagonal ![(rootTwo*rootFifteen)*(-36823/448800:ℂ),
      (rootTwo*rootFifteen)*(-20357/328032:ℂ),
      (rootTwo*rootFifteen)*(-20357/328032:ℂ),
      (rootTwo*rootFifteen)*(1699/96480:ℂ)] := by
  ext mu nu
  rw [←StaticTable.regular_row (0:Fin 4→ℂ)]
  fin_cases mu <;> fin_cases nu <;>
    norm_num [StaticTable.regularTerms,sourceMatrix,SourceTerm.matrix,Matrix.single_apply,
      StaticTable.index,coefficientValue,Powers.value,Matrix.diagonal_apply,Matrix.cons_val,Fin.ext_iff] <;> ring

/-- The complete finite static tensor retains its source-generated angular dependence. -/
def emStaticExplicit (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  let x:ℂ:=n 0; let y:ℂ:=n 1; let z:ℂ:=n 2; let R:=rootTwo*rootFifteen
  ![![R*(-36823/448800+z^2/96),3/80*x*z,3/80*y*z,3/40*z^2],
    ![3/80*x*z,R*(-20357/328032+605677/1206000*x^2),R*(605677/1206000*x*y),R*(287177/603000*x*z)],
    ![3/80*y*z,R*(605677/1206000*x*y),R*(-20357/328032+605677/1206000*y^2),R*(287177/603000*y*z)],
    ![3/40*z^2,R*(287177/603000*x*z),R*(287177/603000*y*z),R*(1699/96480+137677/301500*z^2)]]

set_option maxHeartbeats 2400000 in
/-- The literal 4x4 table is generated from original regular/contact and every source static mode. -/
theorem em_static_limit_explicit (n : PhysicalMomentum) : emStaticLimitTensor n=emStaticExplicit n := by
  ext mu nu
  rw [emStaticLimitTensor,←StaticTable.regular_row (0:Fin 4→ℂ),←StaticTable.directional_row]
  fin_cases mu <;> fin_cases nu <;>
    norm_num [StaticTable.regularTerms,StaticTable.directionalTerms,sourceMatrix,SourceTerm.matrix,
      Matrix.single_apply,StaticTable.index,coefficientValue,Powers.value,emStaticExplicit,
      PreparationVacuumPhysicalCharacteristic.physicalFrequencyMomentum,Fin.cases,Fin.induction,Fin.induction.go,
      Matrix.cons_val]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

/-- The original actual bare-current kernel now has an explicit polynomial in the source direction and both side signs. -/
theorem em_bare_static_explicit (n : PhysicalMomentum) (sideD sideS : Fin 2) :
    emBareStaticLimit n sideD sideS=(16/9:ℂ)*(ActionNormalization.phaseMomentum:ℂ)^2*
      ((rootTwo*rootFifteen)*(-36823/448800+(n 2:ℂ)^2/96)+
        ((PreparationVacuumElectromagneticIdentity.sourceRestSign sideS:ℂ)+
          (PreparationVacuumElectromagneticIdentity.sourceRestSign sideD:ℂ))*
          (Stage9C.Material.SpinPair.lapse:ℂ)*(3/40)*(n 2:ℂ)^2+
        (PreparationVacuumElectromagneticIdentity.sourceRestSign sideD:ℂ)*
          (PreparationVacuumElectromagneticIdentity.sourceRestSign sideS:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)^2*
          (rootTwo*rootFifteen)*(1699/96480+137677/301500*(n 2:ℂ)^2)) := by
  rw [em_bare_static_limit_entries,em_static_limit_explicit]
  simp [emStaticExplicit]
  ring_nf
  simp

end LowEnergy.GaussComposite.ActualEMCarrierOwn
