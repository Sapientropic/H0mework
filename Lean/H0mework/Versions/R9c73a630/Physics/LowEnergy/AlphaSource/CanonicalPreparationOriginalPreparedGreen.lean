import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalFactorization
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationGaugePreparedPorts
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalGreenFeedback
open scoped BigOperators Matrix
open PreparationVacuumGaugeSourceInjection
open GaussUnitaryHistory (Index)

/-- Only the original active103 block is inverted; the identity outside it is
coordinate padding and never contributes to the returned physical field. -/
def extendedKernel (p : Fin 4→ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  activeKernel p+(1-activeProjection)

def regularSource : Set (Fin 4→ℂ) := {p | IsUnit (extendedKernel p).det}

def sourceGreen (p : regularSource) : Matrix (Fin 289) (Fin 289) ℂ :=
  originalChange p.val*(contactInverse p.val+activeProjection*(extendedKernel p.val)⁻¹)*
    originalReadback p.val

/-- The source is unchanged, including all nine unfulfilled compatibility rows. -/
def sourceField (p : regularSource) (forcing : Fin 289→ℂ) : Fin 289→ℂ :=
  sourceGreen p *ᵥ forcing

def sourceCompatibility (p : Fin 4→ℂ) (forcing : Fin 289→ℂ) : Fin 289→ℂ :=
  nullProjection *ᵥ (originalReadback p *ᵥ forcing)

private theorem term_left_projection (flag : Fin 289→Bool) (a : SourceTerm)
    (inside : flag a.row=true) (p : Fin 4→ℂ) : projectionMatrix flag*a.matrix p=a.matrix p := by
  ext i j
  simp only [projectionMatrix,Matrix.diagonal_mul]
  by_cases same : a.row=i
  · rw [←same,inside]
    simp
  · simp [SourceTerm.matrix,Matrix.single,same]

private theorem source_left_projection (flag : Fin 289→Bool) (ts : List SourceTerm)
    (inside : ∀ a∈ts,flag a.row=true) (p : Fin 4→ℂ) :
    projectionMatrix flag*sourceMatrix ts p=sourceMatrix ts p := by
  induction ts with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    rw [sourceMatrix_cons,mul_add,term_left_projection flag a (inside a (by simp)) p,
      ih (fun b hb=>inside b (by simp [hb]))]

theorem original_active_support (p : Fin 4→ℂ) : activeProjection*activeKernel p=activeKernel p := by
  have source : activeTerms.all (fun a=>activeFlag a.row)=true := by decide +kernel
  exact source_left_projection activeFlag activeTerms (List.all_eq_true.mp source) p

theorem active_projection_square : activeProjection*activeProjection=activeProjection := by
  rw [activeProjection,projectionMatrix,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem original_active_extended (p : Fin 4→ℂ) : activeProjection*extendedKernel p=activeKernel p := by
  rw [extendedKernel,mul_add,original_active_support,mul_sub,mul_one,active_projection_square,sub_self,add_zero]

theorem generated_active_inverse (p : regularSource) :
    activeKernel p.val*(extendedKernel p.val)⁻¹=activeProjection := by
  rw [←original_active_extended,mul_assoc,Matrix.mul_nonsing_inv _ p.property,mul_one]

/-- The actual original H acts on the generated Green, leaving exactly its
original nine compatibility directions. Neither a Green identity nor a Ward
completion is supplied as an input. -/
theorem original_green_equation (p : regularSource) :
    originalJacobi p.val*sourceGreen p=1-originalRowLift p.val*nullProjection*originalReadback p.val := by
  have partition : contactProjection+activeProjection=1-nullProjection := by
    rw [eq_sub_iff_add_eq]
    exact projection_partition
  unfold sourceGreen
  calc
    _=(originalJacobi p.val*originalChange p.val*contactInverse p.val+
        originalJacobi p.val*originalChange p.val*activeProjection*(extendedKernel p.val)⁻¹)*
          originalReadback p.val := by noncomm_ring
    _=(originalRowLift p.val*contactProjection+
        originalRowLift p.val*activeKernel p.val*(extendedKernel p.val)⁻¹)*originalReadback p.val := by
      rw [original_contact_intertwiner,original_active_intertwiner]
    _=originalRowLift p.val*(contactProjection+activeProjection)*originalReadback p.val := by
      rw [mul_assoc,generated_active_inverse]
      noncomm_ring
    _=1-originalRowLift p.val*nullProjection*originalReadback p.val := by
      rw [partition,mul_sub,mul_one,sub_mul,original_row_readback]

theorem original_forced_field (p : regularSource) (forcing : Fin 289→ℂ) :
    originalJacobi p.val *ᵥ sourceField p forcing=
      forcing-originalRowLift p.val *ᵥ sourceCompatibility p.val forcing := by
  rw [sourceField,Matrix.mulVec_mulVec,original_green_equation,Matrix.sub_mulVec,Matrix.one_mulVec]
  simp only [sourceCompatibility,Matrix.mulVec_mulVec,mul_assoc]

private def regularPointInverseTermsAtoms : List SourceAtom :=
  let d0 : ℚ := 45164431
  let d1 : ℚ := 49093736497
  let d2 : ℚ := 90328862
  let d3 : ℚ := 135493293
  let d4 : ℚ := 196374945988
  let d5 : ℚ := 1503763264
  let d6 : ℚ := 4394375689941502785000
  let d7 : ℚ := 1625919516
  let d8 : ℚ := 270986586
  let d9 : ℚ := 1038781913
  let d10 : ℚ := 116057593078908
  let d11 : ℚ := 145071991348635
  let d12 : ℚ := 1551754823197176
  let d13 : ℚ := 46552644695915280
  let d14 : ℚ := 232115186157816
  let d15 : ℚ := 131831270698245083550000
  let a (r s t u : ℚ) : SourceAtom := (⟨0,0,0,0⟩,⟨⟨r,s⟩,⟨t,u⟩⟩)
  [
 a (0) (0) (0) ((-12475178177035/d12)),a (0) ((150764442125/d4)) (0) (0), a (0) (0) ((1053560162827/119365755630552:ℚ)) (0),a (0) (0) ((-16855490653951/d12)) (0),
 a (0) (0) ((10350/d0)) (0),a (0) (0) ((-259950/d0)) (0), a ((-55965270925/d4)) (0) (0) (0),a ((60129839675/d4)) (0) (0) (0),
 a ((-215625/d2)) (0) (0) (0),a ((5415625/d2)) (0) (0) (0), a ((14511888825/d1)) (0) (0) (0),a (0) (0) ((-3493389626071/d12)) (0),
 a ((-355/6522:ℚ)) (0) (0) (0),a (0) (0) ((-3005/117396:ℚ)) (0), a (0) (0) (0) ((-15/878:ℚ)),a (0) (0) (0) ((1115786675/d1)),
 a (0) (0) (0) ((1677339225/98187472994:ℚ)),a (0) (0) (0) ((1518575/d2)), a (0) ((-150764442125/589124837964:ℚ)) (0) (0),a (0) ((150764442125/589124837964:ℚ)) (0) (0),
 a (0) ((-42259375/180657724:ℚ)) (0) (0),a (0) ((-150764442125/d4)) (0) (0), a (0) (0) ((-1053560162827/119365755630552:ℚ)) (0),a (0) (0) ((16855490653951/d12)) (0),
 a (0) (0) ((-10350/d0)) (0),a (0) (0) ((259950/d0)) (0), a (0) (0) ((3493389626071/d12)) (0),a ((355/6522:ℚ)) (0) (0) (0),
 a (0) (0) (0) ((15/878:ℚ)),a (0) (0) (0) ((-1115786675/d1)), a (0) (0) (0) ((-1518575/d2)),a (0) (0) (0) ((-467059652226071/d13)),
 a (0) (0) (0) ((223530455904371/d13)),a (0) (0) (0) ((220625/d7)), a (0) (0) (0) ((1004365/d7)),a (0) ((2581238250/d1)) (0) (0),
 a (0) ((-5578933375/98187472994:ℚ)) (0) (0),a (0) ((43125/d2)) (0) (0), a (0) ((-1083125/d2)) (0) (0),a (0) ((-10741409875/d4)) (0) (0),
 a (0) (0) (0) ((-2479675353593/3580972668916560:ℚ)),a (0) ((71/6522:ℚ)) (0) (0), a (0) (0) (0) ((-1775/234792:ℚ)),a (0) (0) ((7/3951:ℚ)) (0),
 a (0) (0) ((-412998120/d1)) (0),a (0) (0) ((-335467845/d1)) (0), a (0) (0) ((-21005/3474187:ℚ)) (0),a ((27894666875/294562418982:ℚ)) (0) (0) (0),
 a ((-4302063750/d1)) (0) (0) (0),a ((11720000/d3)) (0) (0) (0), a (0) (0) (0) ((-504970154672471/d13)),a (0) (0) (0) ((369665/d7)),
 a (0) (0) (0) ((-2738915/d7)),a (0) ((2997695125/d1)) (0) (0), a (0) ((-43125/d2)) (0) (0),a (0) ((1083125/d2)) (0) (0),
 a (0) ((11574323625/d4)) (0) (0),a (0) (0) (0) ((13280528373509/d13)), a (0) ((-71/6522:ℚ)) (0) (0),a (0) (0) (0) ((1775/234792:ℚ)),
 a (0) (0) ((-7/3951:ℚ)) (0),a (0) (0) ((479631220/d1)) (0), a (0) (0) ((335467845/d1)) (0),a (0) (0) ((334365/d0)) (0),
 a ((-27894666875/294562418982:ℚ)) (0) (0) (0),a ((14988475625/147281209491:ℚ)) (0) (0) (0), a ((-13635625/d3)) (0) (0) (0),a (0) (0) (0) ((-2221405/d8)),
 a (0) (0) (0) ((233005/406479879:ℚ)),a (0) (0) (0) ((2070/d0)), a (0) (0) ((-6900/d0)) (0),a ((-71875/d0)) (0) (0) (0),
 a ((71875/d0)) (0) (0) (0),a (0) (0) (0) ((-4992355/d8)), a (0) (0) (0) ((-51990/d0)),a (0) (0) ((173300/d0)) (0),
 a ((5415625/d3)) (0) (0) (0),a ((-5415625/d3)) (0) (0) (0), a (0) ((-2581238250/d1)) (0) (0),a (0) ((5578933375/98187472994:ℚ)) (0) (0),
 a (0) ((10741409875/d4)) (0) (0),a ((-11720000/d3)) (0) (0) (0), a (0) ((-2997695125/d1)) (0) (0),a (0) ((-11574323625/d4)) (0) (0),
 a ((13635625/d3)) (0) (0) (0),a (0) (0) (0) ((-213382718565461/d13)), a (0) (0) ((-47/3951:ℚ)) (0),a ((8451875/d2)) (0) (0) (0),
 a (0) (0) ((446314670/d1)) (0),a (0) (0) ((303715/d0)) (0), a ((-8451875/d2)) (0) (0) (0),a (0) (0) (0) ((-98129/1760940:ℚ)),
 a ((355/9783:ℚ)) (0) (0) (0),a ((-355/9783:ℚ)) (0) (0) (0), a (0) (0) (0) ((10/439:ℚ)),a (0) (0) (0) ((-2231573350/147281209491:ℚ)),
 a (0) (0) (0) ((-25/3261:ℚ)),a (0) (0) (0) ((-338075/d0)), a (0) ((-42259375/541973172:ℚ)) (0) (0),a (0) ((42259375/541973172:ℚ)) (0) (0),
 a (0) (0) (0) ((-1677339225/98187472994:ℚ)),a ((4302063750/d1)) (0) (0) (0), a ((-14988475625/147281209491:ℚ)) (0) (0) (0),a (0) (0) (0) ((-559113075/d1)),
 a (0) (0) (0) ((-504350/d3)),a (0) (0) (0) ((-1518575/d3)), a (0) ((42259375/d8)) (0) (0),a (0) (0) (0) ((25/3261:ℚ)),
 a (0) (0) (0) ((504350/d3)),a (0) ((-42259375/d8)) (0) (0), a (0) (0) (0) ((-21962625/375940816:ℚ)),a (0) (0) ((4581975/375940816:ℚ)) (0),
 a (0) (0) ((-4581975/375940816:ℚ)) (0),a (0) (0) (0) ((-29374625/d5)), a (0) ((-1265625/d5)) (0) (0),a (0) ((1265625/d5)) (0) (0),
 a (0) (0) (0) ((29374625/d5)),a (0) (0) (0) ((-1411850525/218797554912:ℚ)), a (0) (0) (0) ((155951185/72932518304:ℚ)),a ((-9765625/d5)) (0) (0) (0),
 a ((9765625/d5)) (0) (0) (0),a (0) (0) ((-5406175/d5)) (0), a (0) (0) (0) ((-155951185/72932518304:ℚ)),a (0) (0) ((5406175/d5)) (0),
 a (0) (0) (0) ((14874475/9022579584:ℚ)),a (0) (0) (0) ((3232375/563911224:ℚ)), a (0) ((-707028125/9022579584:ℚ)) (0) (0),a (0) ((707028125/9022579584:ℚ)) (0) (0),
 a (0) (0) (0) ((-52506940522923167239/439437568994150278500:ℚ)),a (0) (0) (0) ((26140686383274150529/439437568994150278500:ℚ)), a (0) (0) (0) ((-3/50:ℚ)),a (0) (0) ((99904594974842376161/d6)) (0),
 a ((-5/92:ℚ)) (0) (0) (0),a (0) (0) ((-133271152985028426161/d6)) (0), a ((-45440695/d9)) (0) (0) (0),a ((134940765/2077563826:ℚ)) (0) (0) (0),
 a (0) (0) ((-5733/113275:ℚ)) (0),a (0) ((-3/197:ℚ)) (0) (0), a (0) ((-13353217456669/58028796539454:ℚ)) (0) (0),a (0) ((-2994160185287/d10)) (0) (0),
 a (0) ((3927288865463/d10)) (0) (0),a (0) ((-1374834676213/d10)) (0) (0), a (0) (0) (0) ((71523/2265500:ℚ)),a (0) (0) (0) ((-3480207969917/102320018430500:ℚ)),
 a (0) (0) (0) ((122884543/2258221550:ℚ)),a (0) (0) (0) ((-9830953363274664721/109859392248537569625:ℚ)), a (0) (0) (0) ((3/100:ℚ)),a (0) (0) (0) ((9/100:ℚ)),
 a (0) (0) ((-73538340835193359451/d6)) (0),a ((5/92:ℚ)) (0) (0) (0), a (0) (0) ((106904898845379409451/d6)) (0),a ((45440695/d9)) (0) (0) (0),
 a ((-134940765/2077563826:ℚ)) (0) (0) (0),a ((215625/d2)) (0) (0) (0), a ((-5415625/d2)) (0) (0) (0),a (0) (0) ((5733/113275:ℚ)) (0),
 a (0) ((3/197:ℚ)) (0) (0),a (0) (0) ((3005/117396:ℚ)) (0), a (0) ((13353217456669/58028796539454:ℚ)) (0) (0),a (0) ((2994160185287/d10)) (0) (0),
 a (0) ((-3927288865463/d10)) (0) (0),a (0) ((1374834676213/d10)) (0) (0), a (0) (0) (0) ((-12217/566375:ℚ)),a (0) (0) (0) ((3480207969917/102320018430500:ℚ)),
 a (0) (0) (0) ((-40120931/903288620:ℚ)),a (0) (0) (0) ((-9/100:ℚ)), a (0) (0) (0) ((-3/100:ℚ)),a (0) (0) ((9/500:ℚ)) (0),
 a (0) (0) ((-9/500:ℚ)) (0),a (0) (0) ((3/100:ℚ)) (0), a (0) (0) ((-3/100:ℚ)) (0),a (0) (0) (0) ((1/20:ℚ)),
 a (0) (0) ((-99904594974842376161/d6)) (0),a (0) (0) ((73538340835193359451/d6)) (0), a (0) (0) (0) ((-224786670284595083789/d15)),a (0) ((-1/92:ℚ)) (0) (0),
 a (0) (0) (0) ((-844333459291782934961/d15)),a (0) ((-9088139/d9)) (0) (0), a (0) ((26988153/2077563826:ℚ)) (0) (0),a (0) (0) (0) ((-5733/566375:ℚ)),
 a ((-6/985:ℚ)) (0) (0) (0),a ((-25594260799963/290143982697270:ℚ)) (0) (0) (0), a ((-940993035956/d11)) (0) (0) (0),a ((1407557376044/d11)) (0) (0) (0),
 a ((-1243504394794/d11)) (0) (0) (0),a (0) (0) ((120391/11327500:ℚ)) (0), a (0) (0) ((-3480207969917/255800046076250:ℚ)) (0),a (0) (0) ((446373741/22582215500:ℚ)) (0),
 a (0) ((1/92:ℚ)) (0) (0),a (0) (0) (0) ((-8995/6542856:ℚ)), a (0) (0) (0) ((17065/3271428:ℚ)),a (0) (0) (0) ((-17065/3271428:ℚ)),
 a (0) ((5/69:ℚ)) (0) (0),a (0) (0) ((-40/11853:ℚ)) (0), a (0) (0) ((20/11853:ℚ)) (0),a ((5/138:ℚ)) (0) (0) (0),
 a (0) (0) ((133271152985028426161/d6)) (0),a (0) (0) ((-106904898845379409451/d6)) (0), a (0) (0) (0) ((175612025837637516211/d15)),a (0) ((9088139/d9)) (0) (0),
 a (0) ((-26988153/2077563826:ℚ)) (0) (0),a (0) (0) (0) ((5733/566375:ℚ)), a ((6/985:ℚ)) (0) (0) (0),a ((25594260799963/290143982697270:ℚ)) (0) (0) (0),
 a ((940993035956/d11)) (0) (0) (0),a ((-1407557376044/d11)) (0) (0) (0), a ((1243504394794/d11)) (0) (0) (0),a (0) (0) ((-120391/11327500:ℚ)) (0),
 a (0) (0) ((3480207969917/255800046076250:ℚ)) (0),a (0) (0) ((-446373741/22582215500:ℚ)) (0), a (0) (0) (0) ((-309836592415/73876092088734:ℚ)),a (0) (0) (0) ((-213419127985/147752184177468:ℚ)),
 a (0) (0) (0) ((295145/d7)),a (0) (0) (0) ((-867275/d7)), a (0) (0) ((15325/d0)) (0),a ((90881390/3116345739:ℚ)) (0) (0) (0),
 a ((-1915625/d8)) (0) (0) (0),a (0) ((-5/69:ℚ)) (0) (0), a (0) (0) ((-20/11853:ℚ)) (0),a (0) (0) ((40/11853:ℚ)) (0),
 a ((-5/138:ℚ)) (0) (0) (0),a ((-44980255/d9)) (0) (0) (0), a (0) (0) ((-3450/d0)) (0),a (0) (0) ((86650/d0)) (0),
 a (0) (0) (0) ((18577/226550:ℚ)),a ((-1/197:ℚ)) (0) (0) (0), a ((3/394:ℚ)) (0) (0) (0),a ((-3/394:ℚ)) (0) (0) (0),
 a (0) (0) ((3822/113275:ℚ)) (0),a (0) (0) (0) ((9625/1556694:ℚ)), a (0) (0) (0) ((-8105/1556694:ℚ)),a (0) (0) (0) ((5/2364:ℚ)),
 a (0) (0) (0) ((-5/2364:ℚ)),a (0) ((2/197:ℚ)) (0) (0), a ((355/19566:ℚ)) (0) (0) (0),a ((-355/19566:ℚ)) (0) (0) (0),
 a (0) (0) (0) ((-1615645947355/d14)),a (0) (0) (0) ((-142833852445/d14)), a (0) (0) (0) ((-725906656655/d14)),a (0) (0) (0) ((746905438255/d14)),
 a (0) ((161/2364:ℚ)) (0) (0),a (0) ((6985325375/106768714884:ℚ)) (0) (0), a (0) ((43711903/541973172:ℚ)) (0) (0),a (0) ((-161/2364:ℚ)) (0) (0),
 a (0) ((111647625/8897392907:ℚ)) (0) (0),a (0) ((-121044/d0)) (0) (0), a (0) (0) (0) ((-71523/2265500:ℚ)),a (0) (0) (0) ((12217/566375:ℚ)),
 a (0) (0) (0) ((-1/20:ℚ)),a (0) (0) ((-3822/113275:ℚ)) (0), a (0) ((-2/197:ℚ)) (0) (0),a (0) (0) (0) ((120391/6796500:ℚ)),
 a (0) (0) (0) ((-21469/1132750:ℚ)),a (0) (0) (0) ((11/300:ℚ)), a ((-90881390/3116345739:ℚ)) (0) (0) (0),a ((44980255/d9)) (0) (0) (0),
 a (0) ((-6985325375/106768714884:ℚ)) (0) (0),a (0) ((-111647625/8897392907:ℚ)) (0) (0), a (0) (0) (0) ((-3480207969917/153480027645750:ℚ)),a (0) (0) (0) ((-122884543/2258221550:ℚ)),
 a (0) (0) (0) ((40120931/903288620:ℚ)),a ((1915625/d8)) (0) (0) (0), a (0) ((-43711903/541973172:ℚ)) (0) (0),a (0) ((121044/d0)) (0) (0),
 a (0) (0) (0) ((148791247/4516443100:ℚ)),a (0) (0) (0) ((-5/612:ℚ)), a (0) (0) (0) ((158775/70485512:ℚ)),a (0) (0) (0) ((125/19816:ℚ)),
 a (0) (0) (0) ((-336625/70485512:ℚ)),a (0) ((9428125/105728268:ℚ)) (0) (0), a (0) ((-140625/8810689:ℚ)) (0) (0),a (0) ((140625/8810689:ℚ)) (0) (0),
 a (0) ((-9428125/105728268:ℚ)) (0) (0),a (0) (0) (0) ((-125/19816:ℚ)), a (0) (0) (0) ((336625/70485512:ℚ)),a (0) (0) (0) ((1309391/440534450:ℚ)),
 a (0) (0) (0) ((-6191907/881068900:ℚ)),a (0) (0) (0) ((9288157/881068900:ℚ)), a (0) (0) (0) ((119367/220267225:ℚ)),a (0) ((9119407/105728268:ℚ)) (0) (0),
 a (0) ((51453/17621378:ℚ)) (0) (0),a (0) ((140625/17621378:ℚ)) (0) (0), a (0) ((-140625/17621378:ℚ)) (0) (0),a (0) ((-9119407/105728268:ℚ)) (0) (0),
 a (0) ((-51453/17621378:ℚ)) (0) (0),a (0) (0) (0) ((75425/17621378:ℚ)), a (0) (0) (0) ((6750/8810689:ℚ)),a (0) (0) (0) ((75/13472:ℚ)),
 a (0) ((3125/40416:ℚ)) (0) (0),a (0) ((-3125/40416:ℚ)) (0) (0)]
private def regularPointInverseTermsCodes : List ℕ := [
 756900,757191,762122,762413,763284,763575,765606,765897,766768,767059,767350,767641,771122,771703,772864,774605,775186,776347,
 777508,778089,779250,840731,841000,845936,846227,847098,847389,849432,849723,850594,850885,851176,851450,854933,855527,856978,
 858418,858998,860160,861329,861896,863070,2265502,2265776,2270731,2271022,2271893,2272184,2274215,2274506,2275377,2275668,2275959,2276250,
 2279731,2280312,2281473,2283214,2283795,2284956,2286117,2286698,2287859,2349313,2349587,2354542,2354850,2355721,2356012,2358026,2358333,2359204,
 2359495,2359786,2360077,2363558,2364139,2365300,2367041,2367622,2368783,2369944,2370525,2371686,2600744,2601018,2605973,2606281,2607167,2607458,
 2609457,2609764,2611214,2611519,2618480,2620220,2621961,2623122,2684555,2684829,2689784,2690092,2690978,2691273,2693268,2693575,2695025,2695334,
 2702295,2704035,2705776,2706937,3271206,3271492,3276498,3276789,3277634,3277925,3279931,3280222,3281093,3281384,3281680,3282010,3285469,3286031,
 3287483,3288954,3289518,3290711,3291834,3292432,3293576,3355017,3355303,3360309,3360602,3361427,3361718,3363742,3364050,3364921,3365212,3365507,
 3365823,3369262,3369858,3371310,3372747,3373345,3374524,3375661,3376225,3377403,3606448,3606734,3611714,3611987,3615173,3615481,3616367,3616658,
 3616949,3617207,3624781,3625941,3627100,3628840,3690259,3690545,3695525,3695798,3698984,3699292,3700178,3700473,3700764,3701018,3708596,3709756,
 3710915,3712655,3774070,3774361,3779360,3779653,3780477,3780768,3782800,3783107,3783989,3784284,3784585,3784826,3788312,3788908,3790386,3791797,
 3792377,3793577,3794738,3795275,3796479,3857896,3858170,3863130,3863437,3864319,3864614,3866609,3866916,3867784,3868075,3868389,3868685,3872138,
 3872719,3873906,3875648,3876202,3877389,3878524,3879087,3880290,4863617,4863893,4868851,4869158,4872332,4872639,4874089,4874378,4877891,4881372,
 4881952,5031223,5031512,5036489,5036762,5039951,5040258,5041708,5041982,5046091,5051892,5052473,5366478,5371713,5372020,5377266,5382494,5450564,
 5459003,5459310,5460786,5466594,5869339,5869618,5874574,5874881,5875760,5876055,5878057,5878364,5879814,5880128,5883612,5887095,5887676,5888837,
 5890578,5891739,6037030,6037238,6042195,6042502,6045731,6046022,6046862,6047157,6047434,6047722,6051232,6054716,6055303,6056464,6057619,6059359,
 6372200,6372480,6377436,6377743,6378620,6378915,6380919,6381226,6382102,6382397,6382700,6382989,6389957,6390544,6391705,6392859,6393438,6394606,
 6707428,6707715,6712694,6712967,6716154,6716461,6717340,6717635,6717938,6718187,6722292,6725778,6726938,6728095,6728687,6729837,6875049,6875420,
 6880351,6880642,6881482,6881777,6883792,6884065,6885515,6885824,6889913,6892819,6894559,6895727,6896303,6897468,7210290,7210577,7215571,7215864,
 7216721,7217016,7219016,7219323,7220200,7220495,7220799,7221087,7228058,7228638,7229809,7230957,7231548,7232705,925210,929561,932752,935941,
 942613,944353,945514,947255,1009310,1013082,1016852,1019462,1026424,1028165,1029326,1031066,2098841,2102617,2106388,2108998,2115959,2117700,
 2118861,2120601,2182362,2186717,2189912,2193098,2199771,2201511,2202670,2204409,3104271,3108632,3111817,3115012,3121683,3123423,3124579,3126320,
 3188371,3192148,3195917,3198528,3205489,3207230,3208391,3210131,3942661,3946438,3950208,3952817,3959779,3961520,3962681,3964421,4026182,4030538,
 4033732,4036917,4043591,4045331,4046490,4048229,5953816,5954104,5957880,5958171,5961363,5961650,5964260,5964551,5971224,5972965,5974126,6456676,
 6456965,6460739,6461031,6464223,6464509,6467119,6467411,6474085,6475824,6478727,6791914,6792203,6795981,6796269,6799460,6799751,6802361,6802649,
 6809327,6812224,6813965,7294775,7295063,7298841,7299130,7302319,7302611,7305221,7305510,7313926,7315085,7316824,1093410,1096601,1099791,1104142,
 1109366,1111106,1112265,1114004,1177510,1180122,1183891,1187661,1193175,1194914,1196073,1197813,1931801,1934417,1938192,1941962,1947470,1949209,
 1950373,1952113,2015322,2018517,2021708,2026062,2031283,2033023,2034179,2035920,2937232,2940428,2943617,2947972,2953193,2954933,2956089,2957830,
 3021332,3023952,3027717,3031488,3036999,3038740,3039901,3041641,4110862,4113482,4117248,4121017,4126529,4128270,4129431,4131171,4194381,4197582,
 4200772,4205117,4210341,4212081,4213240,4214979,5702963,5703255,5705869,5706163,5709353,5709640,5713410,5713701,5718924,5720665,5721826,6205823,
 6206114,6208730,6209023,6212213,6212499,6216269,6216561,6221785,6223524,6226427,6541065,6541356,6543973,6544260,6547450,6547741,6551511,6551799,
 6557027,6559924,6561665,7043924,7044216,7046833,7047119,7050309,7050601,7054371,7054660,7061626,7062785,7064524,1261628,1261919,1262790,1263080,
 1263371,1263662,1266852,1267143,1272074,1272365,1273108,1273399,1273816,1274397,1274868,1275267,1275433,1276427,1276718,1277299,1278460,1279041,
 1280202,1281363,1281944,1345439,1345745,1346616,1346907,1347198,1347489,1350679,1350970,1355901,1356192,1357063,1357354,1357645,1358226,1358664,
 1359096,1359387,1360256,1360548,1361129,1362290,1362871,1364032,1365193,1365774,1596870,1597176,1598065,1598356,1598647,1602418,1615446,1617186,
 1680680,1680987,1681876,1682165,1682459,1686230,1699281,1701021,1764532,1764823,1765688,1765980,1766274,1766565,1769755,1770046,1774977,1775268,
 1776014,1776305,1776719,1777300,1777743,1778170,1778339,1779330,1779621,1780202,1781363,1781944,1783105,1784266,1784847,1848302,1848609,1850098,
 1850389,1853580,1853855,1858800,1859091,1860542,1861123,1861994,1863154,1866925,1868085,2770212,2770519,2772008,2772300,2775489,2775765,2780710,
 2781001,2782452,2783034,2783903,2785064,2788835,2789995,2854086,2854377,2855217,2855509,2855806,2856108,2859298,2859598,2864529,2864820,2865527,
 2865818,2866271,2866852,2867316,2867722,2867852,2868882,2869173,2869754,2870915,2871496,2872657,2873818,2874399,4278794,4279101,4280599,4280880,
 4284070,4284347,4289310,4289601,4290472,4290763,4291032,4291614,4292484,4293643,4293954,4294534,4295694,4296274,4297415,4298595,4299176,4362605,
 4362912,4364410,4364691,4367881,4368158,4373121,4373410,4374282,4374573,4374867,4375448,4376318,4377479,4377764,4378344,4379504,4380084,4381250,
 4382411,4382986,4613908,4614343,4615677,4619464,4624552,4624842,4625567,4625858,4629202,4629782,4630942,4631522,4633692,4634272,4697719,4698154,
 4699488,4703275,4708363,4708653,4709378,4709673,4713013,4713593,4714753,4715333,4717507,4718087,4781656,4781965,4783461,4783742,4786932,4787209,
 4792152,4792467,4793924,4794505,4795375,4796535,4796826,4797407,4798566,4799147,4800308,4801468,4949277,4949586,4951082,4951363,4954554,4954830,
 4959774,4960088,4961545,4962129,4963000,4964160,4964451,4965032,4966191,4966772,4967933,4969093,5116774,5117078,5118543,5122356,5130194,5200707,
 5201016,5202512,5202794,5205983,5206260,5211204,5211518,5212975,5213560,5214429,5215590,5215881,5216462,5217621,5218202,5219363,5220523,5284393,
 5284827,5286162,5289949,5298391,5299694,5300274,5301435,5302015,5535947,5536256,5537752,5538034,5541224,5541500,5546443,5546759,5548215,5548800,
 5549670,5550829,5551121,5551702,5552861,5553442,5554603,5555763,5619758,5620068,5621563,5625311,5630274,5630564,5631442,5631733,5632026,5632611,
 5633481,5633774,5634641,5634936,5635517,5636678,5637259,5638420,5639581,5640162,5787379,5787689,5789184,5792932,5797894,5798184,5799062,5799353,
 5799647,5800232,5801102,5801394,5802262,5802557,5803136,5804299,5804878,5806043,5807204,5807785,6122620,6122930,6124425,6128173,6133134,6133424,
 6134302,6134593,6134886,6135471,6136341,6136635,6137501,6137798,6138379,6139536,6140117,6141177,6142441,6143025,6290241,6290551,6292046,6295794,
 6300754,6301044,6301922,6302213,6302507,6303092,6303962,6304255,6305122,6305419,6305998,6307157,6307736,6308816,6310064,6310642,6625586,6625877,
 6626666,6627038,6627265,6627590,6630780,6631057,6636000,6636265,6637769,6638350,6639220,6640380,6640663,6641240,6642316,6642877,6644151,6645312,
 6645893,6960743,6961013,6962506,6962830,6966020,6966298,6971274,6971565,6972251,6972546,6973009,6973590,6974460,6975620,6975916,6976497,6977656,
 6978237,6979392,6980558,6980984,7128459,7128750,7129526,7129898,7130127,7133919,7138901,7139191,7139871,7140166,7143542,7144123,7145283,7145862,
 7147013,7148024,7148764,1429830,4457565,1513930,4541665,2439165,2523265,3448365,3532465,7401066,7402227,7402807,7403968,7404549,7407450,7736307,
 7737466,7738048,7739207,7740949,7741530,7903927,7905088,7905666,7906827,7908571,7909152,8239168,8240327,8240907,8242066,8242651,8245552,8406792,
 8409690,8410266,8411433,8412007,8413174,8743192,8743770,8745513,8746666,8747254,8748407,8910811,8911389,8913127,8914294,8914866,8916033,9244891,
 9247789,9248374,9249527,9250113,9251266,7485175,7485756,7486917,7487498,7488659,7489240,7490401,7490981,7652796,7653375,7654538,7655117,7656280,
 7656859,7658021,7658601,7988037,7988618,7989775,7990356,7991522,7992102,7993263,7993844,8155658,8156237,8157396,8157975,8159142,8159722,8160884,
 8161463,8490903,8491484,8492641,8493221,8494385,8494965,8496126,8496706,8658524,8659103,8660261,8660841,8662005,8662585,8663746,8664326,8993762,
 8994342,8995499,8996080,8997246,8997826,8998985,8999565,9161382,9161962,9163120,9163699,9164866,9165446,9166605,9167185,7569287,7572768,8575009,
 8578487,7821587,7825068,8827309,8830787,8073887,8077369,9079608,9083087,8326187,8329669,9331908,9335387]
def regularPointInverseTerms : List SourceTerm := decodeTerms regularPointInverseTermsAtoms regularPointInverseTermsCodes

def coefficientPoint : Fin 4→SourceCoefficient := Fin.cases 3 (fun _=>0)
def regularPoint : Fin 4→ℂ := Fin.cases 3 (fun _=>0)

def substituteTerms (q : Fin 4→SourceCoefficient) (ts : List SourceTerm) : List SourceTerm :=
  ts.map (fun a=>⟨a.row,a.column,⟨0,0,0,0⟩,
    a.coefficient*q 0^a.powers.temporal*q 1^a.powers.first*q 2^a.powers.second*q 3^a.powers.third⟩)

theorem substituteTerms_value (q : Fin 4→SourceCoefficient) (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (substituteTerms q ts) p=sourceMatrix ts (fun i=>coefficientMap (q i)) := by
  induction ts with
  | nil=>rfl
  | cons a rest ih=>
    simp only [substituteTerms,List.map_cons,sourceMatrix_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [SourceTerm.matrix,Powers.value,pow_zero,mul_one]
    congr 1
    change coefficientMap _=_
    rw [map_mul,map_mul,map_mul,map_mul,map_pow,map_pow,map_pow,map_pow]
    rw [show coefficientMap a.coefficient=coefficientValue a.coefficient from rfl]
    ring

theorem coefficientPoint_value : (fun i=>coefficientMap (coefficientPoint i))=regularPoint := by
  funext i
  refine Fin.cases ?_ (fun j=> ?_) i
  · change coefficientMap (3:SourceCoefficient)=(3:ℂ)
    exact map_ofNat coefficientMap 3
  · change coefficientMap (0:SourceCoefficient)=(0:ℂ)
    exact coefficientMap.map_zero

def outsideFlag (i : Fin 289) : Bool := !activeFlag i

theorem outside_projection : projectionMatrix outsideFlag=1-activeProjection := by
  ext i j
  by_cases same : i=j
  · subst j
    simp only [projectionMatrix,activeProjection,Matrix.sub_apply,Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq,outsideFlag]
    by_cases h : activeFlag i=true
    · simp [h]
    · simp [Bool.eq_false_of_not_eq_true h]
  · simp [projectionMatrix,activeProjection,Matrix.sub_apply,same]

def regularKernelTerms : List SourceTerm :=
  substituteTerms coefficientPoint activeTerms++projectionTerms outsideFlag

def regularInverseTerms : List SourceTerm := regularPointInverseTerms++projectionTerms outsideFlag

theorem regularKernelTerms_value (p : Fin 4→ℂ) :
    sourceMatrix regularKernelTerms p=extendedKernel regularPoint := by
  rw [regularKernelTerms,sourceMatrix_append,substituteTerms_value,
    coefficientPoint_value,projectionTerms_value,outside_projection]
  rfl

def regularDifference (i : Fin 289) : List SourceTerm :=
  productTerms (rowTerms i regularKernelTerms) regularInverseTerms++negativeTerms (rowTerms i identityTerms)

private theorem regular_block0 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 0 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block1 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 1 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block2 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 2 i))=[] := by
  fin_cases i <;> decide +kernel
set_option maxHeartbeats 2000000 in
private theorem regular_block3 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 3 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block4 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 4 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block5 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 5 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block6 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 6 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block7 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 7 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block8 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 8 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block9 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 9 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block10 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 10 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block11 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 11 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block12 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 12 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block13 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 13 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block14 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 14 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block15 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 15 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_block16 (i : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow 16 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem regular_blocks (block offset : Fin 17) : fastNormalizeTerms (regularDifference (sourceRow block offset))=[] := by
  fin_cases block
  · exact regular_block0 offset
  · exact regular_block1 offset
  · exact regular_block2 offset
  · exact regular_block3 offset
  · exact regular_block4 offset
  · exact regular_block5 offset
  · exact regular_block6 offset
  · exact regular_block7 offset
  · exact regular_block8 offset
  · exact regular_block9 offset
  · exact regular_block10 offset
  · exact regular_block11 offset
  · exact regular_block12 offset
  · exact regular_block13 offset
  · exact regular_block14 offset
  · exact regular_block15 offset
  · exact regular_block16 offset

private theorem regular_rows (i : Fin 289) : fastNormalizeTerms (regularDifference i)=[] := by
  let block : Fin 17:=⟨i.val/17,by have hi:=i.isLt;omega⟩
  let offset : Fin 17:=⟨i.val%17,Nat.mod_lt _ (by decide)⟩
  have eq : i=sourceRow block offset := by apply Fin.ext;dsimp [sourceRow,block,offset];omega
  rw [eq]
  exact regular_blocks block offset

theorem actual_regular_inverse :
    extendedKernel regularPoint*sourceMatrix regularInverseTerms regularPoint=1 := by
  ext i j
  have h:=congrFun (congrFun (normalization_equal (productTerms (rowTerms i regularKernelTerms) regularInverseTerms) (rowTerms i identityTerms) (regular_rows i) regularPoint) i) j
  rw [row_product_entry,regularKernelTerms_value,rowTerms_entry,identityTerms_value] at h
  exact h

def generatedRegularPoint : regularSource :=
  ⟨regularPoint,Matrix.isUnit_det_of_right_inverse actual_regular_inverse⟩

open Filter Topology
open PreparationVacuumCausalFieldResponse CanonicalPhysicalLaplace
open CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily
local instance : NormedAlgebra ℝ FieldOp := NormedAlgebra.restrictScalars ℝ ℂ _

private def SourceSubexp {E : Type*} [Norm E] (f : ℝ→E) : Prop :=
  ∀ d : ℝ, 0<d→Tendsto (fun r=>Real.exp (-d*r)*‖f r‖) atTop (𝓝 0)

private theorem subexp_const {E : Type*} [Norm E] (v : E) : SourceSubexp (fun _=>v) := by
  intro d hd
  have h : Tendsto (fun r : ℝ=>Real.exp (-d*r)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 d hd
  simpa using h.mul_const ‖v‖

private theorem subexp_add {E : Type*} [SeminormedAddCommGroup E] {f g : ℝ→E}
    (hf : SourceSubexp f) (hg : SourceSubexp g) : SourceSubexp (fun r=>f r+g r) := by
  intro d hd
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=> ?_) (by simpa using (hf d hd).add (hg d hd))
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le).trans_eq (by simp only [neg_mul];ring)

private theorem subexp_neg {E : Type*} [SeminormedAddCommGroup E] {f : ℝ→E}
    (hf : SourceSubexp f) : SourceSubexp (fun r=> -f r) := by
  simpa only [SourceSubexp,norm_neg] using hf

private theorem subexp_mul {E : Type*} [NormedRing E] {f g : ℝ→E}
    (hf : SourceSubexp f) (hg : SourceSubexp g) : SourceSubexp (fun r=>f r*g r) := by
  intro d hd
  have half : 0<d/2 := by positivity
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=> ?_) (by simpa using (hf (d/2) half).mul (hg (d/2) half))
  have w : Real.exp (-d*r)=Real.exp (-(d/2)*r)*Real.exp (-(d/2)*r) := by
    rw [←Real.exp_add];congr 1;ring
  calc
    _≤Real.exp (-d*r)*(‖f r‖*‖g r‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Real.exp_pos _).le
    _=_ := by rw [w];simp only [neg_mul];ring

private theorem subexp_smul {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (c : 𝕜) {f : ℝ→E} (hf : SourceSubexp f) : SourceSubexp (fun r=>c • f r) := by
  intro d hd
  convert (hf d hd).const_mul ‖c‖ using 1
  · ext r;simp only [norm_smul,neg_mul];ring
  · simp

private theorem subexp_map {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ G] (L : E→L[ℂ] G) {f : ℝ→E}
    (hf : SourceSubexp f) : SourceSubexp (fun r=>L (f r)) := by
  intro d hd
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=> ?_) (by simpa using (hf d hd).const_mul ‖L‖)
  exact (mul_le_mul_of_nonneg_left (L.le_opNorm _) (Real.exp_pos _).le).trans_eq (by simp only [neg_mul];ring)

private theorem source_time_subexp (q : SourceResponsePoint) (F : Index)
    (p : PhysicalMomentum) (a b : ℝ) :
    SourceSubexp (fun r=>SourceFiniteUnitary.time (generator q F p) (a*r+b)) := by
  intro d hd
  let Q : ℝ := 1+(|a|+|b|)*‖FullYSourceCutoffVolterra.cutoff q.cut‖
  have hQ : 1≤Q := by dsimp [Q];have := mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (norm_nonneg (FullYSourceCutoffVolterra.cutoff q.cut));linarith
  have lim : Tendsto (fun r : ℝ=>Real.exp (-d*r)*(57*Q^56*r^56)) atTop (𝓝 0) := by
    have h:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (56:ℕ) d hd
    simp only [Real.rpow_natCast] at h
    convert h.const_mul (57*Q^56) using 1
    · ext r;ac_rfl
    · simp
  refine squeeze_zero' (Filter.Eventually.of_forall (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))) ?_ lim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have harg : |a*r+b| *‖FullYSourceCutoffVolterra.cutoff q.cut‖≤Q*r := by
    have h:=abs_add_le (a*r) b
    rw [abs_mul,abs_of_nonneg (by linarith : 0≤r)] at h
    have hn:=norm_nonneg (FullYSourceCutoffVolterra.cutoff q.cut)
    calc
      _≤(|a| *r+|b|)*‖FullYSourceCutoffVolterra.cutoff q.cut‖ := mul_le_mul_of_nonneg_right h hn
      _≤(|a| *r+|b| *r)*‖FullYSourceCutoffVolterra.cutoff q.cut‖ := by
        apply mul_le_mul_of_nonneg_right _ hn
        exact add_le_add le_rfl (le_mul_of_one_le_right (abs_nonneg b) hr)
      _=((|a|+|b|)*‖FullYSourceCutoffVolterra.cutoff q.cut‖)*r := by ring
      _≤Q*r := mul_le_mul_of_nonneg_right (by dsimp [Q];linarith) (by linarith)
  have hp:=timeBound_polynomial q.cut (a*r+b) (Q*r) (by nlinarith) harg
  have ht:=full_time_bound p F q.cut (a*r+b)
  have bound : ‖SourceFiniteUnitary.time (generator q F p) (a*r+b)‖≤57*Q^56*r^56 := by
    exact ht.trans (by simpa only [mul_pow,mul_assoc] using hp)
  exact mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le

private def SourceSubexpPair (j : ℝ→SourceJet FieldOp) : Prop :=
  SourceSubexp (fun r=>(j r).value) ∧ SourceSubexp (fun r=>(j r).first)
private theorem subexp_jet_const (A : FieldOp) : SourceSubexpPair (fun _=>jetConst A) :=
  ⟨subexp_const A,subexp_const 0⟩
private theorem subexp_jet_mul {a b : ℝ→SourceJet FieldOp}
    (ha : SourceSubexpPair a) (hb : SourceSubexpPair b) : SourceSubexpPair (fun r=>jetMul (a r) (b r)) :=
  ⟨subexp_mul ha.1 hb.1,subexp_add (subexp_mul ha.2 hb.1) (subexp_mul ha.1 hb.2)⟩
private theorem subexp_jet_sub {a b : ℝ→SourceJet FieldOp}
    (ha : SourceSubexpPair a) (hb : SourceSubexpPair b) : SourceSubexpPair (fun r=>jetSub (a r) (b r)) := by
  constructor
  · change SourceSubexp (fun r=>(a r).value-(b r).value)
    simpa only [sub_eq_add_neg] using subexp_add ha.1 (subexp_neg hb.1)
  · change SourceSubexp (fun r=>(a r).first-(b r).first)
    simpa only [sub_eq_add_neg] using subexp_add ha.2 (subexp_neg hb.2)
private theorem subexp_jet_scale (c : ℂ) {a : ℝ→SourceJet FieldOp} (ha : SourceSubexpPair a) :
    SourceSubexpPair (fun r=>jetScale c (a r)) := by
  constructor
  · change SourceSubexp (fun r=>c • (a r).value)
    exact subexp_smul (𝕜:=ℂ) (E:=FieldOp) c ha.1
  · change SourceSubexp (fun r=>c • (a r).first)
    exact subexp_smul (𝕜:=ℂ) (E:=FieldOp) c ha.2
private theorem source_time_pair (q : SourceResponsePoint) (F : Index) (p : PhysicalMomentum) (a b : ℝ) :
    SourceSubexpPair (timeJet (generator q F p) a b) :=
  ⟨source_time_subexp q F p a b,
    subexp_smul (𝕜:=ℝ) (E:=FieldOp) a (subexp_mul (source_time_subexp q F p a b)
      (subexp_const ((-Complex.I) • generator q F p)))⟩
private theorem source_word_pair (q : SourceResponsePoint) (F : Index)
    (po pm pi : PhysicalMomentum) (A B : FieldOp) (ao bo am bm ai bi : ℝ) :
    SourceSubexpPair (wordJet (generator q F po) (generator q F pm) (generator q F pi)
      A B ao bo am bm ai bi) :=
  subexp_jet_mul (subexp_jet_mul (subexp_jet_mul (subexp_jet_mul
    (source_time_pair q F po ao bo) (subexp_jet_const A)) (source_time_pair q F pm am bm))
      (subexp_jet_const B)) (source_time_pair q F pi ai bi)
private theorem raw_action_subexp (q : SourceResponsePoint) (F : Index) (contact : Bool) (a b : Fin 97) :
    SourceSubexp (fun r=>(actionJet q F contact a b r).value) ∧
      SourceSubexp (fun r=>(actionJet q F contact a b r).first) := by
  have h : SourceSubexpPair (fun r=>if contact then rawContactJet q F a b r else rawKernelJet q F a b r) := by
    cases contact
    · simp only [Bool.false_eq_true,↓reduceIte]
      exact subexp_jet_scale _ (subexp_jet_sub
        (source_word_pair q F (q.p+q.k+q.ell) (q.p+q.k) q.p _ _ 0 (-q.age) (-1) 0 1 q.age)
        (source_word_pair q F (q.p+q.k+q.ell) (q.p+q.ell) q.p _ _ (-1) (-q.age) 1 0 0 q.age))
    · simp only [↓reduceIte]
      exact subexp_jet_mul (subexp_jet_mul (source_time_pair q F (q.p+q.k+q.ell) (-1) (-q.age))
        (subexp_jet_const _)) (source_time_pair q F q.p 1 q.age)
  exact ⟨subexp_map (sourcePairRead q) h.1,subexp_map (sourcePairRead q) h.2⟩

private theorem complex_weight_decay (f : ℝ→ℂ) (hf : SourceSubexp f) (lambda : ℂ)
    (positive : 0<lambda.re) : Tendsto (fun r=>laplaceWeight lambda r*f r) atTop (𝓝 0) := by
  have point (r : ℝ) : Real.exp (-lambda.re*r)*‖f r‖=‖laplaceWeight lambda r*f r‖ := by
    have weight : ‖laplaceWeight lambda r‖=Real.exp (-lambda.re*r) := by
      simp only [laplaceWeight,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
        Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,neg_mul]
    exact ((norm_mul (laplaceWeight lambda r) (f r)).trans
      (congrArg (fun x=>x*‖f r‖) weight)).symm
  have hn:=Filter.Tendsto.congr (f₁:=fun r=>Real.exp (-lambda.re*r)*‖f r‖)
    (f₂:=fun r=>‖laplaceWeight lambda r*f r‖) point (hf lambda.re positive)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

theorem actual_initial_cosource_decay (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (a b : Fin 97) (lambda : ℂ) (positive : 0<lambda.re) (d : Fin 3) :
    Tendsto (fun r=>laplaceWeight lambda r*initialCoSource lambda (actionJet q F contact a b r) d)
      atTop (𝓝 0) := by
  have h : SourceSubexp (fun r=>initialCoSource lambda (actionJet q F contact a b r) d) := by
    have source:=raw_action_subexp q F contact a b
    fin_cases d
    · exact subexp_const 0
    · exact source.1
    · exact subexp_add (subexp_mul (subexp_const lambda) source.1) source.2
  exact complex_weight_decay _ h lambda positive


def preparedMomentum (q : SourceResponsePoint) (lambda : ℂ) : Fin 4→ℂ :=
  Fin.cases lambda (physicalSpatial q)

def preparedLaplaceSource (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) : Fin 289→ℂ :=
  injectSource (fun a=>∫ r in (0:ℝ)..time,
    laplaceWeight lambda r*(actionJet q F contact a b r).value)

private def ContinuousTriple {E : Type*} [TopologicalSpace E] (j : ℝ→SourceJet E) : Prop :=
  Continuous (fun r=>(j r).value) ∧ Continuous (fun r=>(j r).first) ∧ Continuous (fun r=>(j r).second)

private theorem continuous_jet_mul (a b : ℝ→SourceJet FieldOp)
    (ha : ContinuousTriple a) (hb : ContinuousTriple b) :
    ContinuousTriple (fun r=>jetMul (a r) (b r)) :=
  ⟨ha.1.mul hb.1,(ha.2.1.mul hb.1).add (ha.1.mul hb.2.1),
    ((ha.2.2.mul hb.1).add (ha.2.1.mul hb.2.1)).add
      ((ha.2.1.mul hb.2.1).add (ha.1.mul hb.2.2))⟩

private theorem continuous_jet_const (A : FieldOp) : ContinuousTriple (fun _=>jetConst A) :=
  ⟨continuous_const,continuous_const,continuous_const⟩

private theorem continuous_time_jet (C : FieldOp) (rate shift : ℝ) :
    ContinuousTriple (timeJet C rate shift) := by
  have h : Continuous (fun r : ℝ=>SourceFiniteUnitary.time C (rate*r+shift)) :=
    (PreparationVacuumActualPreparedMixed.source_time_continuous C).comp (by fun_prop)
  exact ⟨h,(h.mul continuous_const).const_smul rate,
    (((h.mul continuous_const).const_smul rate).mul continuous_const).const_smul rate⟩

private theorem continuous_word_jet (Co Cm Ci A B : FieldOp) (ao bo am bm ai bi : ℝ) :
    ContinuousTriple (wordJet Co Cm Ci A B ao bo am bm ai bi) :=
  continuous_jet_mul _ _ (continuous_jet_mul _ _ (continuous_jet_mul _ _
    (continuous_jet_mul _ _ (continuous_time_jet Co ao bo) (continuous_jet_const A))
      (continuous_time_jet Cm am bm)) (continuous_jet_const B)) (continuous_time_jet Ci ai bi)

private theorem continuous_raw_kernel (q : SourceResponsePoint) (F : Index) (a b : Fin 97) :
    ContinuousTriple (rawKernelJet q F a b) := by
  have hf:=continuous_word_jet (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.ell)) (generator q F q.p)
    (rawGauss false (sourceFieldUnit a) (sourceFieldUnit b) (q.p+q.ell) q.phi)
    (PreparationVacuumSourceFieldFamily.localizedGauss (sourceFieldUnit b) q.p q.psi) (-1) (-q.age) 1 0 0 q.age
  have hr:=continuous_word_jet (generator q F (q.p+q.k+q.ell)) (generator q F (q.p+q.k)) (generator q F q.p)
    (PreparationVacuumSourceFieldFamily.localizedGauss (sourceFieldUnit b) (q.p+q.k) q.psi)
    (rawGauss false (sourceFieldUnit a) (sourceFieldUnit b) q.p q.phi) 0 (-q.age) (-1) 0 1 q.age
  exact ⟨(hr.1.sub hf.1).const_smul (-Complex.I),(hr.2.1.sub hf.2.1).const_smul (-Complex.I),
    (hr.2.2.sub hf.2.2).const_smul (-Complex.I)⟩

private theorem continuous_raw_contact (q : SourceResponsePoint) (F : Index) (a b : Fin 97) :
    ContinuousTriple (rawContactJet q F a b) :=
  continuous_jet_mul _ _ (continuous_jet_mul _ _
    (continuous_time_jet (generator q F (q.p+q.k+q.ell)) (-1) (-q.age))
    (continuous_jet_const (rawGauss true (sourceFieldUnit a) (sourceFieldUnit b) q.p
      (PreparationVacuumCausalFieldResponse.contactLocalizer q.phi q.psi))))
    (continuous_time_jet (generator q F q.p) 1 q.age)

private theorem continuous_action_jet (q : SourceResponsePoint) (F : Index) (contact : Bool) (a b : Fin 97) :
    ContinuousTriple (actionJet q F contact a b) := by
  cases contact
  · have h:=continuous_raw_kernel q F a b
    exact ⟨(sourcePairRead q).continuous.comp h.1,(sourcePairRead q).continuous.comp h.2.1,
      (sourcePairRead q).continuous.comp h.2.2⟩
  · have h:=continuous_raw_contact q F a b
    exact ⟨(sourcePairRead q).continuous.comp h.1,(sourcePairRead q).continuous.comp h.2.1,
      (sourcePairRead q).continuous.comp h.2.2⟩

private theorem actual_jet_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (a b : Fin 97) (d : Fin 3) : Continuous (fun r=>jetEntry (actionJet q F contact a b r) d) := by
  have h:=continuous_action_jet q F contact a b
  fin_cases d
  · exact h.1
  · exact h.2.1
  · exact h.2.2

def sourceBoundaryJet (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) (d : Fin 3) : ℂ :=
  injectSource (fun a=>laplaceWeight lambda r*initialCoSource lambda (actionJet q F contact a b r) d) row

def sourceDerivativeJet (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) (d : Fin 3) : ℂ :=
  injectSource (fun a=>laplaceWeight lambda r*(jetEntry (actionJet q F contact a b r) d-
    lambda^d.val*(actionJet q F contact a b r).value)) row

theorem actual_source_boundary_derivative (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (t : ℝ) (row : Fin 289) (d : Fin 3) :
    HasDerivAt (fun r=>sourceBoundaryJet q F contact b lambda r row d)
      (sourceDerivativeJet q F contact b lambda t row d) t := by
  unfold sourceBoundaryJet sourceDerivativeJet injectSource
  apply HasDerivAt.fun_sum
  intro a _
  by_cases h : row=sourceSlot a
  · simp only [if_pos h]
    exact actual_green_boundary q F contact a b lambda t d
  · simp only [if_neg h]
    exact hasDerivAt_const t 0

theorem actual_source_derivative_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (row : Fin 289) (d : Fin 3) :
    Continuous (fun r=>sourceDerivativeJet q F contact b lambda r row d) := by
  unfold sourceDerivativeJet injectSource
  apply continuous_finsetSum
  intro a _
  by_cases h : row=sourceSlot a
  · simp only [if_pos h]
    have hv:=actual_jet_continuous q F contact a b 0
    change Continuous (fun r=>(actionJet q F contact a b r).value) at hv
    have hw : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
    exact hw.mul ((actual_jet_continuous q F contact a b d).sub (hv.const_mul _))
  · simp only [if_neg h]
    exact continuous_const

def nativeReadbackTerms : List SourceTerm := reflectedTerms originalChangeTerms

private theorem native_time_order : nativeReadbackTerms.all (fun a=>decide (a.powers.temporal < 3))=true := by
  decide +kernel

def nativeTimeOrder (a : {a // a∈nativeReadbackTerms}) : Fin 3 :=
  ⟨a.val.powers.temporal,of_decide_eq_true (List.all_eq_true.mp native_time_order a.val a.property)⟩

def spatialCoefficient (q : SourceResponsePoint) (a : SourceTerm) : ℂ :=
  coefficientValue a.coefficient*(physicalSpatial q 0)^a.powers.first*
    (physicalSpatial q 1)^a.powers.second*(physicalSpatial q 2)^a.powers.third

def nativeBoundary (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
    sourceBoundaryJet q F contact b lambda r a.val.column (nativeTimeOrder a) else 0)).sum

def nativeDifference (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
    sourceDerivativeJet q F contact b lambda r a.val.column (nativeTimeOrder a) else 0)).sum

private theorem derivative_list_sum {ι : Type*} (entries : List ι) (f df : ι→ℝ→ℂ) (t : ℝ)
    (h : ∀ a∈entries,HasDerivAt (f a) (df a t) t) :
    HasDerivAt (fun r=>(entries.map (fun a=>f a r)).sum) ((entries.map (fun a=>df a t)).sum) t := by
  induction entries with
  | nil=>exact hasDerivAt_const t 0
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons] using!
      (h a (by simp)).add (ih (fun b hb=>h b (by simp [hb])))

private theorem continuous_list_sum {ι : Type*} (entries : List ι) (f : ι→ℝ→ℂ)
    (h : ∀ a∈entries,Continuous (f a)) : Continuous (fun r=>(entries.map (fun a=>f a r)).sum) := by
  induction entries with
  | nil=>exact continuous_const
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons] using!
      (h a (by simp)).add (ih (fun b hb=>h b (by simp [hb])))

theorem native_boundary_generated (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>nativeBoundary q F contact b lambda r row)
      (nativeDifference q F contact b lambda t row) t := by
  unfold nativeBoundary nativeDifference
  convert! derivative_list_sum nativeReadbackTerms.attach
    (fun a r=>if row=a.val.row then spatialCoefficient q a.val*
      sourceBoundaryJet q F contact b lambda r a.val.column (nativeTimeOrder a) else 0)
    (fun a r=>if row=a.val.row then spatialCoefficient q a.val*
      sourceDerivativeJet q F contact b lambda r a.val.column (nativeTimeOrder a) else 0) t (by
    intro a _
    by_cases h : row=a.val.row
    · simp only [if_pos h]
      exact (actual_source_boundary_derivative q F contact b lambda t _ _).const_mul _
    · simp only [if_neg h]
      exact hasDerivAt_const t 0) using 1

theorem native_difference_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (row : Fin 289) :
    Continuous (fun r=>nativeDifference q F contact b lambda r row) := by
  unfold nativeDifference
  apply continuous_list_sum
  intro a _
  by_cases h : row=a.val.row
  · simp only [if_pos h]
    exact (actual_source_derivative_continuous q F contact b lambda _ _).const_mul _
  · simp only [if_neg h]
    exact continuous_const

/-- Original full F(-D)^T, actual time jets, and both endpoint co-sources.
This retains the terminal source instead of turning a finite window into a
zero-past infinite-time solution. -/
theorem native_window_boundary (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    (∫ r in (0:ℝ)..time,nativeDifference q F contact b lambda r row)=
      nativeBoundary q F contact b lambda time row-nativeBoundary q F contact b lambda 0 row :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>native_boundary_generated q F contact b lambda t row)
    ((native_difference_continuous q F contact b lambda row).intervalIntegrable _ _)


private theorem inject_source_mul (c : ℂ) (x : Fin 97→ℂ) (row : Fin 289) :
    injectSource (fun a=>c*x a) row=c*injectSource x row := by
  unfold injectSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

private theorem inject_source_sub (x y : Fin 97→ℂ) (row : Fin 289) :
    injectSource (fun a=>x a-y a) row=injectSource x row-injectSource y row := by
  unfold injectSource
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

def preparedCurrent (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97) (r : ℝ) : Fin 289→ℂ :=
  injectSource (fun a=>(actionJet q F contact a b r).value)

def sourceJetValue (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97) (r : ℝ)
    (row : Fin 289) (d : Fin 3) : ℂ := injectSource (fun a=>jetEntry (actionJet q F contact a b r) d) row

theorem source_derivative_difference (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (r : ℝ) (row : Fin 289) (d : Fin 3) :
    sourceDerivativeJet q F contact b lambda r row d=
      laplaceWeight lambda r*(sourceJetValue q F contact b r row d-lambda^d.val*preparedCurrent q F contact b r row) := by
  unfold sourceDerivativeJet sourceJetValue preparedCurrent
  rw [inject_source_mul,inject_source_sub,inject_source_mul]

def nativeFrequency (q : SourceResponsePoint) (lambda : ℂ) (current : Fin 289→ℂ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then
    spatialCoefficient q a.val*lambda^a.val.powers.temporal*current a.val.column else 0)).sum

def nativeTimeSource (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (r : ℝ) (row : Fin 289) : ℂ :=
  (nativeReadbackTerms.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
    sourceJetValue q F contact b r a.val.column (nativeTimeOrder a) else 0)).sum

private theorem sum_weighted_difference {ι : Type*} (ts : List ι) (left right : ι→ℂ) (weight : ℂ) :
    (ts.map (fun a=>weight*(left a-right a))).sum=
      weight*((ts.map left).sum-(ts.map right).sum) := by
  induction ts with
  | nil=>simp
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem native_difference_source (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (r : ℝ) (row : Fin 289) :
    nativeDifference q F contact b lambda r row=laplaceWeight lambda r*
      (nativeTimeSource q F contact b r row-nativeFrequency q lambda (preparedCurrent q F contact b r) row) := by
  unfold nativeDifference nativeTimeSource nativeFrequency
  rw [←sum_weighted_difference]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [source_derivative_difference]
  split_ifs
  · dsimp only [nativeTimeOrder]
    ring
  · ring

theorem sourceMatrix_mulVec (ts : List SourceTerm) (p : Fin 4→ℂ) (v : Fin 289→ℂ) (row : Fin 289) :
    (sourceMatrix ts p *ᵥ v) row=
      (ts.map (fun a=>if row=a.row then coefficientValue a.coefficient*a.powers.value p*v a.column else 0)).sum := by
  induction ts with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    rw [sourceMatrix_cons,Matrix.add_mulVec]
    simp [SourceTerm.matrix,Matrix.single_mulVec,Function.update_apply,ih]

private theorem spatial_source_value (q : SourceResponsePoint) (lambda : ℂ) (a : SourceTerm) :
    spatialCoefficient q a*lambda^a.powers.temporal=
      coefficientValue a.coefficient*a.powers.value (preparedMomentum q lambda) := by
  simp only [spatialCoefficient,Powers.value,preparedMomentum]
  change _=coefficientValue a.coefficient*(lambda^a.powers.temporal*
    (physicalSpatial q 0)^a.powers.first*(physicalSpatial q 1)^a.powers.second*(physicalSpatial q 2)^a.powers.third)
  ring

private theorem map_attached_values {α β : Type*} (ts : List α) (f : α→β) :
    ts.attach.map (fun a=>f a.val)=ts.map f := by
  have h:=congrArg (List.map f) (List.attach_map_subtype_val ts)
  simpa only [List.map_map] using! h

theorem native_frequency_original (q : SourceResponsePoint) (lambda : ℂ) (current : Fin 289→ℂ) (row : Fin 289) :
    nativeFrequency q lambda current row=(originalReadback (preparedMomentum q lambda) *ᵥ current) row := by
  let f : SourceTerm→ℂ:=fun a=>if row=a.row then
    spatialCoefficient q a*lambda^a.powers.temporal*current a.column else 0
  let g : SourceTerm→ℂ:=fun a=>if row=a.row then
    coefficientValue a.coefficient*a.powers.value (preparedMomentum q lambda)*current a.column else 0
  have step (a : SourceTerm) : f a=g a := by
    dsimp [f,g]
    by_cases same : row=a.row
    · simp only [if_pos same];rw [spatial_source_value]
    · simp only [if_neg same]
  have maps : nativeReadbackTerms.attach.map (fun a=>f a.val)=
      nativeReadbackTerms.attach.map (fun a=>g a.val) := List.map_congr_left (fun a _=>step a.val)
  have reflected : sourceMatrix nativeReadbackTerms (preparedMomentum q lambda)=
      originalReadback (preparedMomentum q lambda) := reflectedTerms_value originalChangeTerms _
  calc
    _=(nativeReadbackTerms.attach.map (fun a=>f a.val)).sum := rfl
    _=(nativeReadbackTerms.attach.map (fun a=>g a.val)).sum := congrArg List.sum maps
    _=(nativeReadbackTerms.map g).sum := congrArg List.sum (map_attached_values nativeReadbackTerms g)
    _=(sourceMatrix nativeReadbackTerms (preparedMomentum q lambda) *ᵥ current) row :=
      (sourceMatrix_mulVec nativeReadbackTerms (preparedMomentum q lambda) current row).symm
    _=_ := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ=>(M *ᵥ current) row) reflected


/-- Actual F(-D)^T minus the same F(-lambda)^T, with its generated two endpoints. -/
theorem actual_source_window_readback (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    (∫ r in (0:ℝ)..time,laplaceWeight lambda r*(nativeTimeSource q F contact b r row-
      (originalReadback (preparedMomentum q lambda) *ᵥ preparedCurrent q F contact b r) row))=
        nativeBoundary q F contact b lambda time row-nativeBoundary q F contact b lambda 0 row := by
  have h:=native_window_boundary q F contact b lambda time row
  simpa only [native_difference_source,native_frequency_original] using h

theorem prepared_source_integral (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    preparedLaplaceSource q F contact b lambda time row=
      ∫ r in (0:ℝ)..time,laplaceWeight lambda r*preparedCurrent q F contact b r row := by
  have hw : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  have hInt (a : Fin 97) : IntervalIntegrable
      (fun r=>if row=sourceSlot a then laplaceWeight lambda r*(actionJet q F contact a b r).value else 0)
      MeasureTheory.volume 0 time := by
    by_cases h : row=sourceSlot a
    · simp only [if_pos h]
      have hc:=actual_jet_continuous q F contact a b 0
      change Continuous (fun r=>(actionJet q F contact a b r).value) at hc
      exact (hw.mul hc).intervalIntegrable _ _
    · simp only [if_neg h]
      exact intervalIntegrable_const
  unfold preparedLaplaceSource preparedCurrent
  simp_rw [←inject_source_mul]
  unfold injectSource
  rw [intervalIntegral.integral_finsetSum (fun a _=>hInt a)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : row=sourceSlot a <;> simp [h]

theorem source_jet_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (row : Fin 289) (d : Fin 3) :
    Continuous (fun r=>sourceJetValue q F contact b r row d) := by
  unfold sourceJetValue injectSource
  apply continuous_finsetSum
  intro a _
  by_cases h : row=sourceSlot a
  · simp only [if_pos h]
    exact actual_jet_continuous q F contact a b d
  · simp only [if_neg h]
    exact continuous_const

theorem prepared_current_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (row : Fin 289) : Continuous (fun r=>preparedCurrent q F contact b r row) :=
  source_jet_continuous q F contact b row 0

theorem native_time_continuous (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (row : Fin 289) : Continuous (fun r=>nativeTimeSource q F contact b r row) := by
  unfold nativeTimeSource
  apply continuous_list_sum
  intro a _
  by_cases h : row=a.val.row
  · simp only [if_pos h]
    exact (source_jet_continuous q F contact b _ _).const_mul _
  · simp only [if_neg h]
    exact continuous_const

theorem prepared_readback_integral (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    (originalReadback (preparedMomentum q lambda) *ᵥ preparedLaplaceSource q F contact b lambda time) row=
      ∫ r in (0:ℝ)..time,laplaceWeight lambda r*
        (originalReadback (preparedMomentum q lambda) *ᵥ preparedCurrent q F contact b r) row := by
  have hw : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  change (∑ j,originalReadback (preparedMomentum q lambda) row j*
    preparedLaplaceSource q F contact b lambda time j)=_
  simp_rw [prepared_source_integral,←intervalIntegral.integral_const_mul]
  have hs:=intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=MeasureTheory.volume)
    (f:=fun (j : Fin 289) r=>originalReadback (preparedMomentum q lambda) row j*
      (laplaceWeight lambda r*preparedCurrent q F contact b r j))
    (fun j _=>((hw.mul (prepared_current_continuous q F contact b j)).const_mul
      (originalReadback (preparedMomentum q lambda) row j)).intervalIntegrable 0 time)
  refine hs.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro r _
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The original source ports are fed by actual time jets and both generated
co-sources before the active Green inverse is applied. -/
theorem prepared_readback_cosources (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    (originalReadback (preparedMomentum q lambda) *ᵥ preparedLaplaceSource q F contact b lambda time) row=
      (∫ r in (0:ℝ)..time,laplaceWeight lambda r*nativeTimeSource q F contact b r row)-
        (nativeBoundary q F contact b lambda time row-nativeBoundary q F contact b lambda 0 row) := by
  have hw : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  have hread : Continuous (fun r=>(originalReadback (preparedMomentum q lambda) *ᵥ
      preparedCurrent q F contact b r) row) := by
    change Continuous (fun r=>∑ j,originalReadback (preparedMomentum q lambda) row j*
      preparedCurrent q F contact b r j)
    apply continuous_finsetSum
    intro j _
    exact (prepared_current_continuous q F contact b j).const_mul _
  have h:=actual_source_window_readback q F contact b lambda time row
  simp_rw [mul_sub] at h
  have hi:=intervalIntegral.integral_sub (μ:=MeasureTheory.volume)
    (f:=fun r=>laplaceWeight lambda r*nativeTimeSource q F contact b r row)
    (g:=fun r=>laplaceWeight lambda r*
      (originalReadback (preparedMomentum q lambda) *ᵥ preparedCurrent q F contact b r) row)
    ((hw.mul (native_time_continuous q F contact b row)).intervalIntegrable 0 time)
    ((hw.mul hread).intervalIntegrable 0 time)
  rw [hi,←prepared_readback_integral] at h
  exact (eq_sub_iff_add_eq.mpr (by linear_combination -h))

noncomputable def auxiliaryTerms : List SourceTerm :=
  productTerms (productTerms originalChangeTerms contactInverseTerms) nativeReadbackTerms

private def timeColumnDegree (i : Fin 289) : ℕ :=
  ([1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,2,1,2,2,1,2,2,2,1,0,1,1,0,1,1,0,1,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,1,0,1,1,0,1,1,0,1,1,0,1,1,0,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]:List ℕ).getD i.val 0
private theorem change_degree : originalChangeTerms.all
    (fun a=>decide (a.powers.temporal≤timeColumnDegree a.column))=true := by decide +kernel
private theorem reflected_degree : nativeReadbackTerms.all
    (fun a=>decide (a.powers.temporal≤timeColumnDegree a.row))=true := by decide +kernel
private theorem contact_degree : contactInverseTerms.all
    (fun a=>decide (timeColumnDegree a.row+a.powers.temporal+timeColumnDegree a.column<3))=true := by decide +kernel

private theorem row_property (a : SourceTerm) (bs : List SourceTerm) (P : SourceTerm→Prop)
    (h : ∀ b∈bs,a.column=b.row→P ⟨a.row,b.column,a.powers.join b.powers,a.coefficient*b.coefficient⟩) :
    ∀ c∈rowProduct a bs,P c := by
  induction bs with
  | nil=>simp [rowProduct]
  | cons b rest ih=>
    have tail := ih (fun d hd=>h d (by simp [hd]))
    change ∀ c∈(if a.column=b.row then
      ⟨a.row,b.column,a.powers.join b.powers,a.coefficient*b.coefficient⟩::rowProduct a rest
      else rowProduct a rest),P c
    split_ifs with same
    · intro c hc
      rcases List.mem_cons.mp hc with eq|mem
      · subst c;exact h b (by simp) same
      · exact tail c mem
    · exact tail
private theorem product_property (as bs : List SourceTerm) (P : SourceTerm→Prop)
    (h : ∀ a∈as,∀ b∈bs,a.column=b.row→P ⟨a.row,b.column,a.powers.join b.powers,a.coefficient*b.coefficient⟩) :
    ∀ c∈productTerms as bs,P c := by
  induction as with
  | nil=>simp [productTerms]
  | cons a rest ih=>
    intro c hc
    change c∈rowProduct a bs++productTerms rest bs at hc
    rcases List.mem_append.mp hc with head|tail
    · exact row_property a bs P (h a (by simp)) c head
    · exact ih (fun a ha=>h a (by simp [ha])) c tail
private theorem auxiliary_time_bound : ∀ a∈auxiliaryTerms,a.powers.temporal<3 := by
  have first : ∀ a∈productTerms originalChangeTerms contactInverseTerms,
      a.powers.temporal+timeColumnDegree a.column<3 := by
    apply product_property
    intro a ha b hb same
    have fa:=of_decide_eq_true (List.all_eq_true.mp change_degree a ha)
    have db:=of_decide_eq_true (List.all_eq_true.mp contact_degree b hb)
    change a.powers.temporal+b.powers.temporal+timeColumnDegree b.column<3
    rw [same] at fa
    omega
  apply product_property
  intro a ha b hb same
  have fa:=first a ha
  have fb:=of_decide_eq_true (List.all_eq_true.mp reflected_degree b hb)
  change a.powers.temporal+b.powers.temporal<3
  rw [same] at fa
  omega

def auxiliaryTimeOrder (a : {a // a∈auxiliaryTerms}) : Fin 3 :=
  ⟨a.val.powers.temporal,auxiliary_time_bound a.val a.property⟩

theorem auxiliary_matrix_original (p : Fin 4→ℂ) :
    sourceMatrix auxiliaryTerms p=originalChange p*contactInverse p*originalReadback p := by
  calc
    _=sourceMatrix (productTerms originalChangeTerms contactInverseTerms) p*sourceMatrix nativeReadbackTerms p :=
      productTerms_value _ _ p
    _=(sourceMatrix originalChangeTerms p*sourceMatrix contactInverseTerms p)*sourceMatrix nativeReadbackTerms p :=
      congrArg (fun M=>M*sourceMatrix nativeReadbackTerms p) (productTerms_value originalChangeTerms contactInverseTerms p)
    _=_ := congrArg (fun M=>originalChange p*contactInverse p*M) (reflectedTerms_value originalChangeTerms p)


def auxiliaryBoundary (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ :=
  (auxiliaryTerms.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
    sourceBoundaryJet q F contact b lambda r a.val.column (auxiliaryTimeOrder a) else 0)).sum

def auxiliaryDifference (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : ℂ) (r : ℝ) (row : Fin 289) : ℂ :=
  (auxiliaryTerms.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
    sourceDerivativeJet q F contact b lambda r a.val.column (auxiliaryTimeOrder a) else 0)).sum

theorem auxiliary_boundary_generated (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (t : ℝ) (row : Fin 289) :
    HasDerivAt (fun r=>auxiliaryBoundary q F contact b lambda r row)
      (auxiliaryDifference q F contact b lambda t row) t := by
  convert! derivative_list_sum auxiliaryTerms.attach
    (fun a r=>if row=a.val.row then spatialCoefficient q a.val*
      sourceBoundaryJet q F contact b lambda r a.val.column (auxiliaryTimeOrder a) else 0)
    (fun a r=>if row=a.val.row then spatialCoefficient q a.val*
      sourceDerivativeJet q F contact b lambda r a.val.column (auxiliaryTimeOrder a) else 0) t (by
    intro a _
    by_cases h : row=a.val.row
    · simp only [if_pos h]
      exact (actual_source_boundary_derivative q F contact b lambda t _ _).const_mul _
    · simp only [if_neg h]
      exact hasDerivAt_const t 0) using 1

theorem auxiliary_window_boundary (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (time : ℝ) (row : Fin 289) :
    (∫ r in (0:ℝ)..time,auxiliaryDifference q F contact b lambda r row)=
      auxiliaryBoundary q F contact b lambda time row-auxiliaryBoundary q F contact b lambda 0 row := by
  have hc : Continuous (fun r=>auxiliaryDifference q F contact b lambda r row) := by
    unfold auxiliaryDifference
    apply continuous_list_sum
    intro a _
    by_cases h : row=a.val.row
    · simp only [if_pos h]
      exact (actual_source_derivative_continuous q F contact b lambda _ _).const_mul _
    · simp only [if_neg h]
      exact continuous_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>auxiliary_boundary_generated q F contact b lambda t row) (hc.intervalIntegrable _ _)


theorem source_boundary_decay (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) (d : Fin 3) :
    Tendsto (fun r=>sourceBoundaryJet q F contact b lambda r row d) atTop (𝓝 0) := by
  unfold sourceBoundaryJet injectSource
  have h (a : Fin 97) (_ha : a∈Finset.univ) :
      Tendsto (fun r=>if row=sourceSlot a then laplaceWeight lambda r*
        initialCoSource lambda (actionJet q F contact a b r) d else 0) atTop (𝓝 0) := by
    by_cases same : row=sourceSlot a
    · simpa only [if_pos same] using actual_initial_cosource_decay q F contact a b lambda positive d
    · simp only [if_neg same];exact tendsto_const_nhds
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum
    (f:=fun (a : Fin 97) r=>if row=sourceSlot a then laplaceWeight lambda r*
      initialCoSource lambda (actionJet q F contact a b r) d else 0)
    (a:=fun _=>0) Finset.univ h

private theorem zero_list_sum {ι : Type*} (ts : List ι) : (ts.map (fun _=>(0:ℂ))).sum=0 := by
  induction ts with
  | nil=>rfl
  | cons a rest ih=>simp only [List.map_cons,List.sum_cons,zero_add,ih]

private theorem source_table_terminal (ts : List SourceTerm) (order : {a // a∈ts}→Fin 3)
    (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97) (lambda : ℂ)
    (positive : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun r=>(ts.attach.map (fun a=>if row=a.val.row then spatialCoefficient q a.val*
      sourceBoundaryJet q F contact b lambda r a.val.column (order a) else 0)).sum) atTop (𝓝 0) := by
  have h (a : {a // a∈ts}) (_ha : a∈ts.attach) :
      Tendsto (fun r=>if row=a.val.row then spatialCoefficient q a.val*
        sourceBoundaryJet q F contact b lambda r a.val.column (order a) else 0) atTop (𝓝 0) := by
    by_cases same : row=a.val.row
    · simpa only [if_pos same,mul_zero] using
        (source_boundary_decay q F contact b lambda positive a.val.column (order a)).const_mul (spatialCoefficient q a.val)
    · simp only [if_neg same];exact tendsto_const_nhds
  simpa only [zero_list_sum] using tendsto_list_sum
    (f:=fun (a : {a // a∈ts}) r=>if row=a.val.row then spatialCoefficient q a.val*
      sourceBoundaryJet q F contact b lambda r a.val.column (order a) else 0)
    (a:=fun _=>0) ts.attach h

theorem native_terminal_decay (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun r=>nativeBoundary q F contact b lambda r row) atTop (𝓝 0) :=
  source_table_terminal nativeReadbackTerms nativeTimeOrder q F contact b lambda positive row

theorem auxiliary_terminal_decay (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun r=>auxiliaryBoundary q F contact b lambda r row) atTop (𝓝 0) :=
  source_table_terminal auxiliaryTerms auxiliaryTimeOrder q F contact b lambda positive row

/-- Finite-integral-first positive-damping return, retaining the actual initial co-source. -/
theorem native_source_window_limit (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun T=>∫ r in (0:ℝ)..T,laplaceWeight lambda r*(nativeTimeSource q F contact b r row-
      (originalReadback (preparedMomentum q lambda) *ᵥ preparedCurrent q F contact b r) row)) atTop
        (𝓝 (-nativeBoundary q F contact b lambda 0 row)) := by
  simp_rw [actual_source_window_readback]
  simpa only [zero_sub] using (native_terminal_decay q F contact b lambda positive row).sub_const
    (nativeBoundary q F contact b lambda 0 row)

def eulerField (p : regularSource) (current : Fin 289→ℂ) : Fin 289→ℂ := sourceField p (-current)

/-- The original action equation has H·field + current = 0; the current is
moved with its original minus sign, after the raw 4W reader has been formed. -/
theorem original_euler_field (p : regularSource) (current : Fin 289→ℂ) :
    originalJacobi p.val *ᵥ eulerField p current+current=
      originalRowLift p.val *ᵥ sourceCompatibility p.val current := by
  have h:=original_forced_field p (-current)
  simp only [sourceCompatibility,Matrix.mulVec_neg,sub_neg_eq_add] at h
  change originalJacobi p.val *ᵥ sourceField p (-current)+current=_
  rw [h]
  unfold sourceCompatibility
  abel

def preparedSpectralDomain (q : SourceResponsePoint) : Set ℂ :=
  {lambda | preparedMomentum q lambda∈regularSource}

def preparedEulerField (q : SourceResponsePoint) (F : Index) (contact : Bool) (b : Fin 97)
    (lambda : preparedSpectralDomain q) (time : ℝ) : Fin 289→ℂ :=
  eulerField ⟨preparedMomentum q lambda.val,lambda.property⟩
    (preparedLaplaceSource q F contact b lambda.val time)

theorem prepared_original_equation (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : preparedSpectralDomain q) (time : ℝ) :
    originalJacobi (preparedMomentum q lambda.val) *ᵥ preparedEulerField q F contact b lambda time+
      preparedLaplaceSource q F contact b lambda.val time=
        originalRowLift (preparedMomentum q lambda.val) *ᵥ sourceCompatibility (preparedMomentum q lambda.val)
          (preparedLaplaceSource q F contact b lambda.val time) :=
  original_euler_field ⟨preparedMomentum q lambda.val,lambda.property⟩ _

/-- Actual two-order raw current/contact drives the original Green through
its source time derivatives and generated initial/terminal co-sources. -/
theorem prepared_green_cosources (q : SourceResponsePoint) (F : Index) (contact : Bool)
    (b : Fin 97) (lambda : preparedSpectralDomain q) (time : ℝ) :
    preparedEulerField q F contact b lambda time=
      -(originalChange (preparedMomentum q lambda.val) *ᵥ
        ((contactInverse (preparedMomentum q lambda.val)+
          activeProjection*(extendedKernel (preparedMomentum q lambda.val))⁻¹) *ᵥ
          (fun row=>(∫ r in (0:ℝ)..time,
            laplaceWeight lambda.val r*nativeTimeSource q F contact b r row)-
            (nativeBoundary q F contact b lambda.val time row-nativeBoundary q F contact b lambda.val 0 row)))) := by
  have hread : originalReadback (preparedMomentum q lambda.val) *ᵥ
      preparedLaplaceSource q F contact b lambda.val time=
      (fun row=>(∫ r in (0:ℝ)..time,
        laplaceWeight lambda.val r*nativeTimeSource q F contact b r row)-
        (nativeBoundary q F contact b lambda.val time row-nativeBoundary q F contact b lambda.val 0 row)) :=
    funext (prepared_readback_cosources q F contact b lambda.val time)
  change (originalChange (preparedMomentum q lambda.val)*
    (contactInverse (preparedMomentum q lambda.val)+activeProjection*(extendedKernel (preparedMomentum q lambda.val))⁻¹)*
    originalReadback (preparedMomentum q lambda.val)) *ᵥ
      (-preparedLaplaceSource q F contact b lambda.val time)=_
  rw [Matrix.mulVec_neg,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hread]

end LowEnergy.PreparationVacuumOriginalGreenFeedback
