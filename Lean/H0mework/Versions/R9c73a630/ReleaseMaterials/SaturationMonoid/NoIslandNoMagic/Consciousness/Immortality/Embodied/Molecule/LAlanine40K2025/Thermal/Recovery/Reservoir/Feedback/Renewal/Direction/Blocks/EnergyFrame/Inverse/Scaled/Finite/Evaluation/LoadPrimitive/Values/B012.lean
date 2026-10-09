import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B008

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v193_pa : Scalar.QComplex := ((999950368742740209978772436238 : Int)/10^30,(9962933867987022576281979990 : Int)/10^30)
theorem v193_pa_checked : Scalar.distance (sourceCoefficient 2 3 1 0) v193_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v193_pb : Scalar.QComplex := ((4298779672198133129026452 : Int)/10^30,(-431455871866268850087357467 : Int)/10^30)
theorem v193_pb_checked : Scalar.distance (sourceCoefficient 2 3 1 1) v193_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v193_pg : Scalar.QComplex := ((-93081784619882479324597 : Int)/10^30,(-927413693189693647342 : Int)/10^30)
theorem v193_pg_checked : Scalar.distance (sourceCoefficient 2 3 1 2) v193_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v193_mb : Scalar.QComplex := ((3926451086196524427349636 : Int)/10^30,(-431459420868776504505670571 : Int)/10^30)
theorem v193_mb_checked : Scalar.distance (sourceCoefficient 2 3 3 1) v193_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v193_mg : Scalar.QComplex := ((-93082550277528078139539 : Int)/10^30,(-847087959992187913768 : Int)/10^30)
theorem v193_mg_checked : Scalar.distance (sourceCoefficient 2 3 3 2) v193_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v193_upper : Scalar.QComplex := ((999966074554154234696860900596 : Int)/10^30,(8237095407706212329685332539 : Int)/10^30)
theorem v193_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 3 5) 1) 14) v193_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material193 : Material (2 : Basis) (3 : Basis) where
  plus := ![v193_pa,v193_pb,v193_pg]
  minus := ![(Primitive.Addresses.material193 1).one,v193_mb,v193_mg]
  upper := v193_upper
  lower := (Primitive.Addresses.material193 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v193_pa_checked.trans (by decide +kernel)
    · exact v193_pb_checked.trans (by decide +kernel)
    · exact v193_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 3 Primitive.Addresses.material193
    · exact v193_mb_checked.trans (by decide +kernel)
    · exact v193_mg_checked.trans (by decide +kernel)
  upper_error := v193_upper_checked
  lower_error := reuse_lower_error 2 3 Primitive.Addresses.material193

def v194_pa : Scalar.QComplex := ((999950422004922398107304143571 : Int)/10^30,(9957586664328253320743729641 : Int)/10^30)
theorem v194_pa_checked : Scalar.distance (sourceCoefficient 2 4 1 0) v194_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v194_pb : Scalar.QComplex := ((4296472461426121376637061 : Int)/10^30,(-431455893457233274703223685 : Int)/10^30)
theorem v194_pb_checked : Scalar.distance (sourceCoefficient 2 4 1 1) v194_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v194_pg : Scalar.QComplex := ((-93081789427879718471579 : Int)/10^30,(-926915939732763102591 : Int)/10^30)
theorem v194_pg_checked : Scalar.distance (sourceCoefficient 2 4 1 2) v194_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v194_mb : Scalar.QComplex := ((3924143857651562812617808 : Int)/10^30,(-431459440468713906488326029 : Int)/10^30)
theorem v194_mb_checked : Scalar.distance (sourceCoefficient 2 4 3 1) v194_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v194_mg : Scalar.QComplex := ((-93082554655984711701858 : Int)/10^30,(-846590202571508656262 : Int)/10^30)
theorem v194_mg_checked : Scalar.distance (sourceCoefficient 2 4 3 2) v194_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v194_upper : Scalar.QComplex := ((999966118587468674552476813274 : Int)/10^30,(8231748120085780247932109481 : Int)/10^30)
theorem v194_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 4 5) 1) 14) v194_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material194 : Material (2 : Basis) (4 : Basis) where
  plus := ![v194_pa,v194_pb,v194_pg]
  minus := ![(Primitive.Addresses.material194 1).one,v194_mb,v194_mg]
  upper := v194_upper
  lower := (Primitive.Addresses.material194 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v194_pa_checked.trans (by decide +kernel)
    · exact v194_pb_checked.trans (by decide +kernel)
    · exact v194_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 4 Primitive.Addresses.material194
    · exact v194_mb_checked.trans (by decide +kernel)
    · exact v194_mg_checked.trans (by decide +kernel)
  upper_error := v194_upper_checked
  lower_error := reuse_lower_error 2 4 Primitive.Addresses.material194

def v195_pa : Scalar.QComplex := ((999950669215001416173169824279 : Int)/10^30,(9932730564694638748721888869 : Int)/10^30)
theorem v195_pa_checked : Scalar.distance (sourceCoefficient 2 5 1 0) v195_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v195_pb : Scalar.QComplex := ((4285747554295542257350823 : Int)/10^30,(-431455993605332738588055214 : Int)/10^30)
theorem v195_pb_checked : Scalar.distance (sourceCoefficient 2 5 1 1) v195_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v195_pg : Scalar.QComplex := ((-93081811736745417498364 : Int)/10^30,(-924602167805472599800 : Int)/10^30)
theorem v195_pg_checked : Scalar.distance (sourceCoefficient 2 5 1 2) v195_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v195_mb : Scalar.QComplex := ((3913418868091057436145569 : Int)/10^30,(-431459531361664258855127771 : Int)/10^30)
theorem v195_mb_checked : Scalar.distance (sourceCoefficient 2 5 3 1) v195_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v195_mg : Scalar.QComplex := ((-93082574968161139285880 : Int)/10^30,(-844276412254194842356 : Int)/10^30)
theorem v195_mg_checked : Scalar.distance (sourceCoefficient 2 5 3 2) v195_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v195_upper : Scalar.QComplex := ((999966322897806462370462191755 : Int)/10^30,(8206891630810236615610153017 : Int)/10^30)
theorem v195_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 5 5) 1) 14) v195_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material195 : Material (2 : Basis) (5 : Basis) where
  plus := ![v195_pa,v195_pb,v195_pg]
  minus := ![(Primitive.Addresses.material195 1).one,v195_mb,v195_mg]
  upper := v195_upper
  lower := (Primitive.Addresses.material195 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v195_pa_checked.trans (by decide +kernel)
    · exact v195_pb_checked.trans (by decide +kernel)
    · exact v195_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 5 Primitive.Addresses.material195
    · exact v195_mb_checked.trans (by decide +kernel)
    · exact v195_mg_checked.trans (by decide +kernel)
  upper_error := v195_upper_checked
  lower_error := reuse_lower_error 2 5 Primitive.Addresses.material195

def v196_pa : Scalar.QComplex := ((999981405218858107973332189507 : Int)/10^30,(6098296197947287183923942109 : Int)/10^30)
theorem v196_pa_checked : Scalar.distance (sourceCoefficient 2 6 1 0) v196_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v196_pb : Scalar.QComplex := ((2631263626695374072602157 : Int)/10^30,(-431467185836231974616316323 : Int)/10^30)
theorem v196_pb_checked : Scalar.distance (sourceCoefficient 2 6 1 1) v196_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v196_pg : Scalar.QComplex := ((-93084449588116402815355 : Int)/10^30,(-567667100656724345980 : Int)/10^30)
theorem v196_pg_checked : Scalar.distance (sourceCoefficient 2 6 1 2) v196_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v196_mb : Scalar.QComplex := ((2258925898139682474524492 : Int)/10^30,(-431469295843281786829475465 : Int)/10^30)
theorem v196_mb_checked : Scalar.distance (sourceCoefficient 2 6 3 1) v196_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v196_mg : Scalar.QComplex := ((-93084904799662741276114 : Int)/10^30,(-487339201661756081642 : Int)/10^30)
theorem v196_mg_checked : Scalar.distance (sourceCoefficient 2 6 3 2) v196_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v196_upper : Scalar.QComplex := ((999990440970025649442159943302 : Int)/10^30,(4372409927448141858141711125 : Int)/10^30)
theorem v196_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 6 5) 1) 14) v196_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material196 : Material (2 : Basis) (6 : Basis) where
  plus := ![v196_pa,v196_pb,v196_pg]
  minus := ![(Primitive.Addresses.material196 1).one,v196_mb,v196_mg]
  upper := v196_upper
  lower := (Primitive.Addresses.material196 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v196_pa_checked.trans (by decide +kernel)
    · exact v196_pb_checked.trans (by decide +kernel)
    · exact v196_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 6 Primitive.Addresses.material196
    · exact v196_mb_checked.trans (by decide +kernel)
    · exact v196_mg_checked.trans (by decide +kernel)
  upper_error := v196_upper_checked
  lower_error := reuse_lower_error 2 6 Primitive.Addresses.material196

def v197_pa : Scalar.QComplex := ((999981766044573626388290979510 : Int)/10^30,(6038839157952191430295312452 : Int)/10^30)
theorem v197_pa_checked : Scalar.distance (sourceCoefficient 2 7 1 0) v197_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v197_pb : Scalar.QComplex := ((2605609093588284565927666 : Int)/10^30,(-431467292782107470983696379 : Int)/10^30)
theorem v197_pb_checked : Scalar.distance (sourceCoefficient 2 7 1 1) v197_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v197_pg : Scalar.QComplex := ((-93084477918285441189406 : Int)/10^30,(-562132440148335594108 : Int)/10^30)
theorem v197_pg_checked : Scalar.distance (sourceCoefficient 2 7 1 2) v197_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v197_mb : Scalar.QComplex := ((2233271282295474223767971 : Int)/10^30,(-431469380650410828220791352 : Int)/10^30)
theorem v197_mb_checked : Scalar.distance (sourceCoefficient 2 7 3 1) v197_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v197_mg : Scalar.QComplex := ((-93084928353658484149878 : Int)/10^30,(-481804518766514446856 : Int)/10^30)
theorem v197_mg_checked : Scalar.distance (sourceCoefficient 2 7 3 2) v197_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v197_upper : Scalar.QComplex := ((999990699177746629337665670718 : Int)/10^30,(4312952353254871731093828415 : Int)/10^30)
theorem v197_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 7 5) 1) 14) v197_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material197 : Material (2 : Basis) (7 : Basis) where
  plus := ![v197_pa,v197_pb,v197_pg]
  minus := ![(Primitive.Addresses.material197 1).one,v197_mb,v197_mg]
  upper := v197_upper
  lower := (Primitive.Addresses.material197 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v197_pa_checked.trans (by decide +kernel)
    · exact v197_pb_checked.trans (by decide +kernel)
    · exact v197_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 7 Primitive.Addresses.material197
    · exact v197_mb_checked.trans (by decide +kernel)
    · exact v197_mg_checked.trans (by decide +kernel)
  upper_error := v197_upper_checked
  lower_error := reuse_lower_error 2 7 Primitive.Addresses.material197

def v198_pa : Scalar.QComplex := ((999981996790939002772187049227 : Int)/10^30,(6000507812382045524538881481 : Int)/10^30)
theorem v198_pa_checked : Scalar.distance (sourceCoefficient 2 8 1 0) v198_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v198_pb : Scalar.QComplex := ((2589069879938984295462785 : Int)/10^30,(-431467360650745878708099413 : Int)/10^30)
theorem v198_pb_checked : Scalar.distance (sourceCoefficient 2 8 1 1) v198_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v198_pg : Scalar.QComplex := ((-93084495978907693479768 : Int)/10^30,(-558564301282970724209 : Int)/10^30)
theorem v198_pg_checked : Scalar.distance (sourceCoefficient 2 8 1 2) v198_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v198_mb : Scalar.QComplex := ((2216732016236900818480612 : Int)/10^30,(-431469434246427484534063004 : Int)/10^30)
theorem v198_mb_checked : Scalar.distance (sourceCoefficient 2 8 3 1) v198_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v198_mg : Scalar.QComplex := ((-93084943335130873844202 : Int)/10^30,(-478236365644227165038 : Int)/10^30)
theorem v198_mg_checked : Scalar.distance (sourceCoefficient 2 8 3 2) v198_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v198_upper : Scalar.QComplex := ((999990863767343274550096495728 : Int)/10^30,(4274620666527468843028068947 : Int)/10^30)
theorem v198_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 8 5) 1) 14) v198_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material198 : Material (2 : Basis) (8 : Basis) where
  plus := ![v198_pa,v198_pb,v198_pg]
  minus := ![(Primitive.Addresses.material198 1).one,v198_mb,v198_mg]
  upper := v198_upper
  lower := (Primitive.Addresses.material198 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v198_pa_checked.trans (by decide +kernel)
    · exact v198_pb_checked.trans (by decide +kernel)
    · exact v198_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 8 Primitive.Addresses.material198
    · exact v198_mb_checked.trans (by decide +kernel)
    · exact v198_mg_checked.trans (by decide +kernel)
  upper_error := v198_upper_checked
  lower_error := reuse_lower_error 2 8 Primitive.Addresses.material198

def v199_pa : Scalar.QComplex := ((999982123531723827526784572747 : Int)/10^30,(5979349210760893285361354804 : Int)/10^30)
theorem v199_pa_checked : Scalar.distance (sourceCoefficient 2 9 1 0) v199_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v199_pb : Scalar.QComplex := ((2579940364437224601277707 : Int)/10^30,(-431467397751609940938937369 : Int)/10^30)
theorem v199_pb_checked : Scalar.distance (sourceCoefficient 2 9 1 1) v199_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v199_pg : Scalar.QComplex := ((-93084505879876590141528 : Int)/10^30,(-556594716714703855264 : Int)/10^30)
theorem v199_pg_checked : Scalar.distance (sourceCoefficient 2 9 1 2) v199_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v199_mb : Scalar.QComplex := ((2207602472118102260254313 : Int)/10^30,(-431469463468917032513551428 : Int)/10^30)
theorem v199_mb_checked : Scalar.distance (sourceCoefficient 2 9 3 1) v199_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v199_mg : Scalar.QComplex := ((-93084951536433308304441 : Int)/10^30,(-476266773265236410586 : Int)/10^30)
theorem v199_mg_checked : Scalar.distance (sourceCoefficient 2 9 3 2) v199_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v199_upper : Scalar.QComplex := ((999990953990112429029762920920 : Int)/10^30,(4253461877676471481272777518 : Int)/10^30)
theorem v199_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 9 5) 1) 14) v199_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material199 : Material (2 : Basis) (9 : Basis) where
  plus := ![v199_pa,v199_pb,v199_pg]
  minus := ![(Primitive.Addresses.material199 1).one,v199_mb,v199_mg]
  upper := v199_upper
  lower := (Primitive.Addresses.material199 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v199_pa_checked.trans (by decide +kernel)
    · exact v199_pb_checked.trans (by decide +kernel)
    · exact v199_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 9 Primitive.Addresses.material199
    · exact v199_mb_checked.trans (by decide +kernel)
    · exact v199_mg_checked.trans (by decide +kernel)
  upper_error := v199_upper_checked
  lower_error := reuse_lower_error 2 9 Primitive.Addresses.material199

def v200_pa : Scalar.QComplex := ((999982373040296319786070070759 : Int)/10^30,(5937474942907298930456691813 : Int)/10^30)
theorem v200_pa_checked : Scalar.distance (sourceCoefficient 2 10 1 0) v200_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v200_pb : Scalar.QComplex := ((2561872452305316494940775 : Int)/10^30,(-431467470417387365923739366 : Int)/10^30)
theorem v200_pb_checked : Scalar.distance (sourceCoefficient 2 10 1 1) v200_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v200_pg : Scalar.QComplex := ((-93084525331216240261997 : Int)/10^30,(-552696779090369547003 : Int)/10^30)
theorem v200_pg_checked : Scalar.distance (sourceCoefficient 2 10 1 2) v200_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v200_mb : Scalar.QComplex := ((2189534504006410412367124 : Int)/10^30,(-431469520542872979426387110 : Int)/10^30)
theorem v200_mb_checked : Scalar.distance (sourceCoefficient 2 10 3 1) v200_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v200_mg : Scalar.QComplex := ((-93084967624021102595314 : Int)/10^30,(-472368820306652362179 : Int)/10^30)
theorem v200_mg_checked : Scalar.distance (sourceCoefficient 2 10 3 2) v200_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v200_upper : Scalar.QComplex := ((999991131227125796180850896210 : Int)/10^30,(4211587241560519316501324784 : Int)/10^30)
theorem v200_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 10 5) 1) 14) v200_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material200 : Material (2 : Basis) (10 : Basis) where
  plus := ![v200_pa,v200_pb,v200_pg]
  minus := ![(Primitive.Addresses.material200 1).one,v200_mb,v200_mg]
  upper := v200_upper
  lower := (Primitive.Addresses.material200 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v200_pa_checked.trans (by decide +kernel)
    · exact v200_pb_checked.trans (by decide +kernel)
    · exact v200_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 10 Primitive.Addresses.material200
    · exact v200_mb_checked.trans (by decide +kernel)
    · exact v200_mg_checked.trans (by decide +kernel)
  upper_error := v200_upper_checked
  lower_error := reuse_lower_error 2 10 Primitive.Addresses.material200

def v201_pa : Scalar.QComplex := ((999982426514169411877945850142 : Int)/10^30,(5928462096848727110600160940 : Int)/10^30)
theorem v201_pa_checked : Scalar.distance (sourceCoefficient 2 11 1 0) v201_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v201_pb : Scalar.QComplex := ((2557983589021705587751975 : Int)/10^30,(-431467485925737946256582874 : Int)/10^30)
theorem v201_pb_checked : Scalar.distance (sourceCoefficient 2 11 1 1) v201_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v201_pg : Scalar.QComplex := ((-93084529492937534802389 : Int)/10^30,(-551857802967158581383 : Int)/10^30)
theorem v201_pg_checked : Scalar.distance (sourceCoefficient 2 11 1 2) v201_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v201_mb : Scalar.QComplex := ((2185645628787792954853220 : Int)/10^30,(-431469532695303919435828170 : Int)/10^30)
theorem v201_mb_checked : Scalar.distance (sourceCoefficient 2 11 3 1) v201_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v201_mg : Scalar.QComplex := ((-93084971061742239287508 : Int)/10^30,(-471529840904452510114 : Int)/10^30)
theorem v201_mg_checked : Scalar.distance (sourceCoefficient 2 11 3 2) v201_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v201_upper : Scalar.QComplex := ((999991169145564587132665536398 : Int)/10^30,(4202574316634469132539757033 : Int)/10^30)
theorem v201_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 11 5) 1) 14) v201_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material201 : Material (2 : Basis) (11 : Basis) where
  plus := ![v201_pa,v201_pb,v201_pg]
  minus := ![(Primitive.Addresses.material201 1).one,v201_mb,v201_mg]
  upper := v201_upper
  lower := (Primitive.Addresses.material201 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v201_pa_checked.trans (by decide +kernel)
    · exact v201_pb_checked.trans (by decide +kernel)
    · exact v201_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 11 Primitive.Addresses.material201
    · exact v201_mb_checked.trans (by decide +kernel)
    · exact v201_mg_checked.trans (by decide +kernel)
  upper_error := v201_upper_checked
  lower_error := reuse_lower_error 2 11 Primitive.Addresses.material201

def v202_pa : Scalar.QComplex := ((999982455677787920986637683126 : Int)/10^30,(5923540885392464772397278824 : Int)/10^30)
theorem v202_pa_checked : Scalar.distance (sourceCoefficient 2 12 1 0) v202_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v202_pb : Scalar.QComplex := ((2555860184476312523553089 : Int)/10^30,(-431467494373911332502317395 : Int)/10^30)
theorem v202_pb_checked : Scalar.distance (sourceCoefficient 2 12 1 1) v202_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v202_pg : Scalar.QComplex := ((-93084531761604866211149 : Int)/10^30,(-551399703621547879095 : Int)/10^30)
theorem v202_pg_checked : Scalar.distance (sourceCoefficient 2 12 1 2) v202_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v202_mb : Scalar.QComplex := ((2183522217742647306560721 : Int)/10^30,(-431469539311071671956897616 : Int)/10^30)
theorem v202_mb_checked : Scalar.distance (sourceCoefficient 2 12 3 1) v202_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v202_mg : Scalar.QComplex := ((-93084972935089622734331 : Int)/10^30,(-471071739771655400350 : Int)/10^30)
theorem v202_mg_checked : Scalar.distance (sourceCoefficient 2 12 3 2) v202_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v202_upper : Scalar.QComplex := ((999991189815575135764436949667 : Int)/10^30,(4197653062174013328416089099 : Int)/10^30)
theorem v202_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 12 5) 1) 14) v202_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material202 : Material (2 : Basis) (12 : Basis) where
  plus := ![v202_pa,v202_pb,v202_pg]
  minus := ![(Primitive.Addresses.material202 1).one,v202_mb,v202_mg]
  upper := v202_upper
  lower := (Primitive.Addresses.material202 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v202_pa_checked.trans (by decide +kernel)
    · exact v202_pb_checked.trans (by decide +kernel)
    · exact v202_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 12 Primitive.Addresses.material202
    · exact v202_mb_checked.trans (by decide +kernel)
    · exact v202_mg_checked.trans (by decide +kernel)
  upper_error := v202_upper_checked
  lower_error := reuse_lower_error 2 12 Primitive.Addresses.material202

def v203_pa : Scalar.QComplex := ((999982759503205151041146233338 : Int)/10^30,(5872026596922751039721161384 : Int)/10^30)
theorem v203_pa_checked : Scalar.distance (sourceCoefficient 2 13 1 0) v203_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v203_pb : Scalar.QComplex := ((2533632798134409831711085 : Int)/10^30,(-431467581971445333581230576 : Int)/10^30)
theorem v203_pb_checked : Scalar.distance (sourceCoefficient 2 13 1 1) v203_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v203_pg : Scalar.QComplex := ((-93084555351703364654510 : Int)/10^30,(-546604408519483291849 : Int)/10^30)
theorem v203_pg_checked : Scalar.distance (sourceCoefficient 2 13 1 2) v203_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v203_mb : Scalar.QComplex := ((2161294764084289795094388 : Int)/10^30,(-431469607727339727727316627 : Int)/10^30)
theorem v203_mb_checked : Scalar.distance (sourceCoefficient 2 13 3 1) v203_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v203_mg : Scalar.QComplex := ((-93084992387055636498297 : Int)/10^30,(-466276426097905789854 : Int)/10^30)
theorem v203_mg_checked : Scalar.distance (sourceCoefficient 2 13 3 2) v203_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v203_upper : Scalar.QComplex := ((999991404731551294567765065521 : Int)/10^30,(4146138326053673665442790441 : Int)/10^30)
theorem v203_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 13 5) 1) 14) v203_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material203 : Material (2 : Basis) (13 : Basis) where
  plus := ![v203_pa,v203_pb,v203_pg]
  minus := ![(Primitive.Addresses.material203 1).one,v203_mb,v203_mg]
  upper := v203_upper
  lower := (Primitive.Addresses.material203 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v203_pa_checked.trans (by decide +kernel)
    · exact v203_pb_checked.trans (by decide +kernel)
    · exact v203_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 13 Primitive.Addresses.material203
    · exact v203_mb_checked.trans (by decide +kernel)
    · exact v203_mg_checked.trans (by decide +kernel)
  upper_error := v203_upper_checked
  lower_error := reuse_lower_error 2 13 Primitive.Addresses.material203

def v204_pa : Scalar.QComplex := ((999982855144900780429445977139 : Int)/10^30,(5855716544743501147191326683 : Int)/10^30)
theorem v204_pa_checked : Scalar.distance (sourceCoefficient 2 14 1 0) v204_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v204_pb : Scalar.QComplex := ((2526595336923270849902749 : Int)/10^30,(-431467609387673303678610200 : Int)/10^30)
theorem v204_pb_checked : Scalar.distance (sourceCoefficient 2 14 1 1) v204_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v204_pg : Scalar.QComplex := ((-93084562760545297563903 : Int)/10^30,(-545086159640363512704 : Int)/10^30)
theorem v204_pg_checked : Scalar.distance (sourceCoefficient 2 14 1 2) v204_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v204_mb : Scalar.QComplex := ((2154257281834549292935689 : Int)/10^30,(-431469629070545419784107125 : Int)/10^30)
theorem v204_mb_checked : Scalar.distance (sourceCoefficient 2 14 3 1) v204_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v204_mg : Scalar.QComplex := ((-93084998485714407468022 : Int)/10^30,(-464758171390602549560 : Int)/10^30)
theorem v204_mg_checked : Scalar.distance (sourceCoefficient 2 14 3 2) v204_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v204_upper : Scalar.QComplex := ((999991472223434051875389589234 : Int)/10^30,(4129828133097440471116954395 : Int)/10^30)
theorem v204_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 14 5) 1) 14) v204_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material204 : Material (2 : Basis) (14 : Basis) where
  plus := ![v204_pa,v204_pb,v204_pg]
  minus := ![(Primitive.Addresses.material204 1).one,v204_mb,v204_mg]
  upper := v204_upper
  lower := (Primitive.Addresses.material204 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v204_pa_checked.trans (by decide +kernel)
    · exact v204_pb_checked.trans (by decide +kernel)
    · exact v204_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 14 Primitive.Addresses.material204
    · exact v204_mb_checked.trans (by decide +kernel)
    · exact v204_mg_checked.trans (by decide +kernel)
  upper_error := v204_upper_checked
  lower_error := reuse_lower_error 2 14 Primitive.Addresses.material204

def v205_pa : Scalar.QComplex := ((999983008677206988671874219556 : Int)/10^30,(5829438813554217239707838646 : Int)/10^30)
theorem v205_pa_checked : Scalar.distance (sourceCoefficient 2 15 1 0) v205_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v205_pb : Scalar.QComplex := ((2515257022117174132287322 : Int)/10^30,(-431467653237048761377567559 : Int)/10^30)
theorem v205_pb_checked : Scalar.distance (sourceCoefficient 2 15 1 1) v205_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v205_pg : Scalar.QComplex := ((-93084574636434796779258 : Int)/10^30,(-542640052501109907276 : Int)/10^30)
theorem v205_pg_checked : Scalar.distance (sourceCoefficient 2 15 1 2) v205_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v205_mb : Scalar.QComplex := ((2142918933410189246780231 : Int)/10^30,(-431469663135449531437421843 : Int)/10^30)
theorem v205_mb_checked : Scalar.distance (sourceCoefficient 2 15 3 1) v205_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v205_mg : Scalar.QComplex := ((-93085008250719192147002 : Int)/10^30,(-462312054913788657079 : Int)/10^30)
theorem v205_mg_checked : Scalar.distance (sourceCoefficient 2 15 3 2) v205_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v205_upper : Scalar.QComplex := ((999991580402531456230377159923 : Int)/10^30,(4103550176062918197521083800 : Int)/10^30)
theorem v205_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 15 5) 1) 14) v205_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material205 : Material (2 : Basis) (15 : Basis) where
  plus := ![v205_pa,v205_pb,v205_pg]
  minus := ![(Primitive.Addresses.material205 1).one,v205_mb,v205_mg]
  upper := v205_upper
  lower := (Primitive.Addresses.material205 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v205_pa_checked.trans (by decide +kernel)
    · exact v205_pb_checked.trans (by decide +kernel)
    · exact v205_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 15 Primitive.Addresses.material205
    · exact v205_mb_checked.trans (by decide +kernel)
    · exact v205_mg_checked.trans (by decide +kernel)
  upper_error := v205_upper_checked
  lower_error := reuse_lower_error 2 15 Primitive.Addresses.material205

def v206_pa : Scalar.QComplex := ((999983028098013833533672895923 : Int)/10^30,(5826106412251316287569759447 : Int)/10^30)
theorem v206_pa_checked : Scalar.distance (sourceCoefficient 2 16 1 0) v206_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v206_pb : Scalar.QComplex := ((2513819157727862833618425 : Int)/10^30,(-431467658769407330657139743 : Int)/10^30)
theorem v206_pb_checked : Scalar.distance (sourceCoefficient 2 16 1 1) v206_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v206_pg : Scalar.QComplex := ((-93084576137113343759393 : Int)/10^30,(-542329850283195092073 : Int)/10^30)
theorem v206_pg_checked : Scalar.distance (sourceCoefficient 2 16 1 2) v206_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v206_mb : Scalar.QComplex := ((2141481064782084296792974 : Int)/10^30,(-431469667426993831799533855 : Int)/10^30)
theorem v206_mb_checked : Scalar.distance (sourceCoefficient 2 16 3 1) v206_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v206_mg : Scalar.QComplex := ((-93085009483706637284711 : Int)/10^30,(-462001851516358306557 : Int)/10^30)
theorem v206_mg_checked : Scalar.distance (sourceCoefficient 2 16 3 2) v206_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v206_upper : Scalar.QComplex := ((999991594071887040359324205431 : Int)/10^30,(4100217746204686762301724371 : Int)/10^30)
theorem v206_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 16 5) 1) 14) v206_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material206 : Material (2 : Basis) (16 : Basis) where
  plus := ![v206_pa,v206_pb,v206_pg]
  minus := ![(Primitive.Addresses.material206 1).one,v206_mb,v206_mg]
  upper := v206_upper
  lower := (Primitive.Addresses.material206 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v206_pa_checked.trans (by decide +kernel)
    · exact v206_pb_checked.trans (by decide +kernel)
    · exact v206_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 16 Primitive.Addresses.material206
    · exact v206_mb_checked.trans (by decide +kernel)
    · exact v206_mg_checked.trans (by decide +kernel)
  upper_error := v206_upper_checked
  lower_error := reuse_lower_error 2 16 Primitive.Addresses.material206

def v207_pa : Scalar.QComplex := ((999983067060687209632995514178 : Int)/10^30,(5819415082389892848282070752 : Int)/10^30)
theorem v207_pa_checked : Scalar.distance (sourceCoefficient 2 17 1 0) v207_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v207_pb : Scalar.QComplex := ((2510931982999217841566904 : Int)/10^30,(-431467669858870021173505416 : Int)/10^30)
theorem v207_pb_checked : Scalar.distance (sourceCoefficient 2 17 1 1) v207_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v207_pg : Scalar.QComplex := ((-93084579146774227515667 : Int)/10^30,(-541706976516012303741 : Int)/10^30)
theorem v207_pg_checked : Scalar.distance (sourceCoefficient 2 17 1 2) v207_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v207_mb : Scalar.QComplex := ((2138593881558759555563035 : Int)/10^30,(-431469676024950635904205136 : Int)/10^30)
theorem v207_mb_checked : Scalar.distance (sourceCoefficient 2 17 3 1) v207_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v207_mg : Scalar.QComplex := ((-93085011955854392521035 : Int)/10^30,(-461378975383898095897 : Int)/10^30)
theorem v207_mg_checked : Scalar.distance (sourceCoefficient 2 17 3 2) v207_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v207_upper : Scalar.QComplex := ((999991621485874078019823120149 : Int)/10^30,(4093526359063173551753867513 : Int)/10^30)
theorem v207_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 17 5) 1) 14) v207_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material207 : Material (2 : Basis) (17 : Basis) where
  plus := ![v207_pa,v207_pb,v207_pg]
  minus := ![(Primitive.Addresses.material207 1).one,v207_mb,v207_mg]
  upper := v207_upper
  lower := (Primitive.Addresses.material207 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v207_pa_checked.trans (by decide +kernel)
    · exact v207_pb_checked.trans (by decide +kernel)
    · exact v207_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 17 Primitive.Addresses.material207
    · exact v207_mb_checked.trans (by decide +kernel)
    · exact v207_mg_checked.trans (by decide +kernel)
  upper_error := v207_upper_checked
  lower_error := reuse_lower_error 2 17 Primitive.Addresses.material207

def v208_pa : Scalar.QComplex := ((999983196701577468605282935591 : Int)/10^30,(5797095349761371036273689082 : Int)/10^30)
theorem v208_pa_checked : Scalar.distance (sourceCoefficient 2 18 1 0) v208_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v208_pb : Scalar.QComplex := ((2501301465982293764951023 : Int)/10^30,(-431467706662833627694507019 : Int)/10^30)
theorem v208_pb_checked : Scalar.distance (sourceCoefficient 2 18 1 1) v208_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v208_pg : Scalar.QComplex := ((-93084589150696554090052 : Int)/10^30,(-539629306452224624305 : Int)/10^30)
theorem v208_pg_checked : Scalar.distance (sourceCoefficient 2 18 1 2) v208_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v208_mb : Scalar.QComplex := ((2128963336367554097279457 : Int)/10^30,(-431469704518198095407221757 : Int)/10^30)
theorem v208_mb_checked : Scalar.distance (sourceCoefficient 2 18 3 1) v208_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v208_mg : Scalar.QComplex := ((-93085020166837303915182 : Int)/10^30,(-459301297460787527525 : Int)/10^30)
theorem v208_mg_checked : Scalar.distance (sourceCoefficient 2 18 3 2) v208_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v208_upper : Scalar.QComplex := ((999991712604737565613064004716 : Int)/10^30,(4071206435928855972665345832 : Int)/10^30)
theorem v208_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 18 5) 1) 14) v208_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material208 : Material (2 : Basis) (18 : Basis) where
  plus := ![v208_pa,v208_pb,v208_pg]
  minus := ![(Primitive.Addresses.material208 1).one,v208_mb,v208_mg]
  upper := v208_upper
  lower := (Primitive.Addresses.material208 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v208_pa_checked.trans (by decide +kernel)
    · exact v208_pb_checked.trans (by decide +kernel)
    · exact v208_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 18 Primitive.Addresses.material208
    · exact v208_mb_checked.trans (by decide +kernel)
    · exact v208_mg_checked.trans (by decide +kernel)
  upper_error := v208_upper_checked
  lower_error := reuse_lower_error 2 18 Primitive.Addresses.material208

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
