import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B178
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B179

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v4289_pa : Scalar.QComplex := ((999998426879591906059103707453 : Int)/10^30,(-1773763891130965443675500901 : Int)/10^30)
theorem v4289_pa_checked : Scalar.distance (sourceCoefficient 67 69 1 0) v4289_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4289_pb : Scalar.QComplex := ((-765339245946385248850180 : Int)/10^30,(-431476841874153237755736917 : Int)/10^30)
theorem v4289_pb_checked : Scalar.distance (sourceCoefficient 67 69 1 1) v4289_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4289_pg : Scalar.QComplex := ((-93086283421936741616110 : Int)/10^30,(165113348036591841054 : Int)/10^30)
theorem v4289_pg_checked : Scalar.distance (sourceCoefficient 67 69 1 2) v4289_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4289_mb : Scalar.QComplex := ((-1137684042517429188542235 : Int)/10^30,(-431476020762305890508714898 : Int)/10^30)
theorem v4289_mb_checked : Scalar.distance (sourceCoefficient 67 69 3 1) v4289_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4289_mg : Scalar.QComplex := ((-93086106276276243875884 : Int)/10^30,(245442556699903479045 : Int)/10^30)
theorem v4289_mg_checked : Scalar.distance (sourceCoefficient 67 69 3 2) v4289_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4289_upper : Scalar.QComplex := ((999993876143841646971024509934 : Int)/10^30,(-3499667814963558759599089053 : Int)/10^30)
theorem v4289_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 69 5) 1) 14) v4289_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4289 : Material (67 : Basis) (69 : Basis) where
  plus := ![v4289_pa,v4289_pb,v4289_pg]
  minus := ![(Primitive.Addresses.material4289 1).one,v4289_mb,v4289_mg]
  upper := v4289_upper
  lower := (Primitive.Addresses.material4289 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4289_pa_checked.trans (by decide +kernel)
    · exact v4289_pb_checked.trans (by decide +kernel)
    · exact v4289_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 69 Primitive.Addresses.material4289
    · exact v4289_mb_checked.trans (by decide +kernel)
    · exact v4289_mg_checked.trans (by decide +kernel)
  upper_error := v4289_upper_checked
  lower_error := reuse_lower_error 67 69 Primitive.Addresses.material4289

def v4290_pa : Scalar.QComplex := ((999998401534169953390710114815 : Int)/10^30,(-1787995834726750350092423771 : Int)/10^30)
theorem v4290_pa_checked : Scalar.distance (sourceCoefficient 67 70 1 0) v4290_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4290_pb : Scalar.QComplex := ((-771480009397846495150693 : Int)/10^30,(-431476830778699102288216258 : Int)/10^30)
theorem v4290_pb_checked : Scalar.distance (sourceCoefficient 67 70 1 1) v4290_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4290_pg : Scalar.QComplex := ((-93086281045419502976864 : Int)/10^30,(166438148825107436590 : Int)/10^30)
theorem v4290_pg_checked : Scalar.distance (sourceCoefficient 67 70 1 2) v4290_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4290_mb : Scalar.QComplex := ((-1143824794107526356905050 : Int)/10^30,(-431476004367653597493903869 : Int)/10^30)
theorem v4290_mb_checked : Scalar.distance (sourceCoefficient 67 70 3 1) v4290_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4290_mg : Scalar.QComplex := ((-93086102756516476446238 : Int)/10^30,(246767354944307852048 : Int)/10^30)
theorem v4290_mg_checked : Scalar.distance (sourceCoefficient 67 70 3 2) v4290_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4290_upper : Scalar.QComplex := ((999993826235413908843995951149 : Int)/10^30,(-3513899693618636510039413733 : Int)/10^30)
theorem v4290_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 70 5) 1) 14) v4290_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4290 : Material (67 : Basis) (70 : Basis) where
  plus := ![v4290_pa,v4290_pb,v4290_pg]
  minus := ![(Primitive.Addresses.material4290 1).one,v4290_mb,v4290_mg]
  upper := v4290_upper
  lower := (Primitive.Addresses.material4290 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4290_pa_checked.trans (by decide +kernel)
    · exact v4290_pb_checked.trans (by decide +kernel)
    · exact v4290_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 70 Primitive.Addresses.material4290
    · exact v4290_mb_checked.trans (by decide +kernel)
    · exact v4290_mg_checked.trans (by decide +kernel)
  upper_error := v4290_upper_checked
  lower_error := reuse_lower_error 67 70 Primitive.Addresses.material4290

def v4291_pa : Scalar.QComplex := ((999998357803645233425978881360 : Int)/10^30,(-1812288611872921424503684075 : Int)/10^30)
theorem v4291_pa_checked : Scalar.distance (sourceCoefficient 67 71 1 0) v4291_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4291_pb : Scalar.QComplex := ((-781961796031175093344472 : Int)/10^30,(-431476811570449543165550834 : Int)/10^30)
theorem v4291_pb_checked : Scalar.distance (sourceCoefficient 67 71 1 1) v4291_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4291_pg : Scalar.QComplex := ((-93086276938078219384840 : Int)/10^30,(168699476654193727231 : Int)/10^30)
theorem v4291_pg_checked : Scalar.distance (sourceCoefficient 67 71 1 2) v4291_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4291_mb : Scalar.QComplex := ((-1154306560262152488119313 : Int)/10^30,(-431475976114101408063281571 : Int)/10^30)
theorem v4291_mb_checked : Scalar.distance (sourceCoefficient 67 71 3 1) v4291_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4291_mg : Scalar.QComplex := ((-93086096697752652128325 : Int)/10^30,(249028678386947904176 : Int)/10^30)
theorem v4291_mg_checked : Scalar.distance (sourceCoefficient 67 71 3 2) v4291_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4291_upper : Scalar.QComplex := ((999993740577824789594988380115 : Int)/10^30,(-3538192359108651190842412576 : Int)/10^30)
theorem v4291_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 71 5) 1) 14) v4291_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4291 : Material (67 : Basis) (71 : Basis) where
  plus := ![v4291_pa,v4291_pb,v4291_pg]
  minus := ![(Primitive.Addresses.material4291 1).one,v4291_mb,v4291_mg]
  upper := v4291_upper
  lower := (Primitive.Addresses.material4291 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4291_pa_checked.trans (by decide +kernel)
    · exact v4291_pb_checked.trans (by decide +kernel)
    · exact v4291_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 71 Primitive.Addresses.material4291
    · exact v4291_mb_checked.trans (by decide +kernel)
    · exact v4291_mg_checked.trans (by decide +kernel)
  upper_error := v4291_upper_checked
  lower_error := reuse_lower_error 67 71 Primitive.Addresses.material4291

def v4292_pa : Scalar.QComplex := ((999998309679464589058598123748 : Int)/10^30,(-1838651194119855450899223747 : Int)/10^30)
theorem v4292_pa_checked : Scalar.distance (sourceCoefficient 67 72 1 0) v4292_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4292_pb : Scalar.QComplex := ((-793336656789599700633914 : Int)/10^30,(-431476790341475931759876850 : Int)/10^30)
theorem v4292_pb_checked : Scalar.distance (sourceCoefficient 67 72 1 1) v4292_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4292_pg : Scalar.QComplex := ((-93086272408267802483886 : Int)/10^30,(171153475223861625502 : Int)/10^30)
theorem v4292_pg_checked : Scalar.distance (sourceCoefficient 67 72 1 2) v4292_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4292_mb : Scalar.QComplex := ((-1165681398465548469064777 : Int)/10^30,(-431475945069143171365173689 : Int)/10^30)
theorem v4292_mb_checked : Scalar.distance (sourceCoefficient 67 72 3 1) v4292_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4292_mg : Scalar.QComplex := ((-93086090050253680252150 : Int)/10^30,(251482672133857606987 : Int)/10^30)
theorem v4292_mg_checked : Scalar.distance (sourceCoefficient 67 72 3 2) v4292_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4292_upper : Scalar.QComplex := ((999993646954290457112813167559 : Int)/10^30,(-3564554819033645726262688625 : Int)/10^30)
theorem v4292_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 72 5) 1) 14) v4292_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4292 : Material (67 : Basis) (72 : Basis) where
  plus := ![v4292_pa,v4292_pb,v4292_pg]
  minus := ![(Primitive.Addresses.material4292 1).one,v4292_mb,v4292_mg]
  upper := v4292_upper
  lower := (Primitive.Addresses.material4292 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4292_pa_checked.trans (by decide +kernel)
    · exact v4292_pb_checked.trans (by decide +kernel)
    · exact v4292_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 72 Primitive.Addresses.material4292
    · exact v4292_mb_checked.trans (by decide +kernel)
    · exact v4292_mg_checked.trans (by decide +kernel)
  upper_error := v4292_upper_checked
  lower_error := reuse_lower_error 67 72 Primitive.Addresses.material4292

def v4293_pa : Scalar.QComplex := ((999998292260220085792962680009 : Int)/10^30,(-1848100820694925770535822277 : Int)/10^30)
theorem v4293_pa_checked : Scalar.distance (sourceCoefficient 67 73 1 0) v4293_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4293_pb : Scalar.QComplex := ((-797413957873417869760709 : Int)/10^30,(-431476782634638198392564130 : Int)/10^30)
theorem v4293_pb_checked : Scalar.distance (sourceCoefficient 67 73 1 1) v4293_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4293_pg : Scalar.QComplex := ((-93086270766188312826433 : Int)/10^30,(172033107186203301771 : Int)/10^30)
theorem v4293_pg_checked : Scalar.distance (sourceCoefficient 67 73 1 2) v4293_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4293_mb : Scalar.QComplex := ((-1169758691380547242011510 : Int)/10^30,(-431475933843781107094659106 : Int)/10^30)
theorem v4293_mb_checked : Scalar.distance (sourceCoefficient 67 73 3 1) v4293_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4293_mg : Scalar.QComplex := ((-93086087649092035667997 : Int)/10^30,(252362302351631459451 : Int)/10^30)
theorem v4293_mg_checked : Scalar.distance (sourceCoefficient 67 73 3 2) v4293_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4293_upper : Scalar.QComplex := ((999993613225873692620601437821 : Int)/10^30,(-3574004401470571542325510553 : Int)/10^30)
theorem v4293_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 73 5) 1) 14) v4293_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4293 : Material (67 : Basis) (73 : Basis) where
  plus := ![v4293_pa,v4293_pb,v4293_pg]
  minus := ![(Primitive.Addresses.material4293 1).one,v4293_mb,v4293_mg]
  upper := v4293_upper
  lower := (Primitive.Addresses.material4293 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4293_pa_checked.trans (by decide +kernel)
    · exact v4293_pb_checked.trans (by decide +kernel)
    · exact v4293_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 73 Primitive.Addresses.material4293
    · exact v4293_mb_checked.trans (by decide +kernel)
    · exact v4293_mg_checked.trans (by decide +kernel)
  upper_error := v4293_upper_checked
  lower_error := reuse_lower_error 67 73 Primitive.Addresses.material4293

def v4294_pa : Scalar.QComplex := ((999998272552516451769085732315 : Int)/10^30,(-1858733973171430847998619416 : Int)/10^30)
theorem v4294_pa_checked : Scalar.distance (sourceCoefficient 67 74 1 0) v4294_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4294_pb : Scalar.QComplex := ((-802001923700634455280025 : Int)/10^30,(-431476773901125187287446115 : Int)/10^30)
theorem v4294_pb_checked : Scalar.distance (sourceCoefficient 67 74 1 1) v4294_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4294_pg : Scalar.QComplex := ((-93086268906849746897226 : Int)/10^30,(173022909340922392150 : Int)/10^30)
theorem v4294_pg_checked : Scalar.distance (sourceCoefficient 67 74 1 2) v4294_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4294_mb : Scalar.QComplex := ((-1174346647962826083902098 : Int)/10^30,(-431475921151063473297894763 : Int)/10^30)
theorem v4294_mb_checked : Scalar.distance (sourceCoefficient 67 74 3 1) v4294_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4294_mg : Scalar.QComplex := ((-93086084935599481567136 : Int)/10^30,(253352102533276530538 : Int)/10^30)
theorem v4294_mg_checked : Scalar.distance (sourceCoefficient 67 74 3 2) v4294_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4294_upper : Scalar.QComplex := ((999993575166342868515870610210 : Int)/10^30,(-3584637504096536460447813765 : Int)/10^30)
theorem v4294_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 74 5) 1) 14) v4294_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4294 : Material (67 : Basis) (74 : Basis) where
  plus := ![v4294_pa,v4294_pb,v4294_pg]
  minus := ![(Primitive.Addresses.material4294 1).one,v4294_mb,v4294_mg]
  upper := v4294_upper
  lower := (Primitive.Addresses.material4294 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4294_pa_checked.trans (by decide +kernel)
    · exact v4294_pb_checked.trans (by decide +kernel)
    · exact v4294_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 74 Primitive.Addresses.material4294
    · exact v4294_mb_checked.trans (by decide +kernel)
    · exact v4294_mg_checked.trans (by decide +kernel)
  upper_error := v4294_upper_checked
  lower_error := reuse_lower_error 67 74 Primitive.Addresses.material4294

def v4295_pa : Scalar.QComplex := ((999998244905389139510783818310 : Int)/10^30,(-1873549076315826150457230301 : Int)/10^30)
theorem v4295_pa_checked : Scalar.distance (sourceCoefficient 67 75 1 0) v4295_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4295_pb : Scalar.QComplex := ((-808394307001493517771139 : Int)/10^30,(-431476761624327050461771296 : Int)/10^30)
theorem v4295_pb_checked : Scalar.distance (sourceCoefficient 67 75 1 1) v4295_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4295_pg : Scalar.QComplex := ((-93086266295772889897848 : Int)/10^30,(174401994328134686349 : Int)/10^30)
theorem v4295_pg_checked : Scalar.distance (sourceCoefficient 67 75 1 2) v4295_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4295_mb : Scalar.QComplex := ((-1180739018289184831516141 : Int)/10^30,(-431475903357931021300309313 : Int)/10^30)
theorem v4295_mb_checked : Scalar.distance (sourceCoefficient 67 75 3 1) v4295_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4295_mg : Scalar.QComplex := ((-93086081134435364508924 : Int)/10^30,(254731184753750727646 : Int)/10^30)
theorem v4295_mg_checked : Scalar.distance (sourceCoefficient 67 75 3 2) v4295_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4295_upper : Scalar.QComplex := ((999993521949732721838133931490 : Int)/10^30,(-3599452537459142320434189065 : Int)/10^30)
theorem v4295_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 75 5) 1) 14) v4295_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4295 : Material (67 : Basis) (75 : Basis) where
  plus := ![v4295_pa,v4295_pb,v4295_pg]
  minus := ![(Primitive.Addresses.material4295 1).one,v4295_mb,v4295_mg]
  upper := v4295_upper
  lower := (Primitive.Addresses.material4295 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4295_pa_checked.trans (by decide +kernel)
    · exact v4295_pb_checked.trans (by decide +kernel)
    · exact v4295_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 75 Primitive.Addresses.material4295
    · exact v4295_mb_checked.trans (by decide +kernel)
    · exact v4295_mg_checked.trans (by decide +kernel)
  upper_error := v4295_upper_checked
  lower_error := reuse_lower_error 67 75 Primitive.Addresses.material4295

def v4296_pa : Scalar.QComplex := ((999998221539572960808955153745 : Int)/10^30,(-1885979239322875352756331998 : Int)/10^30)
theorem v4296_pa_checked : Scalar.distance (sourceCoefficient 67 76 1 0) v4296_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4296_pb : Scalar.QComplex := ((-813757642299300406472793 : Int)/10^30,(-431476751226434453977213917 : Int)/10^30)
theorem v4296_pb_checked : Scalar.distance (sourceCoefficient 67 76 1 1) v4296_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4296_pg : Scalar.QComplex := ((-93086264086638402833390 : Int)/10^30,(175559073758391872352 : Int)/10^30)
theorem v4296_pg_checked : Scalar.distance (sourceCoefficient 67 76 1 2) v4296_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4296_mb : Scalar.QComplex := ((-1186102342617063865244300 : Int)/10^30,(-431475888331725490073873642 : Int)/10^30)
theorem v4296_mb_checked : Scalar.distance (sourceCoefficient 67 76 3 1) v4296_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4296_mg : Scalar.QComplex := ((-93086077926794264617262 : Int)/10^30,(255888261846790794009 : Int)/10^30)
theorem v4296_mg_checked : Scalar.distance (sourceCoefficient 67 76 3 2) v4296_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4296_upper : Scalar.QComplex := ((999993477130617649187076228434 : Int)/10^30,(-3611882641625644879096172437 : Int)/10^30)
theorem v4296_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 76 5) 1) 14) v4296_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4296 : Material (67 : Basis) (76 : Basis) where
  plus := ![v4296_pa,v4296_pb,v4296_pg]
  minus := ![(Primitive.Addresses.material4296 1).one,v4296_mb,v4296_mg]
  upper := v4296_upper
  lower := (Primitive.Addresses.material4296 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4296_pa_checked.trans (by decide +kernel)
    · exact v4296_pb_checked.trans (by decide +kernel)
    · exact v4296_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 76 Primitive.Addresses.material4296
    · exact v4296_mb_checked.trans (by decide +kernel)
    · exact v4296_mg_checked.trans (by decide +kernel)
  upper_error := v4296_upper_checked
  lower_error := reuse_lower_error 67 76 Primitive.Addresses.material4296

def v4297_pa : Scalar.QComplex := ((999998216108162338597197969636 : Int)/10^30,(-1888856927629172534381208387 : Int)/10^30)
theorem v4297_pa_checked : Scalar.distance (sourceCoefficient 67 77 1 0) v4297_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4297_pb : Scalar.QComplex := ((-814999299964786870934832 : Int)/10^30,(-431476748806562544067762672 : Int)/10^30)
theorem v4297_pb_checked : Scalar.distance (sourceCoefficient 67 77 1 1) v4297_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4297_pg : Scalar.QComplex := ((-93086263572812995481711 : Int)/10^30,(175826947472879353549 : Int)/10^30)
theorem v4297_pg_checked : Scalar.distance (sourceCoefficient 67 77 1 2) v4297_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4297_mb : Scalar.QComplex := ((-1187343997731983963020258 : Int)/10^30,(-431475884840359838063833646 : Int)/10^30)
theorem v4297_mb_checked : Scalar.distance (sourceCoefficient 67 77 3 1) v4297_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4297_mg : Scalar.QComplex := ((-93086077181806097567812 : Int)/10^30,(256156135018128464162 : Int)/10^30)
theorem v4297_mg_checked : Scalar.distance (sourceCoefficient 67 77 3 2) v4297_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4297_upper : Scalar.QComplex := ((999993466732586161598331104060 : Int)/10^30,(-3614760316271841365290789121 : Int)/10^30)
theorem v4297_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 77 5) 1) 14) v4297_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4297 : Material (67 : Basis) (77 : Basis) where
  plus := ![v4297_pa,v4297_pb,v4297_pg]
  minus := ![(Primitive.Addresses.material4297 1).one,v4297_mb,v4297_mg]
  upper := v4297_upper
  lower := (Primitive.Addresses.material4297 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4297_pa_checked.trans (by decide +kernel)
    · exact v4297_pb_checked.trans (by decide +kernel)
    · exact v4297_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 77 Primitive.Addresses.material4297
    · exact v4297_mb_checked.trans (by decide +kernel)
    · exact v4297_mg_checked.trans (by decide +kernel)
  upper_error := v4297_upper_checked
  lower_error := reuse_lower_error 67 77 Primitive.Addresses.material4297

def v4298_pa : Scalar.QComplex := ((999998183282075707547998107119 : Int)/10^30,(-1906156485737959436936210850 : Int)/10^30)
theorem v4298_pa_checked : Scalar.distance (sourceCoefficient 67 78 1 0) v4298_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4298_pb : Scalar.QComplex := ((-822463669446346202544574 : Int)/10^30,(-431476734158813573080917222 : Int)/10^30)
theorem v4298_pb_checked : Scalar.distance (sourceCoefficient 67 78 1 1) v4298_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4298_pg : Scalar.QComplex := ((-93086260464937712814499 : Int)/10^30,(177437301471860042773 : Int)/10^30)
theorem v4298_pg_checked : Scalar.distance (sourceCoefficient 67 78 1 2) v4298_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4298_mb : Scalar.QComplex := ((-1194808351793869746269982 : Int)/10^30,(-431475863751201641239422302 : Int)/10^30)
theorem v4298_mb_checked : Scalar.distance (sourceCoefficient 67 78 3 1) v4298_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4298_mg : Scalar.QComplex := ((-93086072684268998636031 : Int)/10^30,(257766485735544367317 : Int)/10^30)
theorem v4298_mg_checked : Scalar.distance (sourceCoefficient 67 78 3 2) v4298_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4298_upper : Scalar.QComplex := ((999993404049080529035071972406 : Int)/10^30,(-3632059791960121047779537195 : Int)/10^30)
theorem v4298_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 78 5) 1) 14) v4298_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4298 : Material (67 : Basis) (78 : Basis) where
  plus := ![v4298_pa,v4298_pb,v4298_pg]
  minus := ![(Primitive.Addresses.material4298 1).one,v4298_mb,v4298_mg]
  upper := v4298_upper
  lower := (Primitive.Addresses.material4298 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4298_pa_checked.trans (by decide +kernel)
    · exact v4298_pb_checked.trans (by decide +kernel)
    · exact v4298_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 78 Primitive.Addresses.material4298
    · exact v4298_mb_checked.trans (by decide +kernel)
    · exact v4298_mg_checked.trans (by decide +kernel)
  upper_error := v4298_upper_checked
  lower_error := reuse_lower_error 67 78 Primitive.Addresses.material4298

def v4299_pa : Scalar.QComplex := ((999998172635734566332306846490 : Int)/10^30,(-1911733556646212349573235449 : Int)/10^30)
theorem v4299_pa_checked : Scalar.distance (sourceCoefficient 67 79 1 0) v4299_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4299_pb : Scalar.QComplex := ((-824870049843873140486204 : Int)/10^30,(-431476729399938847028532439 : Int)/10^30)
theorem v4299_pb_checked : Scalar.distance (sourceCoefficient 67 79 1 1) v4299_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4299_pg : Scalar.QComplex := ((-93086259456085877524871 : Int)/10^30,(177956451056134634294 : Int)/10^30)
theorem v4299_pg_checked : Scalar.distance (sourceCoefficient 67 79 1 2) v4299_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4299_mb : Scalar.QComplex := ((-1197214727188696728373275 : Int)/10^30,(-431475856915730783417715936 : Int)/10^30)
theorem v4299_mb_checked : Scalar.distance (sourceCoefficient 67 79 3 1) v4299_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4299_mg : Scalar.QComplex := ((-93086071227414829388384 : Int)/10^30,(258285634255922145449 : Int)/10^30)
theorem v4299_mg_checked : Scalar.distance (sourceCoefficient 67 79 3 2) v4299_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4299_upper : Scalar.QComplex := ((999993383777236804569924702178 : Int)/10^30,(-3637636836187362990128427410 : Int)/10^30)
theorem v4299_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 79 5) 1) 14) v4299_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4299 : Material (67 : Basis) (79 : Basis) where
  plus := ![v4299_pa,v4299_pb,v4299_pg]
  minus := ![(Primitive.Addresses.material4299 1).one,v4299_mb,v4299_mg]
  upper := v4299_upper
  lower := (Primitive.Addresses.material4299 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4299_pa_checked.trans (by decide +kernel)
    · exact v4299_pb_checked.trans (by decide +kernel)
    · exact v4299_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 79 Primitive.Addresses.material4299
    · exact v4299_mb_checked.trans (by decide +kernel)
    · exact v4299_mg_checked.trans (by decide +kernel)
  upper_error := v4299_upper_checked
  lower_error := reuse_lower_error 67 79 Primitive.Addresses.material4299

def v4300_pa : Scalar.QComplex := ((999998155942854832692300216022 : Int)/10^30,(-1920445492532360512496025957 : Int)/10^30)
theorem v4300_pa_checked : Scalar.distance (sourceCoefficient 67 80 1 0) v4300_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4300_pb : Scalar.QComplex := ((-828629053803006471785736 : Int)/10^30,(-431476721930297797959729815 : Int)/10^30)
theorem v4300_pb_checked : Scalar.distance (sourceCoefficient 67 80 1 1) v4300_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4300_pg : Scalar.QComplex := ((-93086257873400000041093 : Int)/10^30,(178767414007003107436 : Int)/10^30)
theorem v4300_pg_checked : Scalar.distance (sourceCoefficient 67 80 1 2) v4300_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4300_mb : Scalar.QComplex := ((-1200973723302217285517663 : Int)/10^30,(-431475846202241398159226086 : Int)/10^30)
theorem v4300_mb_checked : Scalar.distance (sourceCoefficient 67 80 3 1) v4300_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4300_mg : Scalar.QComplex := ((-93086068944905039026856 : Int)/10^30,(259096595539045418402 : Int)/10^30)
theorem v4300_mg_checked : Scalar.distance (sourceCoefficient 67 80 3 2) v4300_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4300_upper : Scalar.QComplex := ((999993352048370934171457739233 : Int)/10^30,(-3646348730287709972468155361 : Int)/10^30)
theorem v4300_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 80 5) 1) 14) v4300_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4300 : Material (67 : Basis) (80 : Basis) where
  plus := ![v4300_pa,v4300_pb,v4300_pg]
  minus := ![(Primitive.Addresses.material4300 1).one,v4300_mb,v4300_mg]
  upper := v4300_upper
  lower := (Primitive.Addresses.material4300 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4300_pa_checked.trans (by decide +kernel)
    · exact v4300_pb_checked.trans (by decide +kernel)
    · exact v4300_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 80 Primitive.Addresses.material4300
    · exact v4300_mb_checked.trans (by decide +kernel)
    · exact v4300_mg_checked.trans (by decide +kernel)
  upper_error := v4300_upper_checked
  lower_error := reuse_lower_error 67 80 Primitive.Addresses.material4300

def v4301_pa : Scalar.QComplex := ((999998105221398967506598052594 : Int)/10^30,(-1946677582929191660146885453 : Int)/10^30)
theorem v4301_pa_checked : Scalar.distance (sourceCoefficient 67 81 1 0) v4301_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4301_pb : Scalar.QComplex := ((-839947609355289567884727 : Int)/10^30,(-431476699175143027182938279 : Int)/10^30)
theorem v4301_pb_checked : Scalar.distance (sourceCoefficient 67 81 1 1) v4301_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4301_pg : Scalar.QComplex := ((-93086253058075821049713 : Int)/10^30,(181209265458468614432 : Int)/10^30)
theorem v4301_pg_checked : Scalar.distance (sourceCoefficient 67 81 1 2) v4301_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4301_mb : Scalar.QComplex := ((-1212292255003411152904723 : Int)/10^30,(-431475813679691427364772503 : Int)/10^30)
theorem v4301_mb_checked : Scalar.distance (sourceCoefficient 67 81 3 1) v4301_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4301_mg : Scalar.QComplex := ((-93086062022374827292845 : Int)/10^30,(261538441925890139574 : Int)/10^30)
theorem v4301_mg_checked : Scalar.distance (sourceCoefficient 67 81 3 2) v4301_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4301_upper : Scalar.QComplex := ((999993256052782344356706912945 : Int)/10^30,(-3672580694074292503057521421 : Int)/10^30)
theorem v4301_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 81 5) 1) 14) v4301_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4301 : Material (67 : Basis) (81 : Basis) where
  plus := ![v4301_pa,v4301_pb,v4301_pg]
  minus := ![(Primitive.Addresses.material4301 1).one,v4301_mb,v4301_mg]
  upper := v4301_upper
  lower := (Primitive.Addresses.material4301 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4301_pa_checked.trans (by decide +kernel)
    · exact v4301_pb_checked.trans (by decide +kernel)
    · exact v4301_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 81 Primitive.Addresses.material4301
    · exact v4301_mb_checked.trans (by decide +kernel)
    · exact v4301_mg_checked.trans (by decide +kernel)
  upper_error := v4301_upper_checked
  lower_error := reuse_lower_error 67 81 Primitive.Addresses.material4301

def v4302_pa : Scalar.QComplex := ((999998085821515510696208449181 : Int)/10^30,(-1956617822902402445897651595 : Int)/10^30)
theorem v4302_pa_checked : Scalar.distance (sourceCoefficient 67 82 1 0) v4302_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4302_pb : Scalar.QComplex := ((-844236598718997878394497 : Int)/10^30,(-431476690449004389805472160 : Int)/10^30)
theorem v4302_pb_checked : Scalar.distance (sourceCoefficient 67 82 1 1) v4302_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4302_pg : Scalar.QComplex := ((-93086251213859665020416 : Int)/10^30,(182134566830277323057 : Int)/10^30)
theorem v4302_pg_checked : Scalar.distance (sourceCoefficient 67 82 1 2) v4302_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4302_mb : Scalar.QComplex := ((-1216581235239868073446788 : Int)/10^30,(-431475801252351387157427758 : Int)/10^30)
theorem v4302_mb_checked : Scalar.distance (sourceCoefficient 67 82 3 1) v4302_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4302_mg : Scalar.QComplex := ((-93086059379665948105366 : Int)/10^30,(262463741361691376872 : Int)/10^30)
theorem v4302_mg_checked : Scalar.distance (sourceCoefficient 67 82 3 2) v4302_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4302_upper : Scalar.QComplex := ((999993219496975359158156727740 : Int)/10^30,(-3682520885760244608546444078 : Int)/10^30)
theorem v4302_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 82 5) 1) 14) v4302_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4302 : Material (67 : Basis) (82 : Basis) where
  plus := ![v4302_pa,v4302_pb,v4302_pg]
  minus := ![(Primitive.Addresses.material4302 1).one,v4302_mb,v4302_mg]
  upper := v4302_upper
  lower := (Primitive.Addresses.material4302 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4302_pa_checked.trans (by decide +kernel)
    · exact v4302_pb_checked.trans (by decide +kernel)
    · exact v4302_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 82 Primitive.Addresses.material4302
    · exact v4302_mb_checked.trans (by decide +kernel)
    · exact v4302_mg_checked.trans (by decide +kernel)
  upper_error := v4302_upper_checked
  lower_error := reuse_lower_error 67 82 Primitive.Addresses.material4302

def v4303_pa : Scalar.QComplex := ((999998059180856626093717814663 : Int)/10^30,(-1970186417567856769572080513 : Int)/10^30)
theorem v4303_pa_checked : Scalar.distance (sourceCoefficient 67 83 1 0) v4303_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4303_pb : Scalar.QComplex := ((-850091141244610406561023 : Int)/10^30,(-431476678445922365569678885 : Int)/10^30)
theorem v4303_pb_checked : Scalar.distance (sourceCoefficient 67 83 1 1) v4303_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4303_pg : Scalar.QComplex := ((-93086248679152673262596 : Int)/10^30,(183397618751619766731 : Int)/10^30)
theorem v4303_pg_checked : Scalar.distance (sourceCoefficient 67 83 1 2) v4303_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4303_mb : Scalar.QComplex := ((-1222435765227447665347244 : Int)/10^30,(-431475784197067311421164415 : Int)/10^30)
theorem v4303_mb_checked : Scalar.distance (sourceCoefficient 67 83 3 1) v4303_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4303_mg : Scalar.QComplex := ((-93086055755002977763112 : Int)/10^30,(263726790625403890983 : Int)/10^30)
theorem v4303_mg_checked : Scalar.distance (sourceCoefficient 67 83 3 2) v4303_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4303_upper : Scalar.QComplex := ((999993169438192693406007242868 : Int)/10^30,(-3696089414237510643990899056 : Int)/10^30)
theorem v4303_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 83 5) 1) 14) v4303_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4303 : Material (67 : Basis) (83 : Basis) where
  plus := ![v4303_pa,v4303_pb,v4303_pg]
  minus := ![(Primitive.Addresses.material4303 1).one,v4303_mb,v4303_mg]
  upper := v4303_upper
  lower := (Primitive.Addresses.material4303 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4303_pa_checked.trans (by decide +kernel)
    · exact v4303_pb_checked.trans (by decide +kernel)
    · exact v4303_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 83 Primitive.Addresses.material4303
    · exact v4303_mb_checked.trans (by decide +kernel)
    · exact v4303_mg_checked.trans (by decide +kernel)
  upper_error := v4303_upper_checked
  lower_error := reuse_lower_error 67 83 Primitive.Addresses.material4303

def v4304_pa : Scalar.QComplex := ((999997989332987973672543104916 : Int)/10^30,(-2005325405332217313578630418 : Int)/10^30)
theorem v4304_pa_checked : Scalar.distance (sourceCoefficient 67 84 1 0) v4304_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v4304_pb : Scalar.QComplex := ((-865252821508988612086728 : Int)/10^30,(-431476646868860332802031893 : Int)/10^30)
theorem v4304_pb_checked : Scalar.distance (sourceCoefficient 67 84 1 1) v4304_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4304_pg : Scalar.QComplex := ((-93086242022010039772065 : Int)/10^30,(186668581341998849286 : Int)/10^30)
theorem v4304_pg_checked : Scalar.distance (sourceCoefficient 67 84 1 2) v4304_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4304_mb : Scalar.QComplex := ((-1237597412596857029227513 : Int)/10^30,(-431475739536169824808738115 : Int)/10^30)
theorem v4304_mb_checked : Scalar.distance (sourceCoefficient 67 84 3 1) v4304_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v4304_mg : Scalar.QComplex := ((-93086046275169426220224 : Int)/10^30,(266997746253039844637 : Int)/10^30)
theorem v4304_mg_checked : Scalar.distance (sourceCoefficient 67 84 3 2) v4304_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v4304_upper : Scalar.QComplex := ((999993038943722973962364550214 : Int)/10^30,(-3731228229115391883508211371 : Int)/10^30)
theorem v4304_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 67 84 5) 1) 14) v4304_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material4304 : Material (67 : Basis) (84 : Basis) where
  plus := ![v4304_pa,v4304_pb,v4304_pg]
  minus := ![(Primitive.Addresses.material4304 1).one,v4304_mb,v4304_mg]
  upper := v4304_upper
  lower := (Primitive.Addresses.material4304 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v4304_pa_checked.trans (by decide +kernel)
    · exact v4304_pb_checked.trans (by decide +kernel)
    · exact v4304_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 67 84 Primitive.Addresses.material4304
    · exact v4304_mb_checked.trans (by decide +kernel)
    · exact v4304_mg_checked.trans (by decide +kernel)
  upper_error := v4304_upper_checked
  lower_error := reuse_lower_error 67 84 Primitive.Addresses.material4304

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
