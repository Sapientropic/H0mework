import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B077
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B078

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1857_pa : Scalar.QComplex := ((999999702175919141724242876368 : Int)/10^30,(-771782400043800153494411188 : Int)/10^30)
theorem v1857_pa_checked : Scalar.distance (sourceCoefficient 21 52 1 0) v1857_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1857_pb : Scalar.QComplex := ((-333006745247907645928998 : Int)/10^30,(-431477377628177381986728935 : Int)/10^30)
theorem v1857_pb_checked : Scalar.distance (sourceCoefficient 21 52 1 1) v1857_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1857_pg : Scalar.QComplex := ((-93086400569785072976526 : Int)/10^30,(71842467039604002400 : Int)/10^30)
theorem v1857_pg_checked : Scalar.distance (sourceCoefficient 21 52 1 2) v1857_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1857_mb : Scalar.QComplex := ((-705352165127693537991169 : Int)/10^30,(-431476929599607118803343222 : Int)/10^30)
theorem v1857_mb_checked : Scalar.distance (sourceCoefficient 21 52 3 1) v1857_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1857_mg : Scalar.QComplex := ((-93086303912650491598556 : Int)/10^30,(152171811525244292148 : Int)/10^30)
theorem v1857_mg_checked : Scalar.distance (sourceCoefficient 21 52 3 2) v1857_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1857_upper : Scalar.QComplex := ((999996880767424044203857037468 : Int)/10^30,(-2497690017255890259465298016 : Int)/10^30)
theorem v1857_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 52 5) 1) 14) v1857_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1857 : Material (21 : Basis) (52 : Basis) where
  plus := ![v1857_pa,v1857_pb,v1857_pg]
  minus := ![(Primitive.Addresses.material1857 1).one,v1857_mb,v1857_mg]
  upper := v1857_upper
  lower := (Primitive.Addresses.material1857 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1857_pa_checked.trans (by decide +kernel)
    · exact v1857_pb_checked.trans (by decide +kernel)
    · exact v1857_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 52 Primitive.Addresses.material1857
    · exact v1857_mb_checked.trans (by decide +kernel)
    · exact v1857_mg_checked.trans (by decide +kernel)
  upper_error := v1857_upper_checked
  lower_error := reuse_lower_error 21 52 Primitive.Addresses.material1857

def v1858_pa : Scalar.QComplex := ((999999699311393307127158922007 : Int)/10^30,(-775485088813516444169847494 : Int)/10^30)
theorem v1858_pa_checked : Scalar.distance (sourceCoefficient 21 53 1 0) v1858_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1858_pb : Scalar.QComplex := ((-334604371975704294505320 : Int)/10^30,(-431477376149066519513169637 : Int)/10^30)
theorem v1858_pb_checked : Scalar.distance (sourceCoefficient 21 53 1 1) v1858_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1858_pg : Scalar.QComplex := ((-93086400276910051910974 : Int)/10^30,(72187137091919806645 : Int)/10^30)
theorem v1858_pg_checked : Scalar.distance (sourceCoefficient 21 53 1 2) v1858_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1858_mb : Scalar.QComplex := ((-706949789984214683025954 : Int)/10^30,(-431476926741816895418594722 : Int)/10^30)
theorem v1858_mb_checked : Scalar.distance (sourceCoefficient 21 53 3 1) v1858_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1858_mg : Scalar.QComplex := ((-93086303322340847798121 : Int)/10^30,(152516481196485731138 : Int)/10^30)
theorem v1858_mg_checked : Scalar.distance (sourceCoefficient 21 53 3 2) v1858_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1858_upper : Scalar.QComplex := ((999996871512397564752435614594 : Int)/10^30,(-2501392695566974853263839497 : Int)/10^30)
theorem v1858_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 53 5) 1) 14) v1858_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1858 : Material (21 : Basis) (53 : Basis) where
  plus := ![v1858_pa,v1858_pb,v1858_pg]
  minus := ![(Primitive.Addresses.material1858 1).one,v1858_mb,v1858_mg]
  upper := v1858_upper
  lower := (Primitive.Addresses.material1858 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1858_pa_checked.trans (by decide +kernel)
    · exact v1858_pb_checked.trans (by decide +kernel)
    · exact v1858_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 53 Primitive.Addresses.material1858
    · exact v1858_mb_checked.trans (by decide +kernel)
    · exact v1858_mg_checked.trans (by decide +kernel)
  upper_error := v1858_upper_checked
  lower_error := reuse_lower_error 21 53 Primitive.Addresses.material1858

def v1859_pa : Scalar.QComplex := ((999999697849794044560771514506 : Int)/10^30,(-777367558247790205566596061 : Int)/10^30)
theorem v1859_pa_checked : Scalar.distance (sourceCoefficient 21 54 1 0) v1859_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1859_pb : Scalar.QComplex := ((-335416615095439657171172 : Int)/10^30,(-431477375394053243551444102 : Int)/10^30)
theorem v1859_pb_checked : Scalar.distance (sourceCoefficient 21 54 1 1) v1859_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1859_pg : Scalar.QComplex := ((-93086400127439705346073 : Int)/10^30,(72362369437449419709 : Int)/10^30)
theorem v1859_pg_checked : Scalar.distance (sourceCoefficient 21 54 1 2) v1859_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1859_mb : Scalar.QComplex := ((-707762032149972358250599 : Int)/10^30,(-431476925285874670323322188 : Int)/10^30)
theorem v1859_mb_checked : Scalar.distance (sourceCoefficient 21 54 3 1) v1859_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1859_mg : Scalar.QComplex := ((-93086303021652934867677 : Int)/10^30,(152691713347782156256 : Int)/10^30)
theorem v1859_mg_checked : Scalar.distance (sourceCoefficient 21 54 3 2) v1859_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1859_upper : Scalar.QComplex := ((999996866801829011802992242729 : Int)/10^30,(-2503275159674943790762871277 : Int)/10^30)
theorem v1859_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 54 5) 1) 14) v1859_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1859 : Material (21 : Basis) (54 : Basis) where
  plus := ![v1859_pa,v1859_pb,v1859_pg]
  minus := ![(Primitive.Addresses.material1859 1).one,v1859_mb,v1859_mg]
  upper := v1859_upper
  lower := (Primitive.Addresses.material1859 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1859_pa_checked.trans (by decide +kernel)
    · exact v1859_pb_checked.trans (by decide +kernel)
    · exact v1859_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 54 Primitive.Addresses.material1859
    · exact v1859_mb_checked.trans (by decide +kernel)
    · exact v1859_mg_checked.trans (by decide +kernel)
  upper_error := v1859_upper_checked
  lower_error := reuse_lower_error 21 54 Primitive.Addresses.material1859

def v1860_pa : Scalar.QComplex := ((999999685804467330274875943808 : Int)/10^30,(-792711149549832873107327023 : Int)/10^30)
theorem v1860_pa_checked : Scalar.distance (sourceCoefficient 21 55 1 0) v1860_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1860_pb : Scalar.QComplex := ((-342037028781300446986817 : Int)/10^30,(-431477369164078143560642614 : Int)/10^30)
theorem v1860_pb_checked : Scalar.distance (sourceCoefficient 21 55 1 1) v1860_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1860_pg : Scalar.QComplex := ((-93086398894787890893804 : Int)/10^30,(73790649460034014394 : Int)/10^30)
theorem v1860_pg_checked : Scalar.distance (sourceCoefficient 21 55 1 2) v1860_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1860_mb : Scalar.QComplex := ((-714382437994562641338211 : Int)/10^30,(-431476913342783051502845484 : Int)/10^30)
theorem v1860_mb_checked : Scalar.distance (sourceCoefficient 21 55 3 1) v1860_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1860_mg : Scalar.QComplex := ((-93086300556460247241782 : Int)/10^30,(154119991774829823615 : Int)/10^30)
theorem v1860_mg_checked : Scalar.distance (sourceCoefficient 21 55 3 2) v1860_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1860_upper : Scalar.QComplex := ((999996828274873610020178573373 : Int)/10^30,(-2518618707335368433402037153 : Int)/10^30)
theorem v1860_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 55 5) 1) 14) v1860_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1860 : Material (21 : Basis) (55 : Basis) where
  plus := ![v1860_pa,v1860_pb,v1860_pg]
  minus := ![(Primitive.Addresses.material1860 1).one,v1860_mb,v1860_mg]
  upper := v1860_upper
  lower := (Primitive.Addresses.material1860 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1860_pa_checked.trans (by decide +kernel)
    · exact v1860_pb_checked.trans (by decide +kernel)
    · exact v1860_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 55 Primitive.Addresses.material1860
    · exact v1860_mb_checked.trans (by decide +kernel)
    · exact v1860_mg_checked.trans (by decide +kernel)
  upper_error := v1860_upper_checked
  lower_error := reuse_lower_error 21 55 Primitive.Addresses.material1860

def v1861_pa : Scalar.QComplex := ((999999682911208148905188104685 : Int)/10^30,(-796352612325022580636715773 : Int)/10^30)
theorem v1861_pa_checked : Scalar.distance (sourceCoefficient 21 56 1 0) v1861_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1861_pb : Scalar.QComplex := ((-343608237853981399640038 : Int)/10^30,(-431477367665644701762374604 : Int)/10^30)
theorem v1861_pb_checked : Scalar.distance (sourceCoefficient 21 56 1 1) v1861_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1861_pg : Scalar.QComplex := ((-93086398598491212723837 : Int)/10^30,(74129620201508508083 : Int)/10^30)
theorem v1861_pg_checked : Scalar.distance (sourceCoefficient 21 56 1 2) v1861_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1861_mb : Scalar.QComplex := ((-715953645189130075095395 : Int)/10^30,(-431476910488467502545894523 : Int)/10^30)
theorem v1861_mb_checked : Scalar.distance (sourceCoefficient 21 56 3 1) v1861_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1861_mg : Scalar.QComplex := ((-93086299967647196179592 : Int)/10^30,(154458962134399329972 : Int)/10^30)
theorem v1861_mg_checked : Scalar.distance (sourceCoefficient 21 56 3 2) v1861_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1861_upper : Scalar.QComplex := ((999996819096784338765145512346 : Int)/10^30,(-2522260159693524220930684096 : Int)/10^30)
theorem v1861_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 56 5) 1) 14) v1861_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1861 : Material (21 : Basis) (56 : Basis) where
  plus := ![v1861_pa,v1861_pb,v1861_pg]
  minus := ![(Primitive.Addresses.material1861 1).one,v1861_mb,v1861_mg]
  upper := v1861_upper
  lower := (Primitive.Addresses.material1861 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1861_pa_checked.trans (by decide +kernel)
    · exact v1861_pb_checked.trans (by decide +kernel)
    · exact v1861_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 56 Primitive.Addresses.material1861
    · exact v1861_mb_checked.trans (by decide +kernel)
    · exact v1861_mg_checked.trans (by decide +kernel)
  upper_error := v1861_upper_checked
  lower_error := reuse_lower_error 21 56 Primitive.Addresses.material1861

def v1862_pa : Scalar.QComplex := ((999999673462522545738461898961 : Int)/10^30,(-808130464889054219108919723 : Int)/10^30)
theorem v1862_pa_checked : Scalar.distance (sourceCoefficient 21 57 1 0) v1862_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1862_pb : Scalar.QComplex := ((-348690115622317723385613 : Int)/10^30,(-431477362766911092490727654 : Int)/10^30)
theorem v1862_pb_checked : Scalar.distance (sourceCoefficient 21 57 1 1) v1862_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1862_pg : Scalar.QComplex := ((-93086397630295624807230 : Int)/10^30,(75225978355919369658 : Int)/10^30)
theorem v1862_pg_checked : Scalar.distance (sourceCoefficient 21 57 1 2) v1862_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1862_mb : Scalar.QComplex := ((-721035516837864578371930 : Int)/10^30,(-431476901204304082500693780 : Int)/10^30)
theorem v1862_mb_checked : Scalar.distance (sourceCoefficient 21 57 3 1) v1862_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1862_mg : Scalar.QComplex := ((-93086298053344259648150 : Int)/10^30,(155555319045076758156 : Int)/10^30)
theorem v1862_mg_checked : Scalar.distance (sourceCoefficient 21 57 3 2) v1862_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1862_upper : Scalar.QComplex := ((999996789320607761225210075767 : Int)/10^30,(-2534037978408253816023418652 : Int)/10^30)
theorem v1862_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 57 5) 1) 14) v1862_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1862 : Material (21 : Basis) (57 : Basis) where
  plus := ![v1862_pa,v1862_pb,v1862_pg]
  minus := ![(Primitive.Addresses.material1862 1).one,v1862_mb,v1862_mg]
  upper := v1862_upper
  lower := (Primitive.Addresses.material1862 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1862_pa_checked.trans (by decide +kernel)
    · exact v1862_pb_checked.trans (by decide +kernel)
    · exact v1862_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 57 Primitive.Addresses.material1862
    · exact v1862_mb_checked.trans (by decide +kernel)
    · exact v1862_mg_checked.trans (by decide +kernel)
  upper_error := v1862_upper_checked
  lower_error := reuse_lower_error 21 57 Primitive.Addresses.material1862

def v1863_pa : Scalar.QComplex := ((999999668277704609040442050476 : Int)/10^30,(-814521013075929095426696629 : Int)/10^30)
theorem v1863_pa_checked : Scalar.distance (sourceCoefficient 21 58 1 0) v1863_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1863_pb : Scalar.QComplex := ((-351447493030999142724549 : Int)/10^30,(-431477360075507787342519900 : Int)/10^30)
theorem v1863_pb_checked : Scalar.distance (sourceCoefficient 21 58 1 1) v1863_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1863_pg : Scalar.QComplex := ((-93086397098657509125838 : Int)/10^30,(75820851619853679037 : Int)/10^30)
theorem v1863_pg_checked : Scalar.distance (sourceCoefficient 21 58 1 2) v1863_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1863_mb : Scalar.QComplex := ((-723792890897288534047962 : Int)/10^30,(-431476896133409263461298912 : Int)/10^30)
theorem v1863_mb_checked : Scalar.distance (sourceCoefficient 21 58 3 1) v1863_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1863_mg : Scalar.QComplex := ((-93086297008357507241855 : Int)/10^30,(156150191628732814579 : Int)/10^30)
theorem v1863_mg_checked : Scalar.distance (sourceCoefficient 21 58 3 2) v1863_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1863_upper : Scalar.QComplex := ((999996773106291122161204960402 : Int)/10^30,(-2540428508128632458782110508 : Int)/10^30)
theorem v1863_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 58 5) 1) 14) v1863_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1863 : Material (21 : Basis) (58 : Basis) where
  plus := ![v1863_pa,v1863_pb,v1863_pg]
  minus := ![(Primitive.Addresses.material1863 1).one,v1863_mb,v1863_mg]
  upper := v1863_upper
  lower := (Primitive.Addresses.material1863 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1863_pa_checked.trans (by decide +kernel)
    · exact v1863_pb_checked.trans (by decide +kernel)
    · exact v1863_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 58 Primitive.Addresses.material1863
    · exact v1863_mb_checked.trans (by decide +kernel)
    · exact v1863_mg_checked.trans (by decide +kernel)
  upper_error := v1863_upper_checked
  lower_error := reuse_lower_error 21 58 Primitive.Addresses.material1863

def v1864_pa : Scalar.QComplex := ((999999653815607090812621917922 : Int)/10^30,(-832086934144949101099886245 : Int)/10^30)
theorem v1864_pa_checked : Scalar.distance (sourceCoefficient 21 59 1 0) v1864_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1864_pb : Scalar.QComplex := ((-359026791731193832494433 : Int)/10^30,(-431477352556505405359263462 : Int)/10^30)
theorem v1864_pb_checked : Scalar.distance (sourceCoefficient 21 59 1 1) v1864_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1864_pg : Scalar.QComplex := ((-93086395614474831040531 : Int)/10^30,(77456000351510656411 : Int)/10^30)
theorem v1864_pg_checked : Scalar.distance (sourceCoefficient 21 59 1 2) v1864_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1864_mb : Scalar.QComplex := ((-731372180286803514317403 : Int)/10^30,(-431476882073816261819864611 : Int)/10^30)
theorem v1864_mb_checked : Scalar.distance (sourceCoefficient 21 59 3 1) v1864_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1864_mg : Scalar.QComplex := ((-93086294113115670730684 : Int)/10^30,(157785338470766383087 : Int)/10^30)
theorem v1864_mg_checked : Scalar.distance (sourceCoefficient 21 59 3 2) v1864_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1864_upper : Scalar.QComplex := ((999996728327028946311383239261 : Int)/10^30,(-2557994378075008144964308138 : Int)/10^30)
theorem v1864_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 59 5) 1) 14) v1864_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1864 : Material (21 : Basis) (59 : Basis) where
  plus := ![v1864_pa,v1864_pb,v1864_pg]
  minus := ![(Primitive.Addresses.material1864 1).one,v1864_mb,v1864_mg]
  upper := v1864_upper
  lower := (Primitive.Addresses.material1864 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1864_pa_checked.trans (by decide +kernel)
    · exact v1864_pb_checked.trans (by decide +kernel)
    · exact v1864_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 59 Primitive.Addresses.material1864
    · exact v1864_mb_checked.trans (by decide +kernel)
    · exact v1864_mg_checked.trans (by decide +kernel)
  upper_error := v1864_upper_checked
  lower_error := reuse_lower_error 21 59 Primitive.Addresses.material1864

def v1865_pa : Scalar.QComplex := ((999999636748942175574800304050 : Int)/10^30,(-852350857157731371767202483 : Int)/10^30)
theorem v1865_pa_checked : Scalar.distance (sourceCoefficient 21 60 1 0) v1865_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1865_pb : Scalar.QComplex := ((-367770217307476861169919 : Int)/10^30,(-431477343662128651567629775 : Int)/10^30)
theorem v1865_pb_checked : Scalar.distance (sourceCoefficient 21 60 1 1) v1865_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1865_pg : Scalar.QComplex := ((-93086393860706424657486 : Int)/10^30,(79342296418068408361 : Int)/10^30)
theorem v1865_pg_checked : Scalar.distance (sourceCoefficient 21 60 1 2) v1865_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1865_mb : Scalar.QComplex := ((-740115594932063055989813 : Int)/10^30,(-431476865634260336748746672 : Int)/10^30)
theorem v1865_mb_checked : Scalar.distance (sourceCoefficient 21 60 3 1) v1865_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1865_mg : Scalar.QComplex := ((-93086290731559367537566 : Int)/10^30,(159671632321546753557 : Int)/10^30)
theorem v1865_mg_checked : Scalar.distance (sourceCoefficient 21 60 3 2) v1865_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1865_upper : Scalar.QComplex := ((999996676286696658539446003132 : Int)/10^30,(-2578258241451542087747382026 : Int)/10^30)
theorem v1865_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 60 5) 1) 14) v1865_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1865 : Material (21 : Basis) (60 : Basis) where
  plus := ![v1865_pa,v1865_pb,v1865_pg]
  minus := ![(Primitive.Addresses.material1865 1).one,v1865_mb,v1865_mg]
  upper := v1865_upper
  lower := (Primitive.Addresses.material1865 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1865_pa_checked.trans (by decide +kernel)
    · exact v1865_pb_checked.trans (by decide +kernel)
    · exact v1865_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 60 Primitive.Addresses.material1865
    · exact v1865_mb_checked.trans (by decide +kernel)
    · exact v1865_mg_checked.trans (by decide +kernel)
  upper_error := v1865_upper_checked
  lower_error := reuse_lower_error 21 60 Primitive.Addresses.material1865

def v1866_pa : Scalar.QComplex := ((999999631737566565790557912676 : Int)/10^30,(-858210190600880132248284630 : Int)/10^30)
theorem v1866_pa_checked : Scalar.distance (sourceCoefficient 21 61 1 0) v1866_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1866_pb : Scalar.QComplex := ((-370298387466275377020371 : Int)/10^30,(-431477341046281389616232409 : Int)/10^30)
theorem v1866_pb_checked : Scalar.distance (sourceCoefficient 21 61 1 1) v1866_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1866_pg : Scalar.QComplex := ((-93086393345291056337844 : Int)/10^30,(79887720794857198836 : Int)/10^30)
theorem v1866_pg_checked : Scalar.distance (sourceCoefficient 21 61 1 2) v1866_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1866_mb : Scalar.QComplex := ((-742643761892149904958560 : Int)/10^30,(-431476860836717066310817119 : Int)/10^30)
theorem v1866_mb_checked : Scalar.distance (sourceCoefficient 21 61 3 1) v1866_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1866_mg : Scalar.QComplex := ((-93086289745467518963929 : Int)/10^30,(160217056050468872015 : Int)/10^30)
theorem v1866_mg_checked : Scalar.distance (sourceCoefficient 21 61 3 2) v1866_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1866_upper : Scalar.QComplex := ((999996661162650544313422228494 : Int)/10^30,(-2584117557518722296270402698 : Int)/10^30)
theorem v1866_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 61 5) 1) 14) v1866_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1866 : Material (21 : Basis) (61 : Basis) where
  plus := ![v1866_pa,v1866_pb,v1866_pg]
  minus := ![(Primitive.Addresses.material1866 1).one,v1866_mb,v1866_mg]
  upper := v1866_upper
  lower := (Primitive.Addresses.material1866 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1866_pa_checked.trans (by decide +kernel)
    · exact v1866_pb_checked.trans (by decide +kernel)
    · exact v1866_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 61 Primitive.Addresses.material1866
    · exact v1866_mb_checked.trans (by decide +kernel)
    · exact v1866_mg_checked.trans (by decide +kernel)
  upper_error := v1866_upper_checked
  lower_error := reuse_lower_error 21 61 Primitive.Addresses.material1866

def v1867_pa : Scalar.QComplex := ((999999624395072811015018370611 : Int)/10^30,(-866723550677439844663932092 : Int)/10^30)
theorem v1867_pa_checked : Scalar.distance (sourceCoefficient 21 62 1 0) v1867_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1867_pb : Scalar.QComplex := ((-373971710209436339887121 : Int)/10^30,(-431477337210370498916052776 : Int)/10^30)
theorem v1867_pb_checked : Scalar.distance (sourceCoefficient 21 62 1 1) v1867_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1867_pg : Scalar.QComplex := ((-93086392589770441474481 : Int)/10^30,(80680199009040236440 : Int)/10^30)
theorem v1867_pg_checked : Scalar.distance (sourceCoefficient 21 62 1 2) v1867_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1867_mb : Scalar.QComplex := ((-746317079957346595742721 : Int)/10^30,(-431476853830895516862579726 : Int)/10^30)
theorem v1867_mb_checked : Scalar.distance (sourceCoefficient 21 62 3 1) v1867_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1867_mg : Scalar.QComplex := ((-93086288306074178469280 : Int)/10^30,(161009533317595789193 : Int)/10^30)
theorem v1867_mg_checked : Scalar.distance (sourceCoefficient 21 62 3 2) v1867_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1867_upper : Scalar.QComplex := ((999996639126880559170822815716 : Int)/10^30,(-2592630892243154109262117572 : Int)/10^30)
theorem v1867_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 62 5) 1) 14) v1867_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1867 : Material (21 : Basis) (62 : Basis) where
  plus := ![v1867_pa,v1867_pb,v1867_pg]
  minus := ![(Primitive.Addresses.material1867 1).one,v1867_mb,v1867_mg]
  upper := v1867_upper
  lower := (Primitive.Addresses.material1867 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1867_pa_checked.trans (by decide +kernel)
    · exact v1867_pb_checked.trans (by decide +kernel)
    · exact v1867_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 62 Primitive.Addresses.material1867
    · exact v1867_mb_checked.trans (by decide +kernel)
    · exact v1867_mg_checked.trans (by decide +kernel)
  upper_error := v1867_upper_checked
  lower_error := reuse_lower_error 21 62 Primitive.Addresses.material1867

def v1868_pa : Scalar.QComplex := ((999999602597111507004512347510 : Int)/10^30,(-891518714922426736561978206 : Int)/10^30)
theorem v1868_pa_checked : Scalar.distance (sourceCoefficient 21 63 1 0) v1868_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1868_pb : Scalar.QComplex := ((-384670263885087977222864 : Int)/10^30,(-431477325800709743023138691 : Int)/10^30)
theorem v1868_pb_checked : Scalar.distance (sourceCoefficient 21 63 1 1) v1868_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1868_pg : Scalar.QComplex := ((-93086390344470150912038 : Int)/10^30,(82988292076456403500 : Int)/10^30)
theorem v1868_pg_checked : Scalar.distance (sourceCoefficient 21 63 1 2) v1868_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1868_mb : Scalar.QComplex := ((-757015619803414391284892 : Int)/10^30,(-431476833188869032191074554 : Int)/10^30)
theorem v1868_mb_checked : Scalar.distance (sourceCoefficient 21 63 3 1) v1868_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1868_mg : Scalar.QComplex := ((-93086284068994359407451 : Int)/10^30,(163317623588010396006 : Int)/10^30)
theorem v1868_mg_checked : Scalar.distance (sourceCoefficient 21 63 3 2) v1868_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1868_upper : Scalar.QComplex := ((999996574534747633544694110776 : Int)/10^30,(-2617425981937352787726546332 : Int)/10^30)
theorem v1868_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 63 5) 1) 14) v1868_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1868 : Material (21 : Basis) (63 : Basis) where
  plus := ![v1868_pa,v1868_pb,v1868_pg]
  minus := ![(Primitive.Addresses.material1868 1).one,v1868_mb,v1868_mg]
  upper := v1868_upper
  lower := (Primitive.Addresses.material1868 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1868_pa_checked.trans (by decide +kernel)
    · exact v1868_pb_checked.trans (by decide +kernel)
    · exact v1868_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 63 Primitive.Addresses.material1868
    · exact v1868_mb_checked.trans (by decide +kernel)
    · exact v1868_mg_checked.trans (by decide +kernel)
  upper_error := v1868_upper_checked
  lower_error := reuse_lower_error 21 63 Primitive.Addresses.material1868

def v1869_pa : Scalar.QComplex := ((999999570376220950185124455215 : Int)/10^30,(-926955971728451742458637651 : Int)/10^30)
theorem v1869_pa_checked : Scalar.distance (sourceCoefficient 21 64 1 0) v1869_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1869_pb : Scalar.QComplex := ((-399960639964270839248586 : Int)/10^30,(-431477308880033989371766335 : Int)/10^30)
theorem v1869_pb_checked : Scalar.distance (sourceCoefficient 21 64 1 1) v1869_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1869_pg : Scalar.QComplex := ((-93086387019583423204110 : Int)/10^30,(86287019405384048781 : Int)/10^30)
theorem v1869_pg_checked : Scalar.distance (sourceCoefficient 21 64 1 2) v1869_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1869_mb : Scalar.QComplex := ((-772305975587510337867473 : Int)/10^30,(-431476803073293675520394771 : Int)/10^30)
theorem v1869_mb_checked : Scalar.distance (sourceCoefficient 21 64 3 1) v1869_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1869_mg : Scalar.QComplex := ((-93086277897455754005997 : Int)/10^30,(166616346819443598768 : Int)/10^30)
theorem v1869_mg_checked : Scalar.distance (sourceCoefficient 21 64 3 2) v1869_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1869_upper : Scalar.QComplex := ((999996481152414661582167344968 : Int)/10^30,(-2652863130353412488938204552 : Int)/10^30)
theorem v1869_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 64 5) 1) 14) v1869_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1869 : Material (21 : Basis) (64 : Basis) where
  plus := ![v1869_pa,v1869_pb,v1869_pg]
  minus := ![(Primitive.Addresses.material1869 1).one,v1869_mb,v1869_mg]
  upper := v1869_upper
  lower := (Primitive.Addresses.material1869 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1869_pa_checked.trans (by decide +kernel)
    · exact v1869_pb_checked.trans (by decide +kernel)
    · exact v1869_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 64 Primitive.Addresses.material1869
    · exact v1869_mb_checked.trans (by decide +kernel)
    · exact v1869_mg_checked.trans (by decide +kernel)
  upper_error := v1869_upper_checked
  lower_error := reuse_lower_error 21 64 Primitive.Addresses.material1869

def v1870_pa : Scalar.QComplex := ((999999536389950249557405608628 : Int)/10^30,(-962922574544083974751047068 : Int)/10^30)
theorem v1870_pa_checked : Scalar.distance (sourceCoefficient 21 65 1 0) v1870_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1870_pb : Scalar.QComplex := ((-415479416496521325132804 : Int)/10^30,(-431477290967870167940501386 : Int)/10^30)
theorem v1870_pb_checked : Scalar.distance (sourceCoefficient 21 65 1 1) v1870_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1870_pg : Scalar.QComplex := ((-93086383505579019054408 : Int)/10^30,(89635021615886932645 : Int)/10^30)
theorem v1870_pg_checked : Scalar.distance (sourceCoefficient 21 65 1 2) v1870_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1870_mb : Scalar.QComplex := ((-787824730884020433685955 : Int)/10^30,(-431476771769131316023327028 : Int)/10^30)
theorem v1870_mb_checked : Scalar.distance (sourceCoefficient 21 65 3 1) v1870_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1870_mg : Scalar.QComplex := ((-93086271494277539038775 : Int)/10^30,(169964344750904712503 : Int)/10^30)
theorem v1870_mg_checked : Scalar.distance (sourceCoefficient 21 65 3 2) v1870_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1870_upper : Scalar.QComplex := ((999996385091100984450450060473 : Int)/10^30,(-2688829620943794742408351508 : Int)/10^30)
theorem v1870_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 65 5) 1) 14) v1870_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1870 : Material (21 : Basis) (65 : Basis) where
  plus := ![v1870_pa,v1870_pb,v1870_pg]
  minus := ![(Primitive.Addresses.material1870 1).one,v1870_mb,v1870_mg]
  upper := v1870_upper
  lower := (Primitive.Addresses.material1870 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1870_pa_checked.trans (by decide +kernel)
    · exact v1870_pb_checked.trans (by decide +kernel)
    · exact v1870_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 65 Primitive.Addresses.material1870
    · exact v1870_mb_checked.trans (by decide +kernel)
    · exact v1870_mg_checked.trans (by decide +kernel)
  upper_error := v1870_upper_checked
  lower_error := reuse_lower_error 21 65 Primitive.Addresses.material1870

def v1871_pa : Scalar.QComplex := ((999999519299824240775118458577 : Int)/10^30,(-980510132760386514575540202 : Int)/10^30)
theorem v1871_pa_checked : Scalar.distance (sourceCoefficient 21 66 1 0) v1871_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1871_pb : Scalar.QComplex := ((-423068050364947927368477 : Int)/10^30,(-431477281937941516645220521 : Int)/10^30)
theorem v1871_pb_checked : Scalar.distance (sourceCoefficient 21 66 1 1) v1871_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1871_pg : Scalar.QComplex := ((-93086381736096757187621 : Int)/10^30,(91272184388799327542 : Int)/10^30)
theorem v1871_pg_checked : Scalar.distance (sourceCoefficient 21 66 1 2) v1871_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1871_mb : Scalar.QComplex := ((-795413354134430095826953 : Int)/10^30,(-431476756190556777913000334 : Int)/10^30)
theorem v1871_mb_checked : Scalar.distance (sourceCoefficient 21 66 3 1) v1871_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1871_mg : Scalar.QComplex := ((-93086268311998198081825 : Int)/10^30,(171601505387243087542 : Int)/10^30)
theorem v1871_mg_checked : Scalar.distance (sourceCoefficient 21 66 3 2) v1871_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1871_upper : Scalar.QComplex := ((999996337646470478882902231453 : Int)/10^30,(-2706417123469488211727654771 : Int)/10^30)
theorem v1871_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 66 5) 1) 14) v1871_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1871 : Material (21 : Basis) (66 : Basis) where
  plus := ![v1871_pa,v1871_pb,v1871_pg]
  minus := ![(Primitive.Addresses.material1871 1).one,v1871_mb,v1871_mg]
  upper := v1871_upper
  lower := (Primitive.Addresses.material1871 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1871_pa_checked.trans (by decide +kernel)
    · exact v1871_pb_checked.trans (by decide +kernel)
    · exact v1871_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 66 Primitive.Addresses.material1871
    · exact v1871_mb_checked.trans (by decide +kernel)
    · exact v1871_mg_checked.trans (by decide +kernel)
  upper_error := v1871_upper_checked
  lower_error := reuse_lower_error 21 66 Primitive.Addresses.material1871

def v1872_pa : Scalar.QComplex := ((999999489922323669367503785110 : Int)/10^30,(-1010027273137725277321954393 : Int)/10^30)
theorem v1872_pa_checked : Scalar.distance (sourceCoefficient 21 67 1 0) v1872_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1872_pb : Scalar.QComplex := ((-435804029079741008135411 : Int)/10^30,(-431477266383092205316118032 : Int)/10^30)
theorem v1872_pb_checked : Scalar.distance (sourceCoefficient 21 67 1 1) v1872_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1872_pg : Scalar.QComplex := ((-93086378690881398378362 : Int)/10^30,(94019829192832599774 : Int)/10^30)
theorem v1872_pg_checked : Scalar.distance (sourceCoefficient 21 67 1 2) v1872_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1872_mb : Scalar.QComplex := ((-808149314683901846824455 : Int)/10^30,(-431476729645137234686774043 : Int)/10^30)
theorem v1872_mb_checked : Scalar.distance (sourceCoefficient 21 67 3 1) v1872_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1872_mg : Scalar.QComplex := ((-93086262895690256592885 : Int)/10^30,(174349146540318922417 : Int)/10^30)
theorem v1872_mg_checked : Scalar.distance (sourceCoefficient 21 67 3 2) v1872_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1872_upper : Scalar.QComplex := ((999996257325107144582169699611 : Int)/10^30,(-2735934169181612829086761903 : Int)/10^30)
theorem v1872_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 67 5) 1) 14) v1872_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1872 : Material (21 : Basis) (67 : Basis) where
  plus := ![v1872_pa,v1872_pb,v1872_pg]
  minus := ![(Primitive.Addresses.material1872 1).one,v1872_mb,v1872_mg]
  upper := v1872_upper
  lower := (Primitive.Addresses.material1872 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1872_pa_checked.trans (by decide +kernel)
    · exact v1872_pb_checked.trans (by decide +kernel)
    · exact v1872_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 67 Primitive.Addresses.material1872
    · exact v1872_mb_checked.trans (by decide +kernel)
    · exact v1872_mg_checked.trans (by decide +kernel)
  upper_error := v1872_upper_checked
  lower_error := reuse_lower_error 21 67 Primitive.Addresses.material1872

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
