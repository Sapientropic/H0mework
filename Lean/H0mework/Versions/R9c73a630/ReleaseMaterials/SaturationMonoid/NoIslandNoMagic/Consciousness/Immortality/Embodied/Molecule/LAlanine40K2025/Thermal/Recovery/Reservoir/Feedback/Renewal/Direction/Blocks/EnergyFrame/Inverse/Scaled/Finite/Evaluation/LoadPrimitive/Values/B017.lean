import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B011
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B012

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v273_pa : Scalar.QComplex := ((999988645018428507624804356735 : Int)/10^30,(4765483627857540070413148139 : Int)/10^30)
theorem v273_pa_checked : Scalar.distance (sourceCoefficient 2 83 1 0) v273_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v273_pb : Scalar.QComplex := ((2056182255922457834890459 : Int)/10^30,(-431469094971004958124991064 : Int)/10^30)
theorem v273_pb_checked : Scalar.distance (sourceCoefficient 2 83 1 1) v273_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v273_pg : Scalar.QComplex := ((-93084992488682272062360 : Int)/10^30,(-443600044774390987734 : Int)/10^30)
theorem v273_pg_checked : Scalar.distance (sourceCoefficient 2 83 1 2) v273_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v273_mb : Scalar.QComplex := ((1683843093998518246118745 : Int)/10^30,(-431470708708021638643990822 : Int)/10^30)
theorem v273_mb_checked : Scalar.distance (sourceCoefficient 2 83 3 1) v273_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v273_mg : Scalar.QComplex := ((-93085340635745010146042 : Int)/10^30,(-363271723476520761603 : Int)/10^30)
theorem v273_mg_checked : Scalar.distance (sourceCoefficient 2 83 3 2) v273_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v273_upper : Scalar.QComplex := ((999995380445229055023903028755 : Int)/10^30,(3039586847188885707534488361 : Int)/10^30)
theorem v273_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 83 5) 1) 14) v273_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material273 : Material (2 : Basis) (83 : Basis) where
  plus := ![v273_pa,v273_pb,v273_pg]
  minus := ![(Primitive.Addresses.material273 1).one,v273_mb,v273_mg]
  upper := v273_upper
  lower := (Primitive.Addresses.material273 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v273_pa_checked.trans (by decide +kernel)
    · exact v273_pb_checked.trans (by decide +kernel)
    · exact v273_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 83 Primitive.Addresses.material273
    · exact v273_mb_checked.trans (by decide +kernel)
    · exact v273_mg_checked.trans (by decide +kernel)
  upper_error := v273_upper_checked
  lower_error := reuse_lower_error 2 83 Primitive.Addresses.material273

def v274_pa : Scalar.QComplex := ((999988811855660534136723208803 : Int)/10^30,(4730344966739525840640076418 : Int)/10^30)
theorem v274_pa_checked : Scalar.distance (sourceCoefficient 2 84 1 0) v274_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v274_pb : Scalar.QComplex := ((2041020669618100625491844 : Int)/10^30,(-431469131476692926827847991 : Int)/10^30)
theorem v274_pb_checked : Scalar.distance (sourceCoefficient 2 84 1 1) v274_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v274_pg : Scalar.QComplex := ((-93085004191663291506380 : Int)/10^30,(-440329107522573946861 : Int)/10^30)
theorem v274_pg_checked : Scalar.distance (sourceCoefficient 2 84 1 2) v274_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v274_mb : Scalar.QComplex := ((1668681481836747974718945 : Int)/10^30,(-431470732129929886449024910 : Int)/10^30)
theorem v274_mb_checked : Scalar.distance (sourceCoefficient 2 84 3 1) v274_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v274_mg : Scalar.QComplex := ((-93085349516050141262407 : Int)/10^30,(-360000777343477611718 : Int)/10^30)
theorem v274_mg_checked : Scalar.distance (sourceCoefficient 2 84 3 2) v274_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v274_upper : Scalar.QComplex := ((999995486636071261819490916620 : Int)/10^30,(3004447950459852413654153671 : Int)/10^30)
theorem v274_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 84 5) 1) 14) v274_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material274 : Material (2 : Basis) (84 : Basis) where
  plus := ![v274_pa,v274_pb,v274_pg]
  minus := ![(Primitive.Addresses.material274 1).one,v274_mb,v274_mg]
  upper := v274_upper
  lower := (Primitive.Addresses.material274 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v274_pa_checked.trans (by decide +kernel)
    · exact v274_pb_checked.trans (by decide +kernel)
    · exact v274_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 84 Primitive.Addresses.material274
    · exact v274_mb_checked.trans (by decide +kernel)
    · exact v274_mg_checked.trans (by decide +kernel)
  upper_error := v274_upper_checked
  lower_error := reuse_lower_error 2 84 Primitive.Addresses.material274

def v275_pa : Scalar.QComplex := ((999989182696723407543898598586 : Int)/10^30,(4651289019092958324066182599 : Int)/10^30)
theorem v275_pa_checked : Scalar.distance (sourceCoefficient 2 85 1 0) v275_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v275_pb : Scalar.QComplex := ((2006909712604557588325744 : Int)/10^30,(-431469211011296855960603223 : Int)/10^30)
theorem v275_pb_checked : Scalar.distance (sourceCoefficient 2 85 1 1) v275_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v275_pg : Scalar.QComplex := ((-93085030031133011967893 : Int)/10^30,(-432970061594213184602 : Int)/10^30)
theorem v275_pg_checked : Scalar.distance (sourceCoefficient 2 85 1 2) v275_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v275_mb : Scalar.QComplex := ((1634570468889492096189407 : Int)/10^30,(-431470782228284598999920951 : Int)/10^30)
theorem v275_mb_checked : Scalar.distance (sourceCoefficient 2 85 3 1) v275_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v275_mg : Scalar.QComplex := ((-93085369004985043458097 : Int)/10^30,(-352641711856927371358 : Int)/10^30)
theorem v275_mg_checked : Scalar.distance (sourceCoefficient 2 85 3 2) v275_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v275_upper : Scalar.QComplex := ((999995721033188072596725914810 : Int)/10^30,(2925391480519800271609255817 : Int)/10^30)
theorem v275_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 85 5) 1) 14) v275_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material275 : Material (2 : Basis) (85 : Basis) where
  plus := ![v275_pa,v275_pb,v275_pg]
  minus := ![(Primitive.Addresses.material275 1).one,v275_mb,v275_mg]
  upper := v275_upper
  lower := (Primitive.Addresses.material275 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v275_pa_checked.trans (by decide +kernel)
    · exact v275_pb_checked.trans (by decide +kernel)
    · exact v275_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 85 Primitive.Addresses.material275
    · exact v275_mb_checked.trans (by decide +kernel)
    · exact v275_mg_checked.trans (by decide +kernel)
  upper_error := v275_upper_checked
  lower_error := reuse_lower_error 2 85 Primitive.Addresses.material275

def v276_pa : Scalar.QComplex := ((999989250427763586362996812598 : Int)/10^30,(4636704532264699755018091818 : Int)/10^30)
theorem v276_pa_checked : Scalar.distance (sourceCoefficient 2 86 1 0) v276_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v276_pb : Scalar.QComplex := ((2000616818215600991689378 : Int)/10^30,(-431469225291232424133320859 : Int)/10^30)
theorem v276_pb_checked : Scalar.distance (sourceCoefficient 2 86 1 1) v276_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v276_pg : Scalar.QComplex := ((-93085034723918532728459 : Int)/10^30,(-431612442039533854251 : Int)/10^30)
theorem v276_pg_checked : Scalar.distance (sourceCoefficient 2 86 1 2) v276_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v276_mb : Scalar.QComplex := ((1628277564520726429133152 : Int)/10^30,(-431470791077730413872638486 : Int)/10^30)
theorem v276_mb_checked : Scalar.distance (sourceCoefficient 2 86 3 1) v276_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v276_mg : Scalar.QComplex := ((-93085372526204286106818 : Int)/10^30,(-351284088758089298291 : Int)/10^30)
theorem v276_mg_checked : Scalar.distance (sourceCoefficient 2 86 3 2) v276_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v276_upper : Scalar.QComplex := ((999995763592626202723048539337 : Int)/10^30,(2910806898515790782407690394 : Int)/10^30)
theorem v276_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 86 5) 1) 14) v276_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material276 : Material (2 : Basis) (86 : Basis) where
  plus := ![v276_pa,v276_pb,v276_pg]
  minus := ![(Primitive.Addresses.material276 1).one,v276_mb,v276_mg]
  upper := v276_upper
  lower := (Primitive.Addresses.material276 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v276_pa_checked.trans (by decide +kernel)
    · exact v276_pb_checked.trans (by decide +kernel)
    · exact v276_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 86 Primitive.Addresses.material276
    · exact v276_mb_checked.trans (by decide +kernel)
    · exact v276_mg_checked.trans (by decide +kernel)
  upper_error := v276_upper_checked
  lower_error := reuse_lower_error 2 86 Primitive.Addresses.material276

def v277_pa : Scalar.QComplex := ((999989254905224512963563322468 : Int)/10^30,(4635738786203590513361988942 : Int)/10^30)
theorem v277_pa_checked : Scalar.distance (sourceCoefficient 2 87 1 0) v277_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v277_pb : Scalar.QComplex := ((2000200119439068027878110 : Int)/10^30,(-431469226232491968828849488 : Int)/10^30)
theorem v277_pb_checked : Scalar.distance (sourceCoefficient 2 87 1 1) v277_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v277_pg : Scalar.QComplex := ((-93085035033846867325840 : Int)/10^30,(-431522544072157790333 : Int)/10^30)
theorem v277_pg_checked : Scalar.distance (sourceCoefficient 2 87 1 2) v277_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v277_mb : Scalar.QComplex := ((1627860865087084869583950 : Int)/10^30,(-431470791659397331362488977 : Int)/10^30)
theorem v277_mb_checked : Scalar.distance (sourceCoefficient 2 87 3 1) v277_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v277_mg : Scalar.QComplex := ((-93085372758554608312323 : Int)/10^30,(-351194190556732162064 : Int)/10^30)
theorem v277_mg_checked : Scalar.distance (sourceCoefficient 2 87 3 2) v277_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v277_upper : Scalar.QComplex := ((999995766403290370995251306557 : Int)/10^30,(2909841146165355487042108485 : Int)/10^30)
theorem v277_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 87 5) 1) 14) v277_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material277 : Material (2 : Basis) (87 : Basis) where
  plus := ![v277_pa,v277_pb,v277_pg]
  minus := ![(Primitive.Addresses.material277 1).one,v277_mb,v277_mg]
  upper := v277_upper
  lower := (Primitive.Addresses.material277 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v277_pa_checked.trans (by decide +kernel)
    · exact v277_pb_checked.trans (by decide +kernel)
    · exact v277_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 87 Primitive.Addresses.material277
    · exact v277_mb_checked.trans (by decide +kernel)
    · exact v277_mg_checked.trans (by decide +kernel)
  upper_error := v277_upper_checked
  lower_error := reuse_lower_error 2 87 Primitive.Addresses.material277

def v278_pa : Scalar.QComplex := ((999989309350485189329026185940 : Int)/10^30,(4623979318685832252410071573 : Int)/10^30)
theorem v278_pa_checked : Scalar.distance (sourceCoefficient 2 88 1 0) v278_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v278_pb : Scalar.QComplex := ((1995126160740742510936836 : Int)/10^30,(-431469237650752114098770746 : Int)/10^30)
theorem v278_pb_checked : Scalar.distance (sourceCoefficient 2 88 1 1) v278_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v278_pg : Scalar.QComplex := ((-93085038799582840534346 : Int)/10^30,(-430427895842115168971 : Int)/10^30)
theorem v278_pg_checked : Scalar.distance (sourceCoefficient 2 88 1 2) v278_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v278_mb : Scalar.QComplex := ((1622786898424581821376242 : Int)/10^30,(-431470798699055391054011061 : Int)/10^30)
theorem v278_mb_checked : Scalar.distance (sourceCoefficient 2 88 3 1) v278_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v278_mg : Scalar.QComplex := ((-93085375579657057964578 : Int)/10^30,(-350099539484616562215 : Int)/10^30)
theorem v278_mg_checked : Scalar.distance (sourceCoefficient 2 88 3 2) v278_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v278_upper : Scalar.QComplex := ((999995800552695832449512169333 : Int)/10^30,(2898081602194362037759530946 : Int)/10^30)
theorem v278_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 88 5) 1) 14) v278_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material278 : Material (2 : Basis) (88 : Basis) where
  plus := ![v278_pa,v278_pb,v278_pg]
  minus := ![(Primitive.Addresses.material278 1).one,v278_mb,v278_mg]
  upper := v278_upper
  lower := (Primitive.Addresses.material278 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v278_pa_checked.trans (by decide +kernel)
    · exact v278_pb_checked.trans (by decide +kernel)
    · exact v278_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 88 Primitive.Addresses.material278
    · exact v278_mb_checked.trans (by decide +kernel)
    · exact v278_mg_checked.trans (by decide +kernel)
  upper_error := v278_upper_checked
  lower_error := reuse_lower_error 2 88 Primitive.Addresses.material278

def v279_pa : Scalar.QComplex := ((999989383618494516671928679083 : Int)/10^30,(4607890005567666127358455706 : Int)/10^30)
theorem v279_pa_checked : Scalar.distance (sourceCoefficient 2 89 1 0) v279_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v279_pb : Scalar.QComplex := ((1988183966593016183925589 : Int)/10^30,(-431469253144334392013964715 : Int)/10^30)
theorem v279_pb_checked : Scalar.distance (sourceCoefficient 2 89 1 1) v279_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v279_pg : Scalar.QComplex := ((-93085043927534930505432 : Int)/10^30,(-428930197268128797644 : Int)/10^30)
theorem v279_pg_checked : Scalar.distance (sourceCoefficient 2 89 1 2) v279_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v279_mb : Scalar.QComplex := ((1615844693491487948710952 : Int)/10^30,(-431470808201831015330361043 : Int)/10^30)
theorem v279_mb_checked : Scalar.distance (sourceCoefficient 2 89 3 1) v279_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v279_mg : Scalar.QComplex := ((-93085379415160823054271 : Int)/10^30,(-348601837043100118933 : Int)/10^30)
theorem v279_mg_checked : Scalar.distance (sourceCoefficient 2 89 3 2) v279_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v279_upper : Scalar.QComplex := ((999995847051899715446146915082 : Int)/10^30,(2881992184859491260914943499 : Int)/10^30)
theorem v279_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 89 5) 1) 14) v279_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material279 : Material (2 : Basis) (89 : Basis) where
  plus := ![v279_pa,v279_pb,v279_pg]
  minus := ![(Primitive.Addresses.material279 1).one,v279_mb,v279_mg]
  upper := v279_upper
  lower := (Primitive.Addresses.material279 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v279_pa_checked.trans (by decide +kernel)
    · exact v279_pb_checked.trans (by decide +kernel)
    · exact v279_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 89 Primitive.Addresses.material279
    · exact v279_mb_checked.trans (by decide +kernel)
    · exact v279_mg_checked.trans (by decide +kernel)
  upper_error := v279_upper_checked
  lower_error := reuse_lower_error 2 89 Primitive.Addresses.material279

def v280_pa : Scalar.QComplex := ((999989504015474161613178521451 : Int)/10^30,(4581687340487738585393451965 : Int)/10^30)
theorem v280_pa_checked : Scalar.distance (sourceCoefficient 2 90 1 0) v280_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v280_pb : Scalar.QComplex := ((1976878078369598655483703 : Int)/10^30,(-431469278058034052522164587 : Int)/10^30)
theorem v280_pb_checked : Scalar.distance (sourceCoefficient 2 90 1 1) v280_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v280_pg : Scalar.QComplex := ((-93085052218617925252424 : Int)/10^30,(-426491081782476629065 : Int)/10^30)
theorem v280_pg_checked : Scalar.distance (sourceCoefficient 2 90 1 2) v280_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v280_mb : Scalar.QComplex := ((1604538787978368574825834 : Int)/10^30,(-431470823359049060823491138 : Int)/10^30)
theorem v280_mb_checked : Scalar.distance (sourceCoefficient 2 90 3 1) v280_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v280_mg : Scalar.QComplex := ((-93085385601393920217835 : Int)/10^30,(-346162715310810910797 : Int)/10^30)
theorem v280_mg_checked : Scalar.distance (sourceCoefficient 2 90 3 2) v280_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v280_upper : Scalar.QComplex := ((999995922225277202481365682636 : Int)/10^30,(2855789351011090835749577212 : Int)/10^30)
theorem v280_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 90 5) 1) 14) v280_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material280 : Material (2 : Basis) (90 : Basis) where
  plus := ![v280_pa,v280_pb,v280_pg]
  minus := ![(Primitive.Addresses.material280 1).one,v280_mb,v280_mg]
  upper := v280_upper
  lower := (Primitive.Addresses.material280 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v280_pa_checked.trans (by decide +kernel)
    · exact v280_pb_checked.trans (by decide +kernel)
    · exact v280_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 90 Primitive.Addresses.material280
    · exact v280_mb_checked.trans (by decide +kernel)
    · exact v280_mg_checked.trans (by decide +kernel)
  upper_error := v280_upper_checked
  lower_error := reuse_lower_error 2 90 Primitive.Addresses.material280

def v281_pa : Scalar.QComplex := ((999989571537142771466680142634 : Int)/10^30,(4566926423933223608750363835 : Int)/10^30)
theorem v281_pa_checked : Scalar.distance (sourceCoefficient 2 91 1 0) v281_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v281_pb : Scalar.QComplex := ((1970509059760692953905931 : Int)/10^30,(-431469291918893714467372672 : Int)/10^30)
theorem v281_pb_checked : Scalar.distance (sourceCoefficient 2 91 1 1) v281_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v281_pg : Scalar.QComplex := ((-93085056856453045222731 : Int)/10^30,(-425117039148314636134 : Int)/10^30)
theorem v281_pg_checked : Scalar.distance (sourceCoefficient 2 91 1 2) v281_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v281_mb : Scalar.QComplex := ((1598169759779641961560123 : Int)/10^30,(-431470831723727352201328483 : Int)/10^30)
theorem v281_mb_checked : Scalar.distance (sourceCoefficient 2 91 3 1) v281_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v281_mg : Scalar.QComplex := ((-93085389053490404611347 : Int)/10^30,(-344788669186024959221 : Int)/10^30)
theorem v281_mg_checked : Scalar.distance (sourceCoefficient 2 91 3 2) v281_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v281_upper : Scalar.QComplex := ((999995964270842373537626921230 : Int)/10^30,(2841028339904952625314699713 : Int)/10^30)
theorem v281_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 91 5) 1) 14) v281_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material281 : Material (2 : Basis) (91 : Basis) where
  plus := ![v281_pa,v281_pb,v281_pg]
  minus := ![(Primitive.Addresses.material281 1).one,v281_mb,v281_mg]
  upper := v281_upper
  lower := (Primitive.Addresses.material281 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v281_pa_checked.trans (by decide +kernel)
    · exact v281_pb_checked.trans (by decide +kernel)
    · exact v281_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 91 Primitive.Addresses.material281
    · exact v281_mb_checked.trans (by decide +kernel)
    · exact v281_mg_checked.trans (by decide +kernel)
  upper_error := v281_upper_checked
  lower_error := reuse_lower_error 2 91 Primitive.Addresses.material281

def v282_pa : Scalar.QComplex := ((999989716967730440481476790099 : Int)/10^30,(4534970650221055206166385667 : Int)/10^30)
theorem v282_pa_checked : Scalar.distance (sourceCoefficient 2 92 1 0) v282_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v282_pb : Scalar.QComplex := ((1956720830481797782804830 : Int)/10^30,(-431469321496706242048101904 : Int)/10^30)
theorem v282_pb_checked : Scalar.distance (sourceCoefficient 2 92 1 1) v282_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v282_pg : Scalar.QComplex := ((-93085066815794422263988 : Int)/10^30,(-422142386887280310819 : Int)/10^30)
theorem v282_pg_checked : Scalar.distance (sourceCoefficient 2 92 1 2) v282_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v282_mb : Scalar.QComplex := ((1584381510110414628122828 : Int)/10^30,(-431470849402907997718310830 : Int)/10^30)
theorem v282_mb_checked : Scalar.distance (sourceCoefficient 2 92 3 1) v282_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v282_mg : Scalar.QComplex := ((-93085396445837145426534 : Int)/10^30,(-341814009438126562711 : Int)/10^30)
theorem v282_mg_checked : Scalar.distance (sourceCoefficient 2 92 3 2) v282_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v282_upper : Scalar.QComplex := ((999996054548447018718287073637 : Int)/10^30,(2809072362787154421268962472 : Int)/10^30)
theorem v282_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 92 5) 1) 14) v282_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material282 : Material (2 : Basis) (92 : Basis) where
  plus := ![v282_pa,v282_pb,v282_pg]
  minus := ![(Primitive.Addresses.material282 1).one,v282_mb,v282_mg]
  upper := v282_upper
  lower := (Primitive.Addresses.material282 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v282_pa_checked.trans (by decide +kernel)
    · exact v282_pb_checked.trans (by decide +kernel)
    · exact v282_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 92 Primitive.Addresses.material282
    · exact v282_mb_checked.trans (by decide +kernel)
    · exact v282_mg_checked.trans (by decide +kernel)
  upper_error := v282_upper_checked
  lower_error := reuse_lower_error 2 92 Primitive.Addresses.material282

def v283_pa : Scalar.QComplex := ((999989888240097734392337460014 : Int)/10^30,(4497045425258999344379700537 : Int)/10^30)
theorem v283_pa_checked : Scalar.distance (sourceCoefficient 2 93 1 0) v283_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v283_pb : Scalar.QComplex := ((1940356913231217889518977 : Int)/10^30,(-431469355837391016334060580 : Int)/10^30)
theorem v283_pb_checked : Scalar.distance (sourceCoefficient 2 93 1 1) v283_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v283_pg : Scalar.QComplex := ((-93085078491662142544672 : Int)/10^30,(-418612059295439901539 : Int)/10^30)
theorem v283_pg_checked : Scalar.distance (sourceCoefficient 2 93 1 2) v283_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v283_mb : Scalar.QComplex := ((1568017569318404682010863 : Int)/10^30,(-431470869622256401621544452 : Int)/10^30)
theorem v283_mb_checked : Scalar.distance (sourceCoefficient 2 93 3 1) v283_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v283_mg : Scalar.QComplex := ((-93085405075186806542156 : Int)/10^30,(-338283673085040478774 : Int)/10^30)
theorem v283_mg_checked : Scalar.distance (sourceCoefficient 2 93 3 2) v283_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v283_upper : Scalar.QComplex := ((999996160365061487581171246349 : Int)/10^30,(2771146898709697889089911188 : Int)/10^30)
theorem v283_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 93 5) 1) 14) v283_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material283 : Material (2 : Basis) (93 : Basis) where
  plus := ![v283_pa,v283_pb,v283_pg]
  minus := ![(Primitive.Addresses.material283 1).one,v283_mb,v283_mg]
  upper := v283_upper
  lower := (Primitive.Addresses.material283 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v283_pa_checked.trans (by decide +kernel)
    · exact v283_pb_checked.trans (by decide +kernel)
    · exact v283_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 93 Primitive.Addresses.material283
    · exact v283_mb_checked.trans (by decide +kernel)
    · exact v283_mg_checked.trans (by decide +kernel)
  upper_error := v283_upper_checked
  lower_error := reuse_lower_error 2 93 Primitive.Addresses.material283

def v284_pa : Scalar.QComplex := ((999990088697800486288490936983 : Int)/10^30,(4452247316256828620964735884 : Int)/10^30)
theorem v284_pa_checked : Scalar.distance (sourceCoefficient 2 94 1 0) v284_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v284_pb : Scalar.QComplex := ((1921027497312802977875038 : Int)/10^30,(-431469395335344359692774214 : Int)/10^30)
theorem v284_pb_checked : Scalar.distance (sourceCoefficient 2 94 1 1) v284_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v284_pg : Scalar.QComplex := ((-93085092082219094171906 : Int)/10^30,(-414441959066080191595 : Int)/10^30)
theorem v284_pg_checked : Scalar.distance (sourceCoefficient 2 94 1 2) v284_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v284_mb : Scalar.QComplex := ((1548688126512259901204345 : Int)/10^30,(-431470892439779665071103236 : Int)/10^30)
theorem v284_mb_checked : Scalar.distance (sourceCoefficient 2 94 3 1) v284_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v284_mg : Scalar.QComplex := ((-93085415067130014188822 : Int)/10^30,(-334113562680361113924 : Int)/10^30)
theorem v284_mg_checked : Scalar.distance (sourceCoefficient 2 94 3 2) v284_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v284_upper : Scalar.QComplex := ((999996283504993596231862464842 : Int)/10^30,(2726348510457238599829021592 : Int)/10^30)
theorem v284_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 94 5) 1) 14) v284_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material284 : Material (2 : Basis) (94 : Basis) where
  plus := ![v284_pa,v284_pb,v284_pg]
  minus := ![(Primitive.Addresses.material284 1).one,v284_mb,v284_mg]
  upper := v284_upper
  lower := (Primitive.Addresses.material284 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v284_pa_checked.trans (by decide +kernel)
    · exact v284_pb_checked.trans (by decide +kernel)
    · exact v284_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 94 Primitive.Addresses.material284
    · exact v284_mb_checked.trans (by decide +kernel)
    · exact v284_mg_checked.trans (by decide +kernel)
  upper_error := v284_upper_checked
  lower_error := reuse_lower_error 2 94 Primitive.Addresses.material284

def v285_pa : Scalar.QComplex := ((999990284837500227048082336577 : Int)/10^30,(4407973527048853187190714539 : Int)/10^30)
theorem v285_pa_checked : Scalar.distance (sourceCoefficient 2 95 1 0) v285_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v285_pb : Scalar.QComplex := ((1901924316941582254638673 : Int)/10^30,(-431469433236617131004686887 : Int)/10^30)
theorem v285_pb_checked : Scalar.distance (sourceCoefficient 2 95 1 1) v285_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v285_pg : Scalar.QComplex := ((-93085105299569292932403 : Int)/10^30,(-410320666255006034310 : Int)/10^30)
theorem v285_pg_checked : Scalar.distance (sourceCoefficient 2 95 1 2) v285_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v285_mb : Scalar.QComplex := ((1529584920546934896962635 : Int)/10^30,(-431470913855854038948792421 : Int)/10^30)
theorem v285_mb_checked : Scalar.distance (sourceCoefficient 2 95 3 1) v285_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v285_mg : Scalar.QComplex := ((-93085424727985211706596 : Int)/10^30,(-329992259997854688413 : Int)/10^30)
theorem v285_mg_checked : Scalar.distance (sourceCoefficient 2 95 3 2) v285_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v285_upper : Scalar.QComplex := ((999996403231857523765153530393 : Int)/10^30,(2682074448670543328733277161 : Int)/10^30)
theorem v285_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 95 5) 1) 14) v285_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material285 : Material (2 : Basis) (95 : Basis) where
  plus := ![v285_pa,v285_pb,v285_pg]
  minus := ![(Primitive.Addresses.material285 1).one,v285_mb,v285_mg]
  upper := v285_upper
  lower := (Primitive.Addresses.material285 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v285_pa_checked.trans (by decide +kernel)
    · exact v285_pb_checked.trans (by decide +kernel)
    · exact v285_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 95 Primitive.Addresses.material285
    · exact v285_mb_checked.trans (by decide +kernel)
    · exact v285_mg_checked.trans (by decide +kernel)
  upper_error := v285_upper_checked
  lower_error := reuse_lower_error 2 95 Primitive.Addresses.material285

def v286_pa : Scalar.QComplex := ((999990378342996618306584597301 : Int)/10^30,(4386709635989131217119954427 : Int)/10^30)
theorem v286_pa_checked : Scalar.distance (sourceCoefficient 2 96 1 0) v286_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v286_pb : Scalar.QComplex := ((1892749409893464725095350 : Int)/10^30,(-431469451039029045243997314 : Int)/10^30)
theorem v286_pb_checked : Scalar.distance (sourceCoefficient 2 96 1 1) v286_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v286_pg : Scalar.QComplex := ((-93085111571946558489320 : Int)/10^30,(-408341284819564207574 : Int)/10^30)
theorem v286_pg_checked : Scalar.distance (sourceCoefficient 2 96 1 2) v286_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v286_mb : Scalar.QComplex := ((1520410001552374884280314 : Int)/10^30,(-431470923740727764485016704 : Int)/10^30)
theorem v286_mb_checked : Scalar.distance (sourceCoefficient 2 96 3 1) v286_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v286_mg : Scalar.QComplex := ((-93085429292243111015020 : Int)/10^30,(-328012873886647949502 : Int)/10^30)
theorem v286_mg_checked : Scalar.distance (sourceCoefficient 2 96 3 2) v286_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v286_upper : Scalar.QComplex := ((999996460037667725618652246590 : Int)/10^30,(2660810427898885241068196033 : Int)/10^30)
theorem v286_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 96 5) 1) 14) v286_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material286 : Material (2 : Basis) (96 : Basis) where
  plus := ![v286_pa,v286_pb,v286_pg]
  minus := ![(Primitive.Addresses.material286 1).one,v286_mb,v286_mg]
  upper := v286_upper
  lower := (Primitive.Addresses.material286 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v286_pa_checked.trans (by decide +kernel)
    · exact v286_pb_checked.trans (by decide +kernel)
    · exact v286_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 96 Primitive.Addresses.material286
    · exact v286_mb_checked.trans (by decide +kernel)
    · exact v286_mg_checked.trans (by decide +kernel)
  upper_error := v286_upper_checked
  lower_error := reuse_lower_error 2 96 Primitive.Addresses.material286

def v287_pa : Scalar.QComplex := ((999990696608096576804581343252 : Int)/10^30,(4313548104953216139227944793 : Int)/10^30)
theorem v287_pa_checked : Scalar.distance (sourceCoefficient 2 97 1 0) v287_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v287_pb : Scalar.QComplex := ((1861181803818935919896701 : Int)/10^30,(-431469510303605917877576034 : Int)/10^30)
theorem v287_pb_checked : Scalar.distance (sourceCoefficient 2 97 1 1) v287_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v287_pg : Scalar.QComplex := ((-93085132777845624409203 : Int)/10^30,(-401530933692831989110 : Int)/10^30)
theorem v287_pg_checked : Scalar.distance (sourceCoefficient 2 97 1 2) v287_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v287_mb : Scalar.QComplex := ((1488842356089247867872748 : Int)/10^30,(-431470955763860280089416167 : Int)/10^30)
theorem v287_mb_checked : Scalar.distance (sourceCoefficient 2 97 3 1) v287_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v287_mg : Scalar.QComplex := ((-93085444621107985468132 : Int)/10^30,(-321202506995984888294 : Int)/10^30)
theorem v287_mg_checked : Scalar.distance (sourceCoefficient 2 97 3 2) v287_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v287_upper : Scalar.QComplex := ((999996652032128259895793224704 : Int)/10^30,(2587648456531786739988482926 : Int)/10^30)
theorem v287_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 2 97 5) 1) 14) v287_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material287 : Material (2 : Basis) (97 : Basis) where
  plus := ![v287_pa,v287_pb,v287_pg]
  minus := ![(Primitive.Addresses.material287 1).one,v287_mb,v287_mg]
  upper := v287_upper
  lower := (Primitive.Addresses.material287 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v287_pa_checked.trans (by decide +kernel)
    · exact v287_pb_checked.trans (by decide +kernel)
    · exact v287_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 2 97 Primitive.Addresses.material287
    · exact v287_mb_checked.trans (by decide +kernel)
    · exact v287_mg_checked.trans (by decide +kernel)
  upper_error := v287_upper_checked
  lower_error := reuse_lower_error 2 97 Primitive.Addresses.material287

def v288_pa : Scalar.QComplex := ((999966769023407052571486651060 : Int)/10^30,(8152352353038326324154922565 : Int)/10^30)
theorem v288_pa_checked : Scalar.distance (sourceCoefficient 3 4 1 0) v288_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v288_pb : Scalar.QComplex := ((3517556783596050354478605 : Int)/10^30,(-431463182579195606670762490 : Int)/10^30)
theorem v288_pb_checked : Scalar.distance (sourceCoefficient 3 4 1 1) v288_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v288_pg : Scalar.QComplex := ((-93083336543781209766545 : Int)/10^30,(-758873375804741553451 : Int)/10^30)
theorem v288_pg_checked : Scalar.distance (sourceCoefficient 3 4 1 2) v288_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v288_mb : Scalar.QComplex := ((3145222179663433225661399 : Int)/10^30,(-431466057418813257727976597 : Int)/10^30)
theorem v288_mb_checked : Scalar.distance (sourceCoefficient 3 4 3 1) v288_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v288_mg : Scalar.QComplex := ((-93083956758145827286145 : Int)/10^30,(-678546366122070108683 : Int)/10^30)
theorem v288_mg_checked : Scalar.distance (sourceCoefficient 3 4 3 2) v288_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v288_upper : Scalar.QComplex := ((999979349910954656247941350219 : Int)/10^30,(6426488284009387618084250749 : Int)/10^30)
theorem v288_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 4 5) 1) 14) v288_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material288 : Material (3 : Basis) (4 : Basis) where
  plus := ![v288_pa,v288_pb,v288_pg]
  minus := ![(Primitive.Addresses.material288 1).one,v288_mb,v288_mg]
  upper := v288_upper
  lower := (Primitive.Addresses.material288 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v288_pa_checked.trans (by decide +kernel)
    · exact v288_pb_checked.trans (by decide +kernel)
    · exact v288_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 4 Primitive.Addresses.material288
    · exact v288_mb_checked.trans (by decide +kernel)
    · exact v288_mg_checked.trans (by decide +kernel)
  upper_error := v288_upper_checked
  lower_error := reuse_lower_error 3 4 Primitive.Addresses.material288

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
