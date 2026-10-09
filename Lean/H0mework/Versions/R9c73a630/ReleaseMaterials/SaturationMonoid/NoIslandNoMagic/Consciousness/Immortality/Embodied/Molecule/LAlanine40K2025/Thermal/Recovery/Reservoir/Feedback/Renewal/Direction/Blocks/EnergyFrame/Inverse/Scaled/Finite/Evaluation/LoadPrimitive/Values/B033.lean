import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B022

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v529_pa : Scalar.QComplex := ((999994372391933072451676843250 : Int)/10^30,(3354874731473969908277872678 : Int)/10^30)
theorem v529_pa_checked : Scalar.distance (sourceCoefficient 5 60 1 0) v529_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v529_pb : Scalar.QComplex := ((1447547606184856149652518 : Int)/10^30,(-431473475410001792561653461 : Int)/10^30)
theorem v529_pb_checked : Scalar.distance (sourceCoefficient 5 60 1 1) v529_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v529_pg : Scalar.QComplex := ((-93085731574563801443514 : Int)/10^30,(-312292726181337876360 : Int)/10^30)
theorem v529_pg_checked : Scalar.distance (sourceCoefficient 5 60 1 2) v529_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v529_mb : Scalar.QComplex := ((1075204890761846016456905 : Int)/10^30,(-431474563921096598943028126 : Int)/10^30)
theorem v529_mb_checked : Scalar.distance (sourceCoefficient 5 60 3 1) v529_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v529_mg : Scalar.QComplex := ((-93085966409049260367324 : Int)/10^30,(-231963815977354835910 : Int)/10^30)
theorem v529_mg_checked : Scalar.distance (sourceCoefficient 5 60 3 2) v529_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v529_upper : Scalar.QComplex := ((999998673227217651195694109539 : Int)/10^30,(1628970166814479334525118252 : Int)/10^30)
theorem v529_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 60 5) 1) 14) v529_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material529 : Material (5 : Basis) (60 : Basis) where
  plus := ![v529_pa,v529_pb,v529_pg]
  minus := ![(Primitive.Addresses.material529 1).one,v529_mb,v529_mg]
  upper := v529_upper
  lower := (Primitive.Addresses.material529 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v529_pa_checked.trans (by decide +kernel)
    · exact v529_pb_checked.trans (by decide +kernel)
    · exact v529_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 60 Primitive.Addresses.material529
    · exact v529_mb_checked.trans (by decide +kernel)
    · exact v529_mg_checked.trans (by decide +kernel)
  upper_error := v529_upper_checked
  lower_error := reuse_lower_error 5 60 Primitive.Addresses.material529

def v530_pa : Scalar.QComplex := ((999994392032104163633732847069 : Int)/10^30,(3349015428804234667487726768 : Int)/10^30)
theorem v530_pa_checked : Scalar.distance (sourceCoefficient 5 61 1 0) v530_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v530_pb : Scalar.QComplex := ((1445019444878068687409521 : Int)/10^30,(-431473479885207331235788219 : Int)/10^30)
theorem v530_pb_checked : Scalar.distance (sourceCoefficient 5 61 1 1) v530_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v530_pg : Scalar.QComplex := ((-93085732971417856790007 : Int)/10^30,(-311747304191702979533 : Int)/10^30)
theorem v530_pg_checked : Scalar.distance (sourceCoefficient 5 61 1 2) v530_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v530_mb : Scalar.QComplex := ((1072676726534507727310105 : Int)/10^30,(-431474566214611127694455385 : Int)/10^30)
theorem v530_mb_checked : Scalar.distance (sourceCoefficient 5 61 3 1) v530_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v530_mg : Scalar.QComplex := ((-93085967335228183440819 : Int)/10^30,(-231418392985383335047 : Int)/10^30)
theorem v530_mg_checked : Scalar.distance (sourceCoefficient 5 61 3 2) v530_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v530_upper : Scalar.QComplex := ((999998682754734634472924453267 : Int)/10^30,(1623110838974333577287805598 : Int)/10^30)
theorem v530_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 61 5) 1) 14) v530_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material530 : Material (5 : Basis) (61 : Basis) where
  plus := ![v530_pa,v530_pb,v530_pg]
  minus := ![(Primitive.Addresses.material530 1).one,v530_mb,v530_mg]
  upper := v530_upper
  lower := (Primitive.Addresses.material530 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v530_pa_checked.trans (by decide +kernel)
    · exact v530_pb_checked.trans (by decide +kernel)
    · exact v530_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 61 Primitive.Addresses.material530
    · exact v530_mb_checked.trans (by decide +kernel)
    · exact v530_mg_checked.trans (by decide +kernel)
  upper_error := v530_upper_checked
  lower_error := reuse_lower_error 5 61 Primitive.Addresses.material530

def v531_pa : Scalar.QComplex := ((999994420507250541198550157707 : Int)/10^30,(3340502113182726552179772768 : Int)/10^30)
theorem v531_pa_checked : Scalar.distance (sourceCoefficient 5 62 1 0) v531_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v531_pb : Scalar.QComplex := ((1441346134922459040030511 : Int)/10^30,(-431473486352292008618999908 : Int)/10^30)
theorem v531_pb_checked : Scalar.distance (sourceCoefficient 5 62 1 1) v531_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v531_pg : Scalar.QComplex := ((-93085734994342697197031 : Int)/10^30,(-310954829425985249928 : Int)/10^30)
theorem v531_pg_checked : Scalar.distance (sourceCoefficient 5 62 1 2) v531_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v531_mb : Scalar.QComplex := ((1069003412365836445062738 : Int)/10^30,(-431474569511792345134344493 : Int)/10^30)
theorem v531_mb_checked : Scalar.distance (sourceCoefficient 5 62 3 1) v531_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v531_mg : Scalar.QComplex := ((-93085968674282239544580 : Int)/10^30,(-230625916769047150487 : Int)/10^30)
theorem v531_mg_checked : Scalar.distance (sourceCoefficient 5 62 3 2) v531_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v531_upper : Scalar.QComplex := ((999998696536628160889266168919 : Int)/10^30,(1614597486886889633337300960 : Int)/10^30)
theorem v531_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 62 5) 1) 14) v531_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material531 : Material (5 : Basis) (62 : Basis) where
  plus := ![v531_pa,v531_pb,v531_pg]
  minus := ![(Primitive.Addresses.material531 1).one,v531_mb,v531_mg]
  upper := v531_upper
  lower := (Primitive.Addresses.material531 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v531_pa_checked.trans (by decide +kernel)
    · exact v531_pb_checked.trans (by decide +kernel)
    · exact v531_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 62 Primitive.Addresses.material531
    · exact v531_mb_checked.trans (by decide +kernel)
    · exact v531_mg_checked.trans (by decide +kernel)
  upper_error := v531_upper_checked
  lower_error := reuse_lower_error 5 62 Primitive.Addresses.material531

def v532_pa : Scalar.QComplex := ((999994503028182491627138890486 : Int)/10^30,(3315707076675740251135853504 : Int)/10^30)
theorem v532_pa_checked : Scalar.distance (sourceCoefficient 5 63 1 0) v532_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v532_pb : Scalar.QComplex := ((1430647617990802603087831 : Int)/10^30,(-431473504950110287597636770 : Int)/10^30)
theorem v532_pb_checked : Scalar.distance (sourceCoefficient 5 63 1 1) v532_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v532_pg : Scalar.QComplex := ((-93085740841266021887901 : Int)/10^30,(-308646746267455521326 : Int)/10^30)
theorem v532_pg_checked : Scalar.distance (sourceCoefficient 5 63 1 2) v532_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v532_mb : Scalar.QComplex := ((1058304883368647248036972 : Int)/10^30,(-431474578877265430591505872 : Int)/10^30)
theorem v532_mb_checked : Scalar.distance (sourceCoefficient 5 63 3 1) v532_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v532_mg : Scalar.QComplex := ((-93085972529431573554096 : Int)/10^30,(-228317829424290772860 : Int)/10^30)
theorem v532_mg_checked : Scalar.distance (sourceCoefficient 5 63 3 2) v532_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v532_upper : Scalar.QComplex := ((999998736263453583165606665604 : Int)/10^30,(1589802344885555273887794545 : Int)/10^30)
theorem v532_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 63 5) 1) 14) v532_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material532 : Material (5 : Basis) (63 : Basis) where
  plus := ![v532_pa,v532_pb,v532_pg]
  minus := ![(Primitive.Addresses.material532 1).one,v532_mb,v532_mg]
  upper := v532_upper
  lower := (Primitive.Addresses.material532 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v532_pa_checked.trans (by decide +kernel)
    · exact v532_pb_checked.trans (by decide +kernel)
    · exact v532_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 63 Primitive.Addresses.material532
    · exact v532_mb_checked.trans (by decide +kernel)
    · exact v532_mg_checked.trans (by decide +kernel)
  upper_error := v532_upper_checked
  lower_error := reuse_lower_error 5 63 Primitive.Addresses.material532

def v533_pa : Scalar.QComplex := ((999994619899897559595155894542 : Int)/10^30,(3280269997942806141677997854 : Int)/10^30)
theorem v533_pa_checked : Scalar.distance (sourceCoefficient 5 64 1 0) v533_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v533_pb : Scalar.QComplex := ((1415357293134564415328805 : Int)/10^30,(-431473530916135357794897374 : Int)/10^30)
theorem v533_pb_checked : Scalar.distance (sourceCoefficient 5 64 1 1) v533_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v533_pg : Scalar.QComplex := ((-93085749081788538520443 : Int)/10^30,(-305348032752005346984 : Int)/10^30)
theorem v533_pg_checked : Scalar.distance (sourceCoefficient 5 64 1 2) v533_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v533_mb : Scalar.QComplex := ((1043014541798185637399184 : Int)/10^30,(-431474591648419132184981379 : Int)/10^30)
theorem v533_mb_checked : Scalar.distance (sourceCoefficient 5 64 3 1) v533_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v533_mg : Scalar.QComplex := ((-93085977923309826571606 : Int)/10^30,(-225019110025902606478 : Int)/10^30)
theorem v533_mg_checked : Scalar.distance (sourceCoefficient 5 64 3 2) v533_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v533_upper : Scalar.QComplex := ((999998791973811518068277039212 : Int)/10^30,(1554365117222009517307206617 : Int)/10^30)
theorem v533_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 64 5) 1) 14) v533_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material533 : Material (5 : Basis) (64 : Basis) where
  plus := ![v533_pa,v533_pb,v533_pg]
  minus := ![(Primitive.Addresses.material533 1).one,v533_mb,v533_mg]
  upper := v533_upper
  lower := (Primitive.Addresses.material533 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v533_pa_checked.trans (by decide +kernel)
    · exact v533_pb_checked.trans (by decide +kernel)
    · exact v533_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 64 Primitive.Addresses.material533
    · exact v533_mb_checked.trans (by decide +kernel)
    · exact v533_mg_checked.trans (by decide +kernel)
  upper_error := v533_upper_checked
  lower_error := reuse_lower_error 5 64 Primitive.Addresses.material533

def v534_pa : Scalar.QComplex := ((999994737233323000706746009070 : Int)/10^30,(3244303570457840181951405878 : Int)/10^30)
theorem v534_pa_checked : Scalar.distance (sourceCoefficient 5 65 1 0) v534_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v534_pb : Scalar.QComplex := ((1399838567036394301062728 : Int)/10^30,(-431473556531297282965408681 : Int)/10^30)
theorem v534_pb_checked : Scalar.distance (sourceCoefficient 5 65 1 1) v534_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v534_pg : Scalar.QComplex := ((-93085757305953072583798 : Int)/10^30,(-302000044142244299817 : Int)/10^30)
theorem v534_pg_checked : Scalar.distance (sourceCoefficient 5 65 1 2) v534_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v534_mb : Scalar.QComplex := ((1027495799373615412946670 : Int)/10^30,(-431474603871609834416911420 : Int)/10^30)
theorem v534_mb_checked : Scalar.distance (sourceCoefficient 5 65 3 1) v534_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v534_mg : Scalar.QComplex := ((-93085983258307915988336 : Int)/10^30,(-221671115565667139087 : Int)/10^30)
theorem v534_mg_checked : Scalar.distance (sourceCoefficient 5 65 3 2) v534_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v534_upper : Scalar.QComplex := ((999998847232271214587838402084 : Int)/10^30,(1518398540797964476928934052 : Int)/10^30)
theorem v534_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 65 5) 1) 14) v534_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material534 : Material (5 : Basis) (65 : Basis) where
  plus := ![v534_pa,v534_pb,v534_pg]
  minus := ![(Primitive.Addresses.material534 1).one,v534_mb,v534_mg]
  upper := v534_upper
  lower := (Primitive.Addresses.material534 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v534_pa_checked.trans (by decide +kernel)
    · exact v534_pb_checked.trans (by decide +kernel)
    · exact v534_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 65 Primitive.Addresses.material534
    · exact v534_mb_checked.trans (by decide +kernel)
    · exact v534_mg_checked.trans (by decide +kernel)
  upper_error := v534_upper_checked
  lower_error := reuse_lower_error 5 65 Primitive.Addresses.material534

def v535_pa : Scalar.QComplex := ((999994794138067419873437364049 : Int)/10^30,(3226716095996329212593621409 : Int)/10^30)
theorem v535_pa_checked : Scalar.distance (sourceCoefficient 5 66 1 0) v535_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v535_pb : Scalar.QComplex := ((1392249957260134905950845 : Int)/10^30,(-431473568786098005955098486 : Int)/10^30)
theorem v535_pb_checked : Scalar.distance (sourceCoefficient 5 66 1 1) v535_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v535_pg : Scalar.QComplex := ((-93085761276399611356902 : Int)/10^30,(-300362887866354336140 : Int)/10^30)
theorem v535_pg_checked : Scalar.distance (sourceCoefficient 5 66 1 2) v535_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v535_mb : Scalar.QComplex := ((1019907181847601165931666 : Int)/10^30,(-431474609577777535769277978 : Int)/10^30)
theorem v535_mb_checked : Scalar.distance (sourceCoefficient 5 66 3 1) v535_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v535_mg : Scalar.QComplex := ((-93085985815960845071198 : Int)/10^30,(-220033956473048737975 : Int)/10^30)
theorem v535_mg_checked : Scalar.distance (sourceCoefficient 5 66 3 2) v535_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v535_upper : Scalar.QComplex := ((999998873782545483473889999586 : Int)/10^30,(1500810994318504238720890113 : Int)/10^30)
theorem v535_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 66 5) 1) 14) v535_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material535 : Material (5 : Basis) (66 : Basis) where
  plus := ![v535_pa,v535_pb,v535_pg]
  minus := ![(Primitive.Addresses.material535 1).one,v535_mb,v535_mg]
  upper := v535_upper
  lower := (Primitive.Addresses.material535 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v535_pa_checked.trans (by decide +kernel)
    · exact v535_pb_checked.trans (by decide +kernel)
    · exact v535_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 66 Primitive.Addresses.material535
    · exact v535_mb_checked.trans (by decide +kernel)
    · exact v535_mg_checked.trans (by decide +kernel)
  upper_error := v535_upper_checked
  lower_error := reuse_lower_error 5 66 Primitive.Addresses.material535

def v536_pa : Scalar.QComplex := ((999994888945917593324367412404 : Int)/10^30,(3197199093259523301785637661 : Int)/10^30)
theorem v536_pa_checked : Scalar.distance (sourceCoefficient 5 67 1 0) v536_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v536_pb : Scalar.QComplex := ((1379514018137806388901299 : Int)/10^30,(-431473588953340416198695234 : Int)/10^30)
theorem v536_pb_checked : Scalar.distance (sourceCoefficient 5 67 1 1) v536_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v536_pg : Scalar.QComplex := ((-93085767864488043105952 : Int)/10^30,(-297615253739365255235 : Int)/10^30)
theorem v536_pg_checked : Scalar.distance (sourceCoefficient 5 67 1 2) v536_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v536_mb : Scalar.QComplex := ((1007171230064022944137617 : Int)/10^30,(-431474618754470579662162820 : Int)/10^30)
theorem v536_mb_checked : Scalar.distance (sourceCoefficient 5 67 3 1) v536_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v536_mg : Scalar.QComplex := ((-93085990032962321029564 : Int)/10^30,(-217286317683905815519 : Int)/10^30)
theorem v536_mg_checked : Scalar.distance (sourceCoefficient 5 67 3 2) v536_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v536_upper : Scalar.QComplex := ((999998917646585489612654606618 : Int)/10^30,(1471293871914058095283431384 : Int)/10^30)
theorem v536_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 67 5) 1) 14) v536_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material536 : Material (5 : Basis) (67 : Basis) where
  plus := ![v536_pa,v536_pb,v536_pg]
  minus := ![(Primitive.Addresses.material536 1).one,v536_mb,v536_mg]
  upper := v536_upper
  lower := (Primitive.Addresses.material536 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v536_pa_checked.trans (by decide +kernel)
    · exact v536_pb_checked.trans (by decide +kernel)
    · exact v536_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 67 Primitive.Addresses.material536
    · exact v536_mb_checked.trans (by decide +kernel)
    · exact v536_mg_checked.trans (by decide +kernel)
  upper_error := v536_upper_checked
  lower_error := reuse_lower_error 5 67 Primitive.Addresses.material536

def v537_pa : Scalar.QComplex := ((999995044905528941780096444699 : Int)/10^30,(3148041357599233113253447621 : Int)/10^30)
theorem v537_pa_checked : Scalar.distance (sourceCoefficient 5 68 1 0) v537_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v537_pb : Scalar.QComplex := ((1358303535489064283143312 : Int)/10^30,(-431473621427449461869821027 : Int)/10^30)
theorem v537_pb_checked : Scalar.distance (sourceCoefficient 5 68 1 1) v537_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v537_pg : Scalar.QComplex := ((-93085778626308935825916 : Int)/10^30,(-293039332957525799589 : Int)/10^30)
theorem v537_pg_checked : Scalar.distance (sourceCoefficient 5 68 1 2) v537_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v537_mb : Scalar.QComplex := ((985960727289219368614792 : Int)/10^30,(-431474632924876292550578788 : Int)/10^30)
theorem v537_mb_checked : Scalar.distance (sourceCoefficient 5 68 3 1) v537_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v537_mg : Scalar.QComplex := ((-93085996845965663725846 : Int)/10^30,(-212710389318924060867 : Int)/10^30)
theorem v537_mg_checked : Scalar.distance (sourceCoefficient 5 68 3 2) v537_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v537_upper : Scalar.QComplex := ((999998988764172359829687649893 : Int)/10^30,(1422135940296300057472768576 : Int)/10^30)
theorem v537_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 68 5) 1) 14) v537_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material537 : Material (5 : Basis) (68 : Basis) where
  plus := ![v537_pa,v537_pb,v537_pg]
  minus := ![(Primitive.Addresses.material537 1).one,v537_mb,v537_mg]
  upper := v537_upper
  lower := (Primitive.Addresses.material537 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v537_pa_checked.trans (by decide +kernel)
    · exact v537_pb_checked.trans (by decide +kernel)
    · exact v537_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 68 Primitive.Addresses.material537
    · exact v537_mb_checked.trans (by decide +kernel)
    · exact v537_mg_checked.trans (by decide +kernel)
  upper_error := v537_upper_checked
  lower_error := reuse_lower_error 5 68 Primitive.Addresses.material537

def v538_pa : Scalar.QComplex := ((999995112780580576695451624919 : Int)/10^30,(3126406076301182521818620039 : Int)/10^30)
theorem v538_pa_checked : Scalar.distance (sourceCoefficient 5 69 1 0) v538_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v538_pb : Scalar.QComplex := ((1348968387805652945865088 : Int)/10^30,(-431473635279360158318433960 : Int)/10^30)
theorem v538_pb_checked : Scalar.distance (sourceCoefficient 5 69 1 1) v538_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v538_pg : Scalar.QComplex := ((-93085783279627795444579 : Int)/10^30,(-291025380767575790008 : Int)/10^30)
theorem v538_pg_checked : Scalar.distance (sourceCoefficient 5 69 1 2) v538_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v538_mb : Scalar.QComplex := ((976625571128135087059639 : Int)/10^30,(-431474638720969819960006811 : Int)/10^30)
theorem v538_mb_checked : Scalar.distance (sourceCoefficient 5 69 3 1) v538_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v538_mg : Scalar.QComplex := ((-93085999761332755813879 : Int)/10^30,(-210696433863255895617 : Int)/10^30)
theorem v538_mg_checked : Scalar.distance (sourceCoefficient 5 69 3 2) v538_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v538_upper : Scalar.QComplex := ((999999019298590119780771535468 : Int)/10^30,(1400500574075277955535361459 : Int)/10^30)
theorem v538_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 69 5) 1) 14) v538_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material538 : Material (5 : Basis) (69 : Basis) where
  plus := ![v538_pa,v538_pb,v538_pg]
  minus := ![(Primitive.Addresses.material538 1).one,v538_mb,v538_mg]
  upper := v538_upper
  lower := (Primitive.Addresses.material538 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v538_pa_checked.trans (by decide +kernel)
    · exact v538_pb_checked.trans (by decide +kernel)
    · exact v538_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 69 Primitive.Addresses.material538
    · exact v538_mb_checked.trans (by decide +kernel)
    · exact v538_mg_checked.trans (by decide +kernel)
  upper_error := v538_upper_checked
  lower_error := reuse_lower_error 5 69 Primitive.Addresses.material538

def v539_pa : Scalar.QComplex := ((999995157174212134093308198405 : Int)/10^30,(3112174179375280686277821689 : Int)/10^30)
theorem v539_pa_checked : Scalar.distance (sourceCoefficient 5 70 1 0) v539_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v539_pb : Scalar.QComplex := ((1342827637778830357524379 : Int)/10^30,(-431473644244445014342828485 : Int)/10^30)
theorem v539_pb_checked : Scalar.distance (sourceCoefficient 5 70 1 1) v539_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v539_pg : Scalar.QComplex := ((-93085786312907425957903 : Int)/10^30,(-289700583599332417904 : Int)/10^30)
theorem v539_pg_checked : Scalar.distance (sourceCoefficient 5 70 1 2) v539_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v539_mb : Scalar.QComplex := ((970484815651329921529531 : Int)/10^30,(-431474642386860633840171050 : Int)/10^30)
theorem v539_mb_checked : Scalar.distance (sourceCoefficient 5 70 3 1) v539_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v539_mg : Scalar.QComplex := ((-93086001651370967354066 : Int)/10^30,(-209371634570711348181 : Int)/10^30)
theorem v539_mg_checked : Scalar.distance (sourceCoefficient 5 70 3 2) v539_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v539_upper : Scalar.QComplex := ((999999039129192571576236202884 : Int)/10^30,(1386268621726734085801349652 : Int)/10^30)
theorem v539_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 70 5) 1) 14) v539_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material539 : Material (5 : Basis) (70 : Basis) where
  plus := ![v539_pa,v539_pb,v539_pg]
  minus := ![(Primitive.Addresses.material539 1).one,v539_mb,v539_mg]
  upper := v539_upper
  lower := (Primitive.Addresses.material539 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v539_pa_checked.trans (by decide +kernel)
    · exact v539_pb_checked.trans (by decide +kernel)
    · exact v539_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 70 Primitive.Addresses.material539
    · exact v539_mb_checked.trans (by decide +kernel)
    · exact v539_mg_checked.trans (by decide +kernel)
  upper_error := v539_upper_checked
  lower_error := reuse_lower_error 5 70 Primitive.Addresses.material539

def v540_pa : Scalar.QComplex := ((999995232482619367292686932227 : Int)/10^30,(3087881479597855289287722528 : Int)/10^30)
theorem v540_pa_checked : Scalar.distance (sourceCoefficient 5 71 1 0) v540_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v540_pb : Scalar.QComplex := ((1332345873400697547498126 : Int)/10^30,(-431473659277915014179291513 : Int)/10^30)
theorem v540_pb_checked : Scalar.distance (sourceCoefficient 5 71 1 1) v540_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v540_pg : Scalar.QComplex := ((-93085791439652428264751 : Int)/10^30,(-287439261771887685915 : Int)/10^30)
theorem v540_pg_checked : Scalar.distance (sourceCoefficient 5 71 1 2) v540_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v540_mb : Scalar.QComplex := ((960003042202829502274722 : Int)/10^30,(-431474648375034458843189890 : Int)/10^30)
theorem v540_mb_checked : Scalar.distance (sourceCoefficient 5 71 3 1) v540_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v540_mg : Scalar.QComplex := ((-93086004826695169809043 : Int)/10^30,(-207110309161110043096 : Int)/10^30)
theorem v540_mg_checked : Scalar.distance (sourceCoefficient 5 71 3 2) v540_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v540_upper : Scalar.QComplex := ((999999072510491642421691030537 : Int)/10^30,(1361975828154952427148578998 : Int)/10^30)
theorem v540_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 71 5) 1) 14) v540_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material540 : Material (5 : Basis) (71 : Basis) where
  plus := ![v540_pa,v540_pb,v540_pg]
  minus := ![(Primitive.Addresses.material540 1).one,v540_mb,v540_mg]
  upper := v540_upper
  lower := (Primitive.Addresses.material540 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v540_pa_checked.trans (by decide +kernel)
    · exact v540_pb_checked.trans (by decide +kernel)
    · exact v540_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 71 Primitive.Addresses.material540
    · exact v540_mb_checked.trans (by decide +kernel)
    · exact v540_mg_checked.trans (by decide +kernel)
  upper_error := v540_upper_checked
  lower_error := reuse_lower_error 5 71 Primitive.Addresses.material540

def v541_pa : Scalar.QComplex := ((999995313539792096394644854061 : Int)/10^30,(3061518978039811277365592043 : Int)/10^30)
theorem v541_pa_checked : Scalar.distance (sourceCoefficient 5 72 1 0) v541_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v541_pb : Scalar.QComplex := ((1320971035852509358786798 : Int)/10^30,(-431473675208142552508848754 : Int)/10^30)
theorem v541_pb_checked : Scalar.distance (sourceCoefficient 5 72 1 1) v541_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v541_pg : Scalar.QComplex := ((-93085796930695985149744 : Int)/10^30,(-284985269461410943354 : Int)/10^30)
theorem v541_pg_checked : Scalar.distance (sourceCoefficient 5 72 1 2) v541_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v541_mb : Scalar.QComplex := ((948628195142944293747354 : Int)/10^30,(-431474654489283565200144788 : Int)/10^30)
theorem v541_mb_checked : Scalar.distance (sourceCoefficient 5 72 3 1) v541_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v541_mg : Scalar.QComplex := ((-93086008200051841896969 : Int)/10^30,(-204656313025843508544 : Int)/10^30)
theorem v541_mg_checked : Scalar.distance (sourceCoefficient 5 72 3 2) v541_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v541_upper : Scalar.QComplex := ((999999108068257544661838507171 : Int)/10^30,(1335613225963431047802695494 : Int)/10^30)
theorem v541_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 72 5) 1) 14) v541_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material541 : Material (5 : Basis) (72 : Basis) where
  plus := ![v541_pa,v541_pb,v541_pg]
  minus := ![(Primitive.Addresses.material541 1).one,v541_mb,v541_mg]
  upper := v541_upper
  lower := (Primitive.Addresses.material541 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v541_pa_checked.trans (by decide +kernel)
    · exact v541_pb_checked.trans (by decide +kernel)
    · exact v541_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 72 Primitive.Addresses.material541
    · exact v541_mb_checked.trans (by decide +kernel)
    · exact v541_mg_checked.trans (by decide +kernel)
  upper_error := v541_upper_checked
  lower_error := reuse_lower_error 5 72 Primitive.Addresses.material541

def v542_pa : Scalar.QComplex := ((999995342425404680421868156829 : Int)/10^30,(3052069379558407957482168745 : Int)/10^30)
theorem v542_pa_checked : Scalar.distance (sourceCoefficient 5 73 1 0) v542_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v542_pb : Scalar.QComplex := ((1316893742849860819557937 : Int)/10^30,(-431473680820963097090295621 : Int)/10^30)
theorem v542_pb_checked : Scalar.distance (sourceCoefficient 5 73 1 1) v542_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v542_pg : Scalar.QComplex := ((-93085798880576143374243 : Int)/10^30,(-284105639678348528788 : Int)/10^30)
theorem v542_pg_checked : Scalar.distance (sourceCoefficient 5 73 1 2) v542_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v542_mb : Scalar.QComplex := ((944550898814846942979679 : Int)/10^30,(-431474656583581793046302688 : Int)/10^30)
theorem v542_mb_checked : Scalar.distance (sourceCoefficient 5 73 3 1) v542_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v542_mg : Scalar.QComplex := ((-93086009390850388363882 : Int)/10^30,(-203776681887648706074 : Int)/10^30)
theorem v542_mg_checked : Scalar.distance (sourceCoefficient 5 73 3 2) v542_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v542_upper : Scalar.QComplex := ((999999120644677388937808620867 : Int)/10^30,(1326163591702147800429241700 : Int)/10^30)
theorem v542_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 73 5) 1) 14) v542_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material542 : Material (5 : Basis) (73 : Basis) where
  plus := ![v542_pa,v542_pb,v542_pg]
  minus := ![(Primitive.Addresses.material542 1).one,v542_mb,v542_mg]
  upper := v542_upper
  lower := (Primitive.Addresses.material542 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v542_pa_checked.trans (by decide +kernel)
    · exact v542_pb_checked.trans (by decide +kernel)
    · exact v542_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 73 Primitive.Addresses.material542
    · exact v542_mb_checked.trans (by decide +kernel)
    · exact v542_mg_checked.trans (by decide +kernel)
  upper_error := v542_upper_checked
  lower_error := reuse_lower_error 5 73 Primitive.Addresses.material542

def v543_pa : Scalar.QComplex := ((999995374822047605899408425883 : Int)/10^30,(3041436258170982920305864212 : Int)/10^30)
theorem v543_pa_checked : Scalar.distance (sourceCoefficient 5 74 1 0) v543_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v543_pb : Scalar.QComplex := ((1312305785965446867079444 : Int)/10^30,(-431473687075339715842827978 : Int)/10^30)
theorem v543_pb_checked : Scalar.distance (sourceCoefficient 5 74 1 1) v543_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v543_pg : Scalar.QComplex := ((-93085801063075119083575 : Int)/10^30,(-283115839935268536404 : Int)/10^30)
theorem v543_pg_checked : Scalar.distance (sourceCoefficient 5 74 1 2) v543_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v543_mb : Scalar.QComplex := ((939962938241493683239292 : Int)/10^30,(-431474658878755925666802562 : Int)/10^30)
theorem v543_mb_checked : Scalar.distance (sourceCoefficient 5 74 3 1) v543_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v543_mg : Scalar.QComplex := ((-93086010719195952076648 : Int)/10^30,(-202786880629718074190 : Int)/10^30)
theorem v543_mg_checked : Scalar.distance (sourceCoefficient 5 74 3 2) v543_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v543_upper : Scalar.QComplex := ((999999134689469177962671353505 : Int)/10^30,(1315530430237841326756845446 : Int)/10^30)
theorem v543_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 74 5) 1) 14) v543_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material543 : Material (5 : Basis) (74 : Basis) where
  plus := ![v543_pa,v543_pb,v543_pg]
  minus := ![(Primitive.Addresses.material543 1).one,v543_mb,v543_mg]
  upper := v543_upper
  lower := (Primitive.Addresses.material543 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v543_pa_checked.trans (by decide +kernel)
    · exact v543_pb_checked.trans (by decide +kernel)
    · exact v543_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 74 Primitive.Addresses.material543
    · exact v543_mb_checked.trans (by decide +kernel)
    · exact v543_mg_checked.trans (by decide +kernel)
  upper_error := v543_upper_checked
  lower_error := reuse_lower_error 5 74 Primitive.Addresses.material543

def v544_pa : Scalar.QComplex := ((999995419771574420550839849069 : Int)/10^30,(3026621197419073755850423031 : Int)/10^30)
theorem v544_pa_checked : Scalar.distance (sourceCoefficient 5 75 1 0) v544_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v544_pb : Scalar.QComplex := ((1305913414858825007427319 : Int)/10^30,(-431473695681072580325781887 : Int)/10^30)
theorem v544_pb_checked : Scalar.distance (sourceCoefficient 5 75 1 1) v544_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v544_pg : Scalar.QComplex := ((-93085804083464737616911 : Int)/10^30,(-281736758236521955130 : Int)/10^30)
theorem v544_pg_checked : Scalar.distance (sourceCoefficient 5 75 1 2) v544_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v544_mb : Scalar.QComplex := ((933570562088683858145844 : Int)/10^30,(-431474661968157222534673233 : Int)/10^30)
theorem v544_mb_checked : Scalar.distance (sourceCoefficient 5 75 3 1) v544_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v544_mg : Scalar.QComplex := ((-93086012549499051496614 : Int)/10^30,(-201407796838006429010 : Int)/10^30)
theorem v544_mg_checked : Scalar.distance (sourceCoefficient 5 75 3 2) v544_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v544_upper : Scalar.QComplex := ((999999154069478199591405911994 : Int)/10^30,(1300715313972419360115141600 : Int)/10^30)
theorem v544_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 5 75 5) 1) 14) v544_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material544 : Material (5 : Basis) (75 : Basis) where
  plus := ![v544_pa,v544_pb,v544_pg]
  minus := ![(Primitive.Addresses.material544 1).one,v544_mb,v544_mg]
  upper := v544_upper
  lower := (Primitive.Addresses.material544 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v544_pa_checked.trans (by decide +kernel)
    · exact v544_pb_checked.trans (by decide +kernel)
    · exact v544_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 5 75 Primitive.Addresses.material544
    · exact v544_mb_checked.trans (by decide +kernel)
    · exact v544_mg_checked.trans (by decide +kernel)
  upper_error := v544_upper_checked
  lower_error := reuse_lower_error 5 75 Primitive.Addresses.material544

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
