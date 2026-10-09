import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B034
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B035

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v833_pa : Scalar.QComplex := ((999999134596580838683950056990 : Int)/10^30,(-1315601037320795898964704785 : Int)/10^30)
theorem v833_pa_checked : Scalar.distance (sourceCoefficient 8 94 1 0) v833_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v833_pb : Scalar.QComplex := ((-567652047415304487514706 : Int)/10^30,(-431476975210734587041378864 : Int)/10^30)
theorem v833_pb_checked : Scalar.distance (sourceCoefficient 8 94 1 1) v833_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v833_pg : Scalar.QComplex := ((-93086330744295174254326 : Int)/10^30,(122464579268847051648 : Int)/10^30)
theorem v833_pg_checked : Scalar.distance (sourceCoefficient 8 94 1 2) v833_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v833_mb : Scalar.QComplex := ((-939997032657791639361914 : Int)/10^30,(-431476324693986423905684494 : Int)/10^30)
theorem v833_mb_checked : Scalar.distance (sourceCoefficient 8 94 3 1) v833_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v833_mg : Scalar.QComplex := ((-93086190402583673560304 : Int)/10^30,(202793844649308454354 : Int)/10^30)
theorem v833_mg_checked : Scalar.distance (sourceCoefficient 8 94 3 2) v833_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v833_upper : Scalar.QComplex := ((999995374607297985211894631728 : Int)/10^30,(-3041506864988459689712720315 : Int)/10^30)
theorem v833_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 94 5) 1) 14) v833_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material833 : Material (8 : Basis) (94 : Basis) where
  plus := ![v833_pa,v833_pb,v833_pg]
  minus := ![(Primitive.Addresses.material833 1).one,v833_mb,v833_mg]
  upper := v833_upper
  lower := (Primitive.Addresses.material833 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v833_pa_checked.trans (by decide +kernel)
    · exact v833_pb_checked.trans (by decide +kernel)
    · exact v833_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 94 Primitive.Addresses.material833
    · exact v833_mb_checked.trans (by decide +kernel)
    · exact v833_mg_checked.trans (by decide +kernel)
  upper_error := v833_upper_checked
  lower_error := reuse_lower_error 8 94 Primitive.Addresses.material833

def v834_pa : Scalar.QComplex := ((999999075369263673020594148096 : Int)/10^30,(-1359875221375829118071137352 : Int)/10^30)
theorem v834_pa_checked : Scalar.distance (sourceCoefficient 8 95 1 0) v834_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v834_pb : Scalar.QComplex := ((-586755341364506028057459 : Int)/10^30,(-431476939655422326948453755 : Int)/10^30)
theorem v834_pb_checked : Scalar.distance (sourceCoefficient 8 95 1 1) v834_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v834_pg : Scalar.QComplex := ((-93086324152335665331427 : Int)/10^30,(126585902708936082048 : Int)/10^30)
theorem v834_pg_checked : Scalar.distance (sourceCoefficient 8 95 1 2) v834_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v834_mb : Scalar.QComplex := ((-959100288811330650312261 : Int)/10^30,(-431476272653405104940191899 : Int)/10^30)
theorem v834_mb_checked : Scalar.distance (sourceCoefficient 8 95 3 1) v834_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v834_mg : Scalar.QComplex := ((-93086180254110107845660 : Int)/10^30,(206915160866276248858 : Int)/10^30)
theorem v834_mg_checked : Scalar.distance (sourceCoefficient 8 95 3 2) v834_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v834_upper : Scalar.QComplex := ((999995238966843875294911275446 : Int)/10^30,(-3085780880881320202149597114 : Int)/10^30)
theorem v834_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 95 5) 1) 14) v834_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material834 : Material (8 : Basis) (95 : Basis) where
  plus := ![v834_pa,v834_pb,v834_pg]
  minus := ![(Primitive.Addresses.material834 1).one,v834_mb,v834_mg]
  upper := v834_upper
  lower := (Primitive.Addresses.material834 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v834_pa_checked.trans (by decide +kernel)
    · exact v834_pb_checked.trans (by decide +kernel)
    · exact v834_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 95 Primitive.Addresses.material834
    · exact v834_mb_checked.trans (by decide +kernel)
    · exact v834_mg_checked.trans (by decide +kernel)
  upper_error := v834_upper_checked
  lower_error := reuse_lower_error 8 95 Primitive.Addresses.material834

def v835_pa : Scalar.QComplex := ((999999046226664843295009258090 : Int)/10^30,(-1381139298054267633161129151 : Int)/10^30)
theorem v835_pa_checked : Scalar.distance (sourceCoefficient 8 96 1 0) v835_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v835_pb : Scalar.QComplex := ((-595930301805948922877496 : Int)/10^30,(-431476922177984553405683122 : Int)/10^30)
theorem v835_pb_checked : Scalar.distance (sourceCoefficient 8 96 1 1) v835_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v835_pg : Scalar.QComplex := ((-93086320910664914711317 : Int)/10^30,(128565298543163612264 : Int)/10^30)
theorem v835_pg_checked : Scalar.distance (sourceCoefficient 8 96 1 2) v835_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v835_mb : Scalar.QComplex := ((-968275230754274812385641 : Int)/10^30,(-431476247258396202959698539 : Int)/10^30)
theorem v835_mb_checked : Scalar.distance (sourceCoefficient 8 96 3 1) v835_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v835_mg : Scalar.QComplex := ((-93086175304311107988382 : Int)/10^30,(208894553166068388778 : Int)/10^30)
theorem v835_mg_checked : Scalar.distance (sourceCoefficient 8 96 3 2) v835_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v835_upper : Scalar.QComplex := ((999995173124421165029338898596 : Int)/10^30,(-3107044875591932574424010108 : Int)/10^30)
theorem v835_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 96 5) 1) 14) v835_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material835 : Material (8 : Basis) (96 : Basis) where
  plus := ![v835_pa,v835_pb,v835_pg]
  minus := ![(Primitive.Addresses.material835 1).one,v835_mb,v835_mg]
  upper := v835_upper
  lower := (Primitive.Addresses.material835 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v835_pa_checked.trans (by decide +kernel)
    · exact v835_pb_checked.trans (by decide +kernel)
    · exact v835_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 96 Primitive.Addresses.material835
    · exact v835_mb_checked.trans (by decide +kernel)
    · exact v835_mg_checked.trans (by decide +kernel)
  upper_error := v835_upper_checked
  lower_error := reuse_lower_error 8 96 Primitive.Addresses.material835

def v836_pa : Scalar.QComplex := ((999998942503090291727793204480 : Int)/10^30,(-1454301447815008664906176003 : Int)/10^30)
theorem v836_pa_checked : Scalar.distance (sourceCoefficient 8 97 1 0) v836_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v836_pb : Scalar.QComplex := ((-627498085856992273240113 : Int)/10^30,(-431476860057093962281997987 : Int)/10^30)
theorem v836_pb_checked : Scalar.distance (sourceCoefficient 8 97 1 1) v836_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v836_pg : Scalar.QComplex := ((-93086309382093855864523 : Int)/10^30,(135375697665516850090 : Int)/10^30)
theorem v836_pg_checked : Scalar.distance (sourceCoefficient 8 97 1 2) v836_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v836_mb : Scalar.QComplex := ((-999842949443658682454406 : Int)/10^30,(-431476157895952866447673003 : Int)/10^30)
theorem v836_mb_checked : Scalar.distance (sourceCoefficient 8 97 3 1) v836_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v836_mg : Scalar.QComplex := ((-93086157898676628154787 : Int)/10^30,(215704939803961186517 : Int)/10^30)
theorem v836_mg_checked : Scalar.distance (sourceCoefficient 8 97 3 2) v836_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v836_upper : Scalar.QComplex := ((999994943129767828882359384179 : Int)/10^30,(-3180206737368765820541437272 : Int)/10^30)
theorem v836_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 97 5) 1) 14) v836_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material836 : Material (8 : Basis) (97 : Basis) where
  plus := ![v836_pa,v836_pb,v836_pg]
  minus := ![(Primitive.Addresses.material836 1).one,v836_mb,v836_mg]
  upper := v836_upper
  lower := (Primitive.Addresses.material836 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v836_pa_checked.trans (by decide +kernel)
    · exact v836_pb_checked.trans (by decide +kernel)
    · exact v836_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 97 Primitive.Addresses.material836
    · exact v836_mb_checked.trans (by decide +kernel)
    · exact v836_mg_checked.trans (by decide +kernel)
  upper_error := v836_upper_checked
  lower_error := reuse_lower_error 8 97 Primitive.Addresses.material836

def v837_pa : Scalar.QComplex := ((999999988975745127098513008321 : Int)/10^30,(148487405608249410482658269 : Int)/10^30)
theorem v837_pa_checked : Scalar.distance (sourceCoefficient 9 10 1 0) v837_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v837_pb : Scalar.QComplex := ((64068977652941530904180 : Int)/10^30,(-431477516117834014250085717 : Int)/10^30)
theorem v837_pb_checked : Scalar.distance (sourceCoefficient 9 10 1 1) v837_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v837_pg : Scalar.QComplex := ((-93086428857165139005834 : Int)/10^30,(-13822162470716374596 : Int)/10^30)
theorem v837_pg_checked : Scalar.distance (sourceCoefficient 9 10 1 2) v837_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v837_mb : Scalar.QComplex := ((-308276709586619585222996 : Int)/10^30,(-431477410747677421783059399 : Int)/10^30)
theorem v837_mb_checked : Scalar.distance (sourceCoefficient 9 10 3 1) v837_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v837_mg : Scalar.QComplex := ((-93086406124737100659616 : Int)/10^30,(66507238322515529500 : Int)/10^30)
theorem v837_mg_checked : Scalar.distance (sourceCoefficient 9 10 3 2) v837_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v837_upper : Scalar.QComplex := ((999998755869021205754586827162 : Int)/10^30,(-1577422077228095102844981497 : Int)/10^30)
theorem v837_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 10 5) 1) 14) v837_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material837 : Material (9 : Basis) (10 : Basis) where
  plus := ![v837_pa,v837_pb,v837_pg]
  minus := ![(Primitive.Addresses.material837 1).one,v837_mb,v837_mg]
  upper := v837_upper
  lower := (Primitive.Addresses.material837 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v837_pa_checked.trans (by decide +kernel)
    · exact v837_pb_checked.trans (by decide +kernel)
    · exact v837_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 10 Primitive.Addresses.material837
    · exact v837_mb_checked.trans (by decide +kernel)
    · exact v837_mg_checked.trans (by decide +kernel)
  upper_error := v837_upper_checked
  lower_error := reuse_lower_error 9 10 Primitive.Addresses.material837

def v838_pa : Scalar.QComplex := ((999999990273445683827019849975 : Int)/10^30,(139474401012300825132905690 : Int)/10^30)
theorem v838_pa_checked : Scalar.distance (sourceCoefficient 9 11 1 0) v838_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v838_pb : Scalar.QComplex := ((60180068765864862587813 : Int)/10^30,(-431477516617638139237531968 : Int)/10^30)
theorem v838_pb_checked : Scalar.distance (sourceCoefficient 9 11 1 1) v838_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v838_pg : Scalar.QComplex := ((-93086428971477858734506 : Int)/10^30,(-12983174049452507905 : Int)/10^30)
theorem v838_pg_checked : Scalar.distance (sourceCoefficient 9 11 1 2) v838_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v838_mb : Scalar.QComplex := ((-312165617456986192486444 : Int)/10^30,(-431477407891528141077824986 : Int)/10^30)
theorem v838_mb_checked : Scalar.distance (sourceCoefficient 9 11 3 1) v838_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v838_mg : Scalar.QComplex := ((-93086405515040556909509 : Int)/10^30,(67346226530032391961 : Int)/10^30)
theorem v838_mg_checked : Scalar.distance (sourceCoefficient 9 11 3 2) v838_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v838_upper : Scalar.QComplex := ((999998741611091550493081415246 : Int)/10^30,(-1586435070639945518860243022 : Int)/10^30)
theorem v838_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 11 5) 1) 14) v838_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material838 : Material (9 : Basis) (11 : Basis) where
  plus := ![v838_pa,v838_pb,v838_pg]
  minus := ![(Primitive.Addresses.material838 1).one,v838_mb,v838_mg]
  upper := v838_upper
  lower := (Primitive.Addresses.material838 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v838_pa_checked.trans (by decide +kernel)
    · exact v838_pb_checked.trans (by decide +kernel)
    · exact v838_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 11 Primitive.Addresses.material838
    · exact v838_mb_checked.trans (by decide +kernel)
    · exact v838_mg_checked.trans (by decide +kernel)
  upper_error := v838_upper_checked
  lower_error := reuse_lower_error 9 11 Primitive.Addresses.material838

def v839_pa : Scalar.QComplex := ((999999990947731170045962667470 : Int)/10^30,(134553103189649638400892270 : Int)/10^30)
theorem v839_pa_checked : Scalar.distance (sourceCoefficient 9 12 1 0) v839_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v839_pb : Scalar.QComplex := ((58056639377077067052319 : Int)/10^30,(-431477516870816461175606384 : Int)/10^30)
theorem v839_pb_checked : Scalar.distance (sourceCoefficient 9 12 1 1) v839_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v839_pg : Scalar.QComplex := ((-93086429030171463045109 : Int)/10^30,(-12525068004232941268 : Int)/10^30)
theorem v839_pg_checked : Scalar.distance (sourceCoefficient 9 12 1 2) v839_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v839_mb : Scalar.QComplex := ((-314289046273605670163256 : Int)/10^30,(-431477406312282441931678365 : Int)/10^30)
theorem v839_mb_checked : Scalar.distance (sourceCoefficient 9 12 3 1) v839_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v839_mg : Scalar.QComplex := ((-93086405178409254671684 : Int)/10^30,(67804332455328078540 : Int)/10^30)
theorem v839_mg_checked : Scalar.distance (sourceCoefficient 9 12 3 2) v839_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v839_upper : Scalar.QComplex := ((999998733791662447197994295798 : Int)/10^30,(-1591356362296657273517034006 : Int)/10^30)
theorem v839_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 12 5) 1) 14) v839_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material839 : Material (9 : Basis) (12 : Basis) where
  plus := ![v839_pa,v839_pb,v839_pg]
  minus := ![(Primitive.Addresses.material839 1).one,v839_mb,v839_mg]
  upper := v839_upper
  lower := (Primitive.Addresses.material839 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v839_pa_checked.trans (by decide +kernel)
    · exact v839_pb_checked.trans (by decide +kernel)
    · exact v839_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 12 Primitive.Addresses.material839
    · exact v839_mb_checked.trans (by decide +kernel)
    · exact v839_mg_checked.trans (by decide +kernel)
  upper_error := v839_upper_checked
  lower_error := reuse_lower_error 9 12 Primitive.Addresses.material839

def v840_pa : Scalar.QComplex := ((999999996552351992425199610888 : Int)/10^30,(83037919068720189082335700 : Int)/10^30)
theorem v840_pa_checked : Scalar.distance (sourceCoefficient 9 13 1 0) v840_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v840_pb : Scalar.QComplex := ((35828995400041211586317 : Int)/10^30,(-431477518684737635503201084 : Int)/10^30)
theorem v840_pb_checked : Scalar.distance (sourceCoefficient 9 13 1 1) v840_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v840_pg : Scalar.QComplex := ((-93086429486695097281131 : Int)/10^30,(-7729703424761612713 : Int)/10^30)
theorem v840_pg_checked : Scalar.distance (sourceCoefficient 9 13 1 2) v840_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v840_mb : Scalar.QComplex := ((-336516683539606096932596 : Int)/10^30,(-431477388944747284593874527 : Int)/10^30)
theorem v840_mb_checked : Scalar.distance (sourceCoefficient 9 13 3 1) v840_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v840_mg : Scalar.QComplex := ((-93086401496749062042618 : Int)/10^30,(72599695643225350455 : Int)/10^30)
theorem v840_mg_checked : Scalar.distance (sourceCoefficient 9 13 3 2) v840_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v840_upper : Scalar.QComplex := ((999998650485740550425341116769 : Int)/10^30,(-1642871479364838465522916455 : Int)/10^30)
theorem v840_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 13 5) 1) 14) v840_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material840 : Material (9 : Basis) (13 : Basis) where
  plus := ![v840_pa,v840_pb,v840_pg]
  minus := ![(Primitive.Addresses.material840 1).one,v840_mb,v840_mg]
  upper := v840_upper
  lower := (Primitive.Addresses.material840 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v840_pa_checked.trans (by decide +kernel)
    · exact v840_pb_checked.trans (by decide +kernel)
    · exact v840_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 13 Primitive.Addresses.material840
    · exact v840_mb_checked.trans (by decide +kernel)
    · exact v840_mg_checked.trans (by decide +kernel)
  upper_error := v840_upper_checked
  lower_error := reuse_lower_error 9 13 Primitive.Addresses.material840

def v841_pa : Scalar.QComplex := ((999999997773714596297988713599 : Int)/10^30,(66727586517479229701802010 : Int)/10^30)
theorem v841_pa_checked : Scalar.distance (sourceCoefficient 9 14 1 0) v841_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v841_pb : Scalar.QComplex := ((28791453539569541830468 : Int)/10^30,(-431477518940830482445658019 : Int)/10^30)
theorem v841_pb_checked : Scalar.distance (sourceCoefficient 9 14 1 1) v841_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v841_pg : Scalar.QComplex := ((-93086429571165817714105 : Int)/10^30,(-6211432796641626263 : Int)/10^30)
theorem v841_pg_checked : Scalar.distance (sourceCoefficient 9 14 1 2) v841_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v841_mb : Scalar.QComplex := ((-343554223000675893400574 : Int)/10^30,(-431477383127758369713529590 : Int)/10^30)
theorem v841_mb_checked : Scalar.distance (sourceCoefficient 9 14 3 1) v841_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v841_mg : Scalar.QComplex := ((-93086400271020579326426 : Int)/10^30,(74117965778918220974 : Int)/10^30)
theorem v841_mg_checked : Scalar.distance (sourceCoefficient 9 14 3 2) v841_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v841_upper : Scalar.QComplex := ((999998623556947013590672016617 : Int)/10^30,(-1659181789731716089213935041 : Int)/10^30)
theorem v841_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 14 5) 1) 14) v841_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material841 : Material (9 : Basis) (14 : Basis) where
  plus := ![v841_pa,v841_pb,v841_pg]
  minus := ![(Primitive.Addresses.material841 1).one,v841_mb,v841_mg]
  upper := v841_upper
  lower := (Primitive.Addresses.material841 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v841_pa_checked.trans (by decide +kernel)
    · exact v841_pb_checked.trans (by decide +kernel)
    · exact v841_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 14 Primitive.Addresses.material841
    · exact v841_mb_checked.trans (by decide +kernel)
    · exact v841_mg_checked.trans (by decide +kernel)
  upper_error := v841_upper_checked
  lower_error := reuse_lower_error 9 14 Primitive.Addresses.material841

def v842_pa : Scalar.QComplex := ((999999999181922742411536750346 : Int)/10^30,(40449406849886885577714329 : Int)/10^30)
theorem v842_pa_checked : Scalar.distance (sourceCoefficient 9 15 1 0) v842_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v842_pb : Scalar.QComplex := ((17453009728163114774330 : Int)/10^30,(-431477519031506163347956426 : Int)/10^30)
theorem v842_pb_checked : Scalar.distance (sourceCoefficient 9 15 1 1) v842_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v842_pg : Scalar.QComplex := ((-93086429646489482592788 : Int)/10^30,(-3765290868054524165 : Int)/10^30)
theorem v842_pg_checked : Scalar.distance (sourceCoefficient 9 15 1 2) v842_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v842_mb : Scalar.QComplex := ((-354892662668510525726307 : Int)/10^30,(-431477373433867672161887851 : Int)/10^30)
theorem v842_mb_checked : Scalar.distance (sourceCoefficient 9 15 3 1) v842_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v842_mg : Scalar.QComplex := ((-93086398235433901930753 : Int)/10^30,(76564106861695819188 : Int)/10^30)
theorem v842_mg_checked : Scalar.distance (sourceCoefficient 9 15 3 2) v842_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v842_upper : Scalar.QComplex := ((999998579611398893916363763587 : Int)/10^30,(-1685459932691486178829404957 : Int)/10^30)
theorem v842_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 15 5) 1) 14) v842_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material842 : Material (9 : Basis) (15 : Basis) where
  plus := ![v842_pa,v842_pb,v842_pg]
  minus := ![(Primitive.Addresses.material842 1).one,v842_mb,v842_mg]
  upper := v842_upper
  lower := (Primitive.Addresses.material842 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v842_pa_checked.trans (by decide +kernel)
    · exact v842_pb_checked.trans (by decide +kernel)
    · exact v842_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 15 Primitive.Addresses.material842
    · exact v842_mb_checked.trans (by decide +kernel)
    · exact v842_mg_checked.trans (by decide +kernel)
  upper_error := v842_upper_checked
  lower_error := reuse_lower_error 9 15 Primitive.Addresses.material842

def v843_pa : Scalar.QComplex := ((999999999311166049750673588162 : Int)/10^30,(37116948958988542013215855 : Int)/10^30)
theorem v843_pa_checked : Scalar.distance (sourceCoefficient 9 16 1 0) v843_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v843_pb : Scalar.QComplex := ((16015129061248452643706 : Int)/10^30,(-431477519014620791488105467 : Int)/10^30)
theorem v843_pb_checked : Scalar.distance (sourceCoefficient 9 16 1 1) v843_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v843_pg : Scalar.QComplex := ((-93086429650683467011285 : Int)/10^30,(-3455084260498875201 : Int)/10^30)
theorem v843_pg_checked : Scalar.distance (sourceCoefficient 9 16 1 2) v843_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v843_mb : Scalar.QComplex := ((-356330542785465185745633 : Int)/10^30,(-431477372176156050783122356 : Int)/10^30)
theorem v843_mb_checked : Scalar.distance (sourceCoefficient 9 16 3 1) v843_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v843_mg : Scalar.QComplex := ((-93086397971933553654082 : Int)/10^30,(76874313357366590680 : Int)/10^30)
theorem v843_mg_checked : Scalar.distance (sourceCoefficient 9 16 3 2) v843_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v843_upper : Scalar.QComplex := ((999998573989122007290517289029 : Int)/10^30,(-1688792385842142175509208432 : Int)/10^30)
theorem v843_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 16 5) 1) 14) v843_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material843 : Material (9 : Basis) (16 : Basis) where
  plus := ![v843_pa,v843_pb,v843_pg]
  minus := ![(Primitive.Addresses.material843 1).one,v843_mb,v843_mg]
  upper := v843_upper
  lower := (Primitive.Addresses.material843 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v843_pa_checked.trans (by decide +kernel)
    · exact v843_pb_checked.trans (by decide +kernel)
    · exact v843_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 16 Primitive.Addresses.material843
    · exact v843_mb_checked.trans (by decide +kernel)
    · exact v843_mg_checked.trans (by decide +kernel)
  upper_error := v843_upper_checked
  lower_error := reuse_lower_error 9 16 Primitive.Addresses.material843

def v844_pa : Scalar.QComplex := ((999999999537144302399595396802 : Int)/10^30,(30425505665256802919597668 : Int)/10^30)
theorem v844_pa_checked : Scalar.distance (sourceCoefficient 9 17 1 0) v844_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v844_pb : Scalar.QComplex := ((13127921703668015248329 : Int)/10^30,(-431477518961421580157126779 : Int)/10^30)
theorem v844_pb_checked : Scalar.distance (sourceCoefficient 9 17 1 1) v844_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v844_pg : Scalar.QComplex := ((-93086429655462655312877 : Int)/10^30,(-2832201694151708575 : Int)/10^30)
theorem v844_pg_checked : Scalar.distance (sourceCoefficient 9 17 1 2) v844_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v844_mb : Scalar.QComplex := ((-359217749022097848643917 : Int)/10^30,(-431477369631426944660983508 : Int)/10^30)
theorem v844_mb_checked : Scalar.distance (sourceCoefficient 9 17 3 1) v844_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v844_mg : Scalar.QComplex := ((-93086397439193139007949 : Int)/10^30,(77497195695910334973 : Int)/10^30)
theorem v844_mg_checked : Scalar.distance (sourceCoefficient 9 17 3 2) v844_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v844_upper : Scalar.QComplex := ((999998562666275841384043079885 : Int)/10^30,(-1695483819559773124219530137 : Int)/10^30)
theorem v844_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 17 5) 1) 14) v844_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material844 : Material (9 : Basis) (17 : Basis) where
  plus := ![v844_pa,v844_pb,v844_pg]
  minus := ![(Primitive.Addresses.material844 1).one,v844_mb,v844_mg]
  upper := v844_upper
  lower := (Primitive.Addresses.material844 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v844_pa_checked.trans (by decide +kernel)
    · exact v844_pb_checked.trans (by decide +kernel)
    · exact v844_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 17 Primitive.Addresses.material844
    · exact v844_mb_checked.trans (by decide +kernel)
    · exact v844_mg_checked.trans (by decide +kernel)
  upper_error := v844_upper_checked
  lower_error := reuse_lower_error 9 17 Primitive.Addresses.material844

def v845_pa : Scalar.QComplex := ((999999999967151273431610000725 : Int)/10^30,(8105396544013189717212138 : Int)/10^30)
theorem v845_pa_checked : Scalar.distance (sourceCoefficient 9 18 1 0) v845_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v845_pb : Scalar.QComplex := ((3497296388176090332660 : Int)/10^30,(-431477518597702989005355966 : Int)/10^30)
theorem v845_pb_checked : Scalar.distance (sourceCoefficient 9 18 1 1) v845_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v845_pg : Scalar.QComplex := ((-93086429636242461849341 : Int)/10^30,(-754502425092911055 : Int)/10^30)
theorem v845_pg_checked : Scalar.distance (sourceCoefficient 9 18 1 2) v845_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v845_mb : Scalar.QComplex := ((-368848370437795064394867 : Int)/10^30,(-431477360956912588931490246 : Int)/10^30)
theorem v845_mb_checked : Scalar.distance (sourceCoefficient 9 18 3 1) v845_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v845_mg : Scalar.QComplex := ((-93086395627012059604598 : Int)/10^30,(79574894174760577761 : Int)/10^30)
theorem v845_mg_checked : Scalar.distance (sourceCoefficient 9 18 3 2) v845_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v845_upper : Scalar.QComplex := ((999998524573798693186816029787 : Int)/10^30,(-1717803896179989127599233486 : Int)/10^30)
theorem v845_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 18 5) 1) 14) v845_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material845 : Material (9 : Basis) (18 : Basis) where
  plus := ![v845_pa,v845_pb,v845_pg]
  minus := ![(Primitive.Addresses.material845 1).one,v845_mb,v845_mg]
  upper := v845_upper
  lower := (Primitive.Addresses.material845 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v845_pa_checked.trans (by decide +kernel)
    · exact v845_pb_checked.trans (by decide +kernel)
    · exact v845_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 18 Primitive.Addresses.material845
    · exact v845_mb_checked.trans (by decide +kernel)
    · exact v845_mg_checked.trans (by decide +kernel)
  upper_error := v845_upper_checked
  lower_error := reuse_lower_error 9 18 Primitive.Addresses.material845

def v846_pa : Scalar.QComplex := ((999999999971527016284907574075 : Int)/10^30,(-7546255192436453844815246 : Int)/10^30)
theorem v846_pa_checked : Scalar.distance (sourceCoefficient 9 19 1 0) v846_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v846_pb : Scalar.QComplex := ((-3256039462015443713202 : Int)/10^30,(-431477518171693249685032912 : Int)/10^30)
theorem v846_pb_checked : Scalar.distance (sourceCoefficient 9 19 1 1) v846_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v846_pg : Scalar.QComplex := ((-93086429590492714663660 : Int)/10^30,(702453952662626972 : Int)/10^30)
theorem v846_pg_checked : Scalar.distance (sourceCoefficient 9 19 1 2) v846_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v846_mb : Scalar.QComplex := ((-375601703405783800451783 : Int)/10^30,(-431477354703078328474550321 : Int)/10^30)
theorem v846_mb_checked : Scalar.distance (sourceCoefficient 9 19 3 1) v846_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v846_mg : Scalar.QComplex := ((-93086394323974594329976 : Int)/10^30,(81031849970544698825 : Int)/10^30)
theorem v846_mg_checked : Scalar.distance (sourceCoefficient 9 19 3 2) v846_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v846_upper : Scalar.QComplex := ((999998497564843439164701691523 : Int)/10^30,(-1733455524612694217085631492 : Int)/10^30)
theorem v846_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 19 5) 1) 14) v846_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material846 : Material (9 : Basis) (19 : Basis) where
  plus := ![v846_pa,v846_pb,v846_pg]
  minus := ![(Primitive.Addresses.material846 1).one,v846_mb,v846_mg]
  upper := v846_upper
  lower := (Primitive.Addresses.material846 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v846_pa_checked.trans (by decide +kernel)
    · exact v846_pb_checked.trans (by decide +kernel)
    · exact v846_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 19 Primitive.Addresses.material846
    · exact v846_mb_checked.trans (by decide +kernel)
    · exact v846_mg_checked.trans (by decide +kernel)
  upper_error := v846_upper_checked
  lower_error := reuse_lower_error 9 19 Primitive.Addresses.material846

def v847_pa : Scalar.QComplex := ((999999999946421274727601065849 : Int)/10^30,(-10351688294279691481185181 : Int)/10^30)
theorem v847_pa_checked : Scalar.distance (sourceCoefficient 9 20 1 0) v847_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v847_pb : Scalar.QComplex := ((-4466520773397452911940 : Int)/10^30,(-431477518080439781484887317 : Int)/10^30)
theorem v847_pb_checked : Scalar.distance (sourceCoefficient 9 20 1 1) v847_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v847_pg : Scalar.QComplex := ((-93086429579480757288607 : Int)/10^30,(963601703485830330 : Int)/10^30)
theorem v847_pg_checked : Scalar.distance (sourceCoefficient 9 20 1 2) v847_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v847_mb : Scalar.QComplex := ((-376812184187700662541035 : Int)/10^30,(-431477353567234040584026822 : Int)/10^30)
theorem v847_mb_checked : Scalar.distance (sourceCoefficient 9 20 3 1) v847_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v847_mg : Scalar.QComplex := ((-93086394087603893752838 : Int)/10^30,(81292997614627836255 : Int)/10^30)
theorem v847_mg_checked : Scalar.distance (sourceCoefficient 9 20 3 2) v847_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v847_upper : Scalar.QComplex := ((999998492697814708120920341688 : Int)/10^30,(-1736260953492844166495390318 : Int)/10^30)
theorem v847_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 20 5) 1) 14) v847_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material847 : Material (9 : Basis) (20 : Basis) where
  plus := ![v847_pa,v847_pb,v847_pg]
  minus := ![(Primitive.Addresses.material847 1).one,v847_mb,v847_mg]
  upper := v847_upper
  lower := (Primitive.Addresses.material847 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v847_pa_checked.trans (by decide +kernel)
    · exact v847_pb_checked.trans (by decide +kernel)
    · exact v847_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 20 Primitive.Addresses.material847
    · exact v847_mb_checked.trans (by decide +kernel)
    · exact v847_mg_checked.trans (by decide +kernel)
  upper_error := v847_upper_checked
  lower_error := reuse_lower_error 9 20 Primitive.Addresses.material847

def v848_pa : Scalar.QComplex := ((999999997992722824508056768744 : Int)/10^30,(-63360510942973974752259379 : Int)/10^30)
theorem v848_pa_checked : Scalar.distance (sourceCoefficient 9 21 1 0) v848_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v848_pb : Scalar.QComplex := ((-27338635897686872000628 : Int)/10^30,(-431477515505140099756217383 : Int)/10^30)
theorem v848_pb_checked : Scalar.distance (sourceCoefficient 9 21 1 1) v848_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v848_pg : Scalar.QComplex := ((-93086429210753358232975 : Int)/10^30,(5898003728489238675 : Int)/10^30)
theorem v848_pg_checked : Scalar.distance (sourceCoefficient 9 21 1 2) v848_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v848_mb : Scalar.QComplex := ((-399684288573288675416539 : Int)/10^30,(-431477331254330087320635090 : Int)/10^30)
theorem v848_mb_checked : Scalar.distance (sourceCoefficient 9 21 3 1) v848_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v848_mg : Scalar.QComplex := ((-93086389460709921630700 : Int)/10^30,(86227397484132718859 : Int)/10^30)
theorem v848_mg_checked : Scalar.distance (sourceCoefficient 9 21 3 2) v848_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v848_upper : Scalar.QComplex := ((999998399255700198884833132563 : Int)/10^30,(-1789269693819217681317224075 : Int)/10^30)
theorem v848_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 9 21 5) 1) 14) v848_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material848 : Material (9 : Basis) (21 : Basis) where
  plus := ![v848_pa,v848_pb,v848_pg]
  minus := ![(Primitive.Addresses.material848 1).one,v848_mb,v848_mg]
  upper := v848_upper
  lower := (Primitive.Addresses.material848 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v848_pa_checked.trans (by decide +kernel)
    · exact v848_pb_checked.trans (by decide +kernel)
    · exact v848_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 9 21 Primitive.Addresses.material848
    · exact v848_mb_checked.trans (by decide +kernel)
    · exact v848_mg_checked.trans (by decide +kernel)
  upper_error := v848_upper_checked
  lower_error := reuse_lower_error 9 21 Primitive.Addresses.material848

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
