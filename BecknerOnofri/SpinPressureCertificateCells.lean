module

public import BecknerOnofri.SpinPressureCertificateSound

@[expose] public section

/-!
# Lemma 5.20 (lem:section5-scalar-pressure) on `[1/16, 0.99]`

The interval `[1/16, 99/100] = [204800/d, 3244032/d]`, `d = 3276800`, is covered by
127 consecutive cells; on each, `checkCell` is evaluated by the kernel. The cells
were chosen greedily by evaluating `checkCell` itself; their choice is not trusted.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

/-- The common denominator of the cell endpoints. -/
def cellDen : ℤ := 3276800

/-- Cells, batch 0. -/
def cells00 : List (ℤ × ℤ) :=
  [(204800, 211394), (211394, 218235), (218235, 225332), (225332, 232694), (232694, 240330),
   (240330, 248249), (248249, 256461), (256461, 264975)]

theorem cells00_check : (cells00.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 1. -/
def cells01 : List (ℤ × ℤ) :=
  [(264975, 273802), (273802, 282951), (282951, 292434), (292434, 302261), (302261, 312444),
   (312444, 322994), (322994, 333923), (333923, 345243)]

theorem cells01_check : (cells01.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 2. -/
def cells02 : List (ℤ × ℤ) :=
  [(345243, 356967), (356967, 369107), (369107, 381676), (381676, 394687), (394687, 408153),
   (408153, 422089), (422089, 436508), (436508, 451425)]

theorem cells02_check : (cells02.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 3. -/
def cells03 : List (ℤ × ℤ) :=
  [(451425, 466853), (466853, 482807), (482807, 499302), (499302, 516353), (516353, 533973),
   (533973, 552178), (552178, 570982), (570982, 590399)]

theorem cells03_check : (cells03.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 4. -/
def cells04 : List (ℤ × ℤ) :=
  [(590399, 610442), (610442, 631125), (631125, 652459), (652459, 674455), (674455, 697122),
   (697122, 720470), (720470, 744507), (744507, 769239)]

theorem cells04_check : (cells04.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 5. -/
def cells05 : List (ℤ × ℤ) :=
  [(769239, 794671), (794671, 820807), (820807, 847649), (847649, 875197), (875197, 903449),
   (903449, 932402), (932402, 962050), (962050, 992388)]

theorem cells05_check : (cells05.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 6. -/
def cells06 : List (ℤ × ℤ) :=
  [(992388, 1023407), (1023407, 1055100), (1055100, 1087456), (1087456, 1120467),
   (1120467, 1154125), (1154125, 1188424), (1188424, 1223359), (1223359, 1258930)]

theorem cells06_check : (cells06.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 7. -/
def cells07 : List (ℤ × ℤ) :=
  [(1258930, 1295142), (1295142, 1332006), (1332006, 1369542), (1369542, 1407780),
   (1407780, 1446764), (1446764, 1486552), (1486552, 1527224), (1527224, 1568882)]

theorem cells07_check : (cells07.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 8. -/
def cells08 : List (ℤ × ℤ) :=
  [(1568882, 1611659), (1611659, 1655723), (1655723, 1701287), (1701287, 1748619),
   (1748619, 1798053), (1798053, 1850004), (1850004, 1904980), (1904980, 1963492)]

theorem cells08_check : (cells08.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 9. -/
def cells09 : List (ℤ × ℤ) :=
  [(1963492, 2025939), (2025939, 2092821), (2092821, 2164406), (2164406, 2240368),
   (2240368, 2319465), (2319465, 2398014), (2398014, 2473668), (2473668, 2545670)]

theorem cells09_check : (cells09.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 10. -/
def cells10 : List (ℤ × ℤ) :=
  [(2545670, 2614801), (2614801, 2680278), (2680278, 2739931), (2739931, 2792347),
   (2792347, 2837374), (2837374, 2875835), (2875835, 2908909), (2908909, 2937675)]

theorem cells10_check : (cells10.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 11. -/
def cells11 : List (ℤ × ℤ) :=
  [(2937675, 2962950), (2962950, 2985399), (2985399, 3005527), (3005527, 3023713),
   (3023713, 3040248), (3040248, 3055361), (3055361, 3069233), (3069233, 3082011)]

theorem cells11_check : (cells11.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 12. -/
def cells12 : List (ℤ × ℤ) :=
  [(3082011, 3093818), (3093818, 3104755), (3104755, 3114910), (3114910, 3124357),
   (3124357, 3133161), (3133161, 3141380), (3141380, 3149064), (3149064, 3156259)]

theorem cells12_check : (cells12.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 13. -/
def cells13 : List (ℤ × ℤ) :=
  [(3156259, 3163004), (3163004, 3169336), (3169336, 3175287), (3175287, 3180887),
   (3180887, 3186162), (3186162, 3191136), (3191136, 3195832), (3195832, 3200269)]

theorem cells13_check : (cells13.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 14. -/
def cells14 : List (ℤ × ℤ) :=
  [(3200269, 3204466), (3204466, 3208440), (3208440, 3212206), (3212206, 3215777),
   (3215777, 3219167), (3219167, 3222387), (3222387, 3225447), (3225447, 3228358)]

theorem cells14_check : (cells14.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- Cells, batch 15. -/
def cells15 : List (ℤ × ℤ) :=
  [(3228358, 3231128), (3231128, 3233765), (3233765, 3236276), (3236276, 3238667),
   (3238667, 3240944), (3240944, 3243111), (3243111, 3244032)]

theorem cells15_check : (cells15.all fun c => checkCell c.1 c.2 cellDen) = true := by
  decide +kernel

/-- All cells. -/
def cells : List (ℤ × ℤ) :=
  cells00 ++ cells01 ++ cells02 ++ cells03 ++ cells04 ++ cells05 ++ cells06 ++ cells07 ++
    cells08 ++ cells09 ++ cells10 ++ cells11 ++ cells12 ++ cells13 ++ cells14 ++ cells15

end BecknerOnofri.HighDim.Spin.PressureCertificate
