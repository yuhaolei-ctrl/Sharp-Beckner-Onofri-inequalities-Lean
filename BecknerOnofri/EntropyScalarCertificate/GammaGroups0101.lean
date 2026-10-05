import BecknerOnofri.EntropyScalarCertificate.Bessel0126
import BecknerOnofri.EntropyScalarCertificate.Bessel0127
import BecknerOnofri.EntropyScalarCertificate.Bessel0552
import BecknerOnofri.EntropyScalarCertificate.Brackets0050
import BecknerOnofri.EntropyScalarCertificate.Brackets0051
import BecknerOnofri.EntropyScalarCertificate.Logs0101
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0808
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3031237223093096129185896187268596375491/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3031237223093096129185896187268596375491/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1521335064753133432225499700230308508143/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1521335064753133432225499700230308508143/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (6073907352599362993636895587729213391777/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6073907352599362993636895587729213391777/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0808 BracketBatch0050.bracket0809 (6073907352599362993636895587729213391777/20000000000000000000000000000000000000000) (227600544173219483719739657191891541/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0808 BracketBatch0050.bracket0809
  (6073907352599362993636895587729213391777/20000000000000000000000000000000000000000) (227600544173219483719739657191891541/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0808
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0809
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3042670129506266864450999400460617016283/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3042670129506266864450999400460617016283/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1527057112305979797161233334579265365259/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1527057112305979797161233334579265365259/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (6096784354118226458773466069619147746801/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6096784354118226458773466069619147746801/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0809 BracketBatch0050.bracket0810 (6096784354118226458773466069619147746801/20000000000000000000000000000000000000000) (721313196262177703820844697237575241/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0809 BracketBatch0050.bracket0810
  (6096784354118226458773466069619147746801/20000000000000000000000000000000000000000) (721313196262177703820844697237575241/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0809
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0810
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (610822844922391918864493333831706146103/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (610822844922391918864493333831706146103/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (3065569567132832807915314235559374233969/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3065569567132832807915314235559374233969/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (1529920947936198100559445226179476241121/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1529920947936198100559445226179476241121/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0810 BracketBatch0050.bracket0811 (1529920947936198100559445226179476241121/5000000000000000000000000000000000000000) (5851863248529380010640649687614394407/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0810 BracketBatch0050.bracket0811
  (1529920947936198100559445226179476241121/5000000000000000000000000000000000000000) (5851863248529380010640649687614394407/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0810
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0811
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1532784783566416403957657117779687116983/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1532784783566416403957657117779687116983/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (3077036216053063208824515670903147269763/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3077036216053063208824515670903147269763/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (6142605783185896016739829906462521503729/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6142605783185896016739829906462521503729/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0811 BracketBatch0050.bracket0812 (6142605783185896016739829906462521503729/20000000000000000000000000000000000000000) (1483523295864936271883870902005380739/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0811 BracketBatch0050.bracket0812
  (6142605783185896016739829906462521503729/20000000000000000000000000000000000000000) (1483523295864936271883870902005380739/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0811
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0812
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (4807869087582911263788305735786167609/15625000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4807869087582911263788305735786167609/15625000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (3088514230620325496853900164133178184947/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3088514230620325496853900164133178184947/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (6165550446673388705678415835036325454707/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6165550446673388705678415835036325454707/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0812 BracketBatch0050.bracket0813 (6165550446673388705678415835036325454707/20000000000000000000000000000000000000000) (1203440390040718382628521818913986759/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0812 BracketBatch0050.bracket0813
  (6165550446673388705678415835036325454707/20000000000000000000000000000000000000000) (1203440390040718382628521818913986759/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0812
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0813
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (193032139413770343553368760258323636559/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (193032139413770343553368760258323636559/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (3100003670347788290304162013377710637223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3100003670347788290304162013377710637223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (6188517900968113787158062177510888822167/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6188517900968113787158062177510888822167/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0813 BracketBatch0050.bracket0814 (6188517900968113787158062177510888822167/20000000000000000000000000000000000000000) (152529903891842209735345070143187907/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0813 BracketBatch0050.bracket0814
  (6188517900968113787158062177510888822167/20000000000000000000000000000000000000000) (152529903891842209735345070143187907/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0813
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0814
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (155000183517389414515208100668885531861/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (155000183517389414515208100668885531861/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (622300919003225271193045244012925188971/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (622300919003225271193045244012925188971/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (248460330614556585850775529337693463283/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (248460330614556585850775529337693463283/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0814 BracketBatch0050.bracket0815 (248460330614556585850775529337693463283/800000000000000000000000000000000000000) (6186082438497374620041518202209406831/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0814 BracketBatch0050.bracket0815
  (248460330614556585850775529337693463283/800000000000000000000000000000000000000) (6186082438497374620041518202209406831/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0814
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0815
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (777876148754031588991306555016156486213/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (777876148754031588991306555016156486213/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0127.rows BesselBatch0127.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (780754266168887328972216463876679650141/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (780754266168887328972216463876679650141/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (779315207461459458981761509446418068177/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (779315207461459458981761509446418068177/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0101.rows ScalarLogs0101.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0815 BracketBatch0051.bracket0816 (779315207461459458981761509446418068177/2500000000000000000000000000000000000000) (3135933734567164256751192158296666297/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0815 BracketBatch0051.bracket0816
  (779315207461459458981761509446418068177/2500000000000000000000000000000000000000) (3135933734567164256751192158296666297/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0815
