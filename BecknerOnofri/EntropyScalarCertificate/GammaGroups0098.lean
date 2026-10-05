import BecknerOnofri.EntropyScalarCertificate.Bessel0122
import BecknerOnofri.EntropyScalarCertificate.Bessel0123
import BecknerOnofri.EntropyScalarCertificate.Bessel0550
import BecknerOnofri.EntropyScalarCertificate.Brackets0049
import BecknerOnofri.EntropyScalarCertificate.Logs0098
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0784
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1380027900217298562951308007413599853439/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1380027900217298562951308007413599853439/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (346404643538995510014122526169639783063/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (346404643538995510014122526169639783063/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (2765646474373280603007798112092158985691/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2765646474373280603007798112092158985691/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0784 BracketBatch0049.bracket0785 (2765646474373280603007798112092158985691/10000000000000000000000000000000000000000) (4001446106934239184993132118715720191/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0784 BracketBatch0049.bracket0785
  (2765646474373280603007798112092158985691/10000000000000000000000000000000000000000) (4001446106934239184993132118715720191/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0784
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0785
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2771237148311964080112980209357118264501/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2771237148311964080112980209357118264501/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1391214174556894228998468015598975388733/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1391214174556894228998468015598975388733/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (5553665497425752538109916240555069041967/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5553665497425752538109916240555069041967/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0785 BracketBatch0049.bracket0786 (5553665497425752538109916240555069041967/20000000000000000000000000000000000000000) (2031522519652443807256616799722773683/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0785 BracketBatch0049.bracket0786
  (5553665497425752538109916240555069041967/20000000000000000000000000000000000000000) (2031522519652443807256616799722773683/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0785
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0786
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2782428349113788457996936031197950777463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2782428349113788457996936031197950777463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (349203681980126977208312546599620643553/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (349203681980126977208312546599620643553/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (5576057804954804275663436403994915925887/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5576057804954804275663436403994915925887/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0786 BracketBatch0049.bracket0787 (5576057804954804275663436403994915925887/20000000000000000000000000000000000000000) (330028923052036283616751329580109/800000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0786 BracketBatch0049.bracket0787
  (5576057804954804275663436403994915925887/20000000000000000000000000000000000000000) (330028923052036283616751329580109/800000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0786
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0787
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2793629455841015817666500372796965148421/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2793629455841015817666500372796965148421/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (701210130428258570676424353141544669857/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (701210130428258570676424353141544669857/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (5598469977554050100372197785363143827849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5598469977554050100372197785363143827849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0787 BracketBatch0049.bracket0788 (5598469977554050100372197785363143827849/20000000000000000000000000000000000000000) (837680274101881516001042560273092517/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0787 BracketBatch0049.bracket0788
  (5598469977554050100372197785363143827849/20000000000000000000000000000000000000000) (837680274101881516001042560273092517/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0787
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0788
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (112193620868521371308227896502647147177/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (112193620868521371308227896502647147177/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (2816061600169312491409565128555045276253/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2816061600169312491409565128555045276253/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2810451060941173387057631270560611977839/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2810451060941173387057631270560611977839/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0788 BracketBatch0049.bracket0789 (2810451060941173387057631270560611977839/10000000000000000000000000000000000000000) (2126085217983581755278457259826118519/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0788 BracketBatch0049.bracket0789
  (2810451060941173387057631270560611977839/10000000000000000000000000000000000000000) (2126085217983581755278457259826118519/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0788
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0789
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (2252849280135449993127652102844036221/8000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2252849280135449993127652102844036221/8000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2827292744871050193485470174879613199211/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2827292744871050193485470174879613199211/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (5643354345040362684895035303434658475461/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5643354345040362684895035303434658475461/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0789 BracketBatch0049.bracket0790 (5643354345040362684895035303434658475461/20000000000000000000000000000000000000000) (539584357844713854149463144383512881/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0789 BracketBatch0049.bracket0790
  (5643354345040362684895035303434658475461/20000000000000000000000000000000000000000) (539584357844713854149463144383512881/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0789
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0790
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (353411593108881274185683771859951649901/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (353411593108881274185683771859951649901/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2838534009702841621858505509031794204193/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2838534009702841621858505509031794204193/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (5665826754573891815343975683911407403401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5665826754573891815343975683911407403401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0790 BracketBatch0049.bracket0791 (5665826754573891815343975683911407403401/20000000000000000000000000000000000000000) (4381920565534707136370752132806417831/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0790 BracketBatch0049.bracket0791
  (5665826754573891815343975683911407403401/20000000000000000000000000000000000000000) (4381920565534707136370752132806417831/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0790
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0791
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (283853400970284162185850550903179420419/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (283853400970284162185850550903179420419/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0123.rows BesselBatch0123.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (2849785448774351768635261130678411367487/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2849785448774351768635261130678411367487/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (5688319458477193390493766639710205571677/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5688319458477193390493766639710205571677/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0098.rows ScalarLogs0098.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0049.bracket0791 BracketBatch0049.bracket0792 (5688319458477193390493766639710205571677/20000000000000000000000000000000000000000) (889582696313592849092805093611365109/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0049.bracket0791 BracketBatch0049.bracket0792
  (5688319458477193390493766639710205571677/20000000000000000000000000000000000000000) (889582696313592849092805093611365109/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0791
