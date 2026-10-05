import BecknerOnofri.EntropyScalarCertificate.Bessel0005
import BecknerOnofri.EntropyScalarCertificate.Bessel0006
import BecknerOnofri.EntropyScalarCertificate.Bessel0491
import BecknerOnofri.EntropyScalarCertificate.Bessel0492
import BecknerOnofri.EntropyScalarCertificate.Brackets0002
import BecknerOnofri.EntropyScalarCertificate.Logs0004
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0032
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (40145087516519697235564302307790911491/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40145087516519697235564302307790911491/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (2511033210883734661696818026159100947/39062500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2511033210883734661696818026159100947/39062500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (80321618890659451822713390726336526643/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (80321618890659451822713390726336526643/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0032 BracketBatch0002.bracket0033 (80321618890659451822713390726336526643/1250000000000000000000000000000000000000) (13149533123061857248850416307648177/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0032 BracketBatch0002.bracket0033
  (80321618890659451822713390726336526643/1250000000000000000000000000000000000000) (13149533123061857248850416307648177/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0032
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0033
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (642824501986236073394385414696729842429/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (642824501986236073394385414696729842429/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (160831902143714996980024898674547185789/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (160831902143714996980024898674547185789/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (257230422112219212262897001878983717117/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (257230422112219212262897001878983717117/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0033 BracketBatch0002.bracket0034 (257230422112219212262897001878983717117/4000000000000000000000000000000000000000) (65953611944355825414547835842697/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0033 BracketBatch0002.bracket0034
  (257230422112219212262897001878983717117/4000000000000000000000000000000000000000) (65953611944355825414547835842697/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0033
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0034
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (643327608574859987920099594698188743153/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (643327608574859987920099594698188743153/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (321915360017033690177605521343159005783/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (321915360017033690177605521343159005783/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1287158328608927368275310637384506754719/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1287158328608927368275310637384506754719/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0034 BracketBatch0002.bracket0035 (1287158328608927368275310637384506754719/20000000000000000000000000000000000000000) (661600412020603093569582299622213/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0034 BracketBatch0002.bracket0035
  (1287158328608927368275310637384506754719/20000000000000000000000000000000000000000) (661600412020603093569582299622213/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0034
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0035
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (643830720034067380355211042686318011563/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (643830720034067380355211042686318011563/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (322166918183869468957736522321067391473/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322166918183869468957736522321067391473/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1288164556401806318270684087328452794509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1288164556401806318270684087328452794509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0035 BracketBatch0002.bracket0036 (1288164556401806318270684087328452794509/20000000000000000000000000000000000000000) (13273390828931786001299232066271263/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0035 BracketBatch0002.bracket0036
  (1288164556401806318270684087328452794509/20000000000000000000000000000000000000000) (13273390828931786001299232066271263/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0035
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0036
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (644333836367738937915473044642134782943/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (644333836367738937915473044642134782943/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (644836957579755554192784821619185553729/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (644836957579755554192784821619185553729/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (40286587310859202878383058320666260521/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40286587310859202878383058320666260521/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0036 BracketBatch0002.bracket0037 (40286587310859202878383058320666260521/625000000000000000000000000000000000000) (13314870305797370506010237253472299/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0036 BracketBatch0002.bracket0037
  (40286587310859202878383058320666260521/625000000000000000000000000000000000000) (13314870305797370506010237253472299/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0036
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0037
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (322418478789877777096392410809592776863/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (322418478789877777096392410809592776863/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (322670041836999164662322445901748645259/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322670041836999164662322445901748645259/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (322544260313438470879357428355670711061/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (322544260313438470879357428355670711061/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0037 BracketBatch0002.bracket0038 (322544260313438470879357428355670711061/5000000000000000000000000000000000000000) (3339111705623911917497430688240407/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0037 BracketBatch0002.bracket0038
  (322544260313438470879357428355670711061/5000000000000000000000000000000000000000) (3339111705623911917497430688240407/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0037
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0038
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (129068016734799665864928978360699458103/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (129068016734799665864928978360699458103/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (645843214654348570163625497789671160461/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (645843214654348570163625497789671160461/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (40349478072760840609008449674786514093/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40349478072760840609008449674786514093/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0038 BracketBatch0002.bracket0039 (40349478072760840609008449674786514093/625000000000000000000000000000000000000) (209345633291144588081966771037187/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0038 BracketBatch0002.bracket0039
  (40349478072760840609008449674786514093/625000000000000000000000000000000000000) (209345633291144588081966771037187/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0038
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0039
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (322921607327174285081812748894835580229/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (322921607327174285081812748894835580229/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0006.rows BesselBatch0006.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (646346350524687790446868117082022491343/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (646346350524687790446868117082022491343/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1292189565179036360610493614871693651801/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1292189565179036360610493614871693651801/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0004.rows ScalarLogs0004.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0002.bracket0039 BracketBatch0002.bracket0040 (1292189565179036360610493614871693651801/20000000000000000000000000000000000000000) (13439891581936633023530733001166461/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0002.bracket0039 BracketBatch0002.bracket0040
  (1292189565179036360610493614871693651801/20000000000000000000000000000000000000000) (13439891581936633023530733001166461/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0039
