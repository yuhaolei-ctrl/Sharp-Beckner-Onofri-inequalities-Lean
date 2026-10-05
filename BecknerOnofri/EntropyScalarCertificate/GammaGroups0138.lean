import BecknerOnofri.EntropyScalarCertificate.Bessel0172
import BecknerOnofri.EntropyScalarCertificate.Bessel0173
import BecknerOnofri.EntropyScalarCertificate.Bessel0575
import BecknerOnofri.EntropyScalarCertificate.Brackets0069
import BecknerOnofri.EntropyScalarCertificate.Logs0138
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1104
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1459653746966627474407408968911988262377/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1459653746966627474407408968911988262377/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (3658947946826627745506885229182415000857/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3658947946826627745506885229182415000857/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (14616164628486392863050815302924771313599/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14616164628486392863050815302924771313599/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1104 BracketBatch0069.bracket1105 (14616164628486392863050815302924771313599/20000000000000000000000000000000000000000) (3391302379565081125400831710570050111/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1104 BracketBatch0069.bracket1105
  (14616164628486392863050815302924771313599/20000000000000000000000000000000000000000) (3391302379565081125400831710570050111/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1104
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1105
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (7317895893653255491013770458364830001711/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7317895893653255491013770458364830001711/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (3668791662404264118097514749183021230691/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3668791662404264118097514749183021230691/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (14655479218461783727208799956730872463093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14655479218461783727208799956730872463093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1105 BracketBatch0069.bracket1106 (14655479218461783727208799956730872463093/20000000000000000000000000000000000000000) (109342922160175297326063029035305112561/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1105 BracketBatch0069.bracket1106
  (14655479218461783727208799956730872463093/20000000000000000000000000000000000000000) (109342922160175297326063029035305112561/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1105
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1106
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (7337583324808528236195029498366042461379/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7337583324808528236195029498366042461379/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (3678665731462999209220006269429977779827/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3678665731462999209220006269429977779827/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (14694914787734526654635042037225998021033/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14694914787734526654635042037225998021033/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1106 BracketBatch0069.bracket1107 (14694914787734526654635042037225998021033/20000000000000000000000000000000000000000) (110169399837152670549646586445009192693/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1106 BracketBatch0069.bracket1107
  (14694914787734526654635042037225998021033/20000000000000000000000000000000000000000) (110169399837152670549646586445009192693/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1106
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1107
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0172.rows BesselBatch0172.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (7357331462925998418440012538859955559651/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7357331462925998418440012538859955559651/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (7377140746902892314785960145245927834189/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7377140746902892314785960145245927834189/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (184180902622861134165324658551323542423/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (184180902622861134165324658551323542423/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1107 BracketBatch0069.bracket1108 (184180902622861134165324658551323542423/250000000000000000000000000000000000000) (22200227985972280432561057509096536547/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1107 BracketBatch0069.bracket1108
  (184180902622861134165324658551323542423/250000000000000000000000000000000000000) (22200227985972280432561057509096536547/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1107
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1108
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (3688570373451446157392980072622963917093/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3688570373451446157392980072622963917093/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (3698505809980616922730925259808373960141/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3698505809980616922730925259808373960141/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (3693538091716031540061952666215668938617/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3693538091716031540061952666215668938617/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1108 BracketBatch0069.bracket1109 (3693538091716031540061952666215668938617/5000000000000000000000000000000000000000) (2236763468218452061125430046393333649/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1108 BracketBatch0069.bracket1109
  (3693538091716031540061952666215668938617/5000000000000000000000000000000000000000) (2236763468218452061125430046393333649/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1108
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1109
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (7397011619961233845461850519616747920279/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7397011619961233845461850519616747920279/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (7416944529703306087436014854965073442833/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7416944529703306087436014854965073442833/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1851744518708067491612233171822727670389/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1851744518708067491612233171822727670389/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1109 BracketBatch0069.bracket1110 (1851744518708067491612233171822727670389/2500000000000000000000000000000000000000) (11268053147512329933615769622117733227/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1109 BracketBatch0069.bracket1110
  (1851744518708067491612233171822727670389/2500000000000000000000000000000000000000) (11268053147512329933615769622117733227/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1109
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1110
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (741694452970330608743601485496507344283/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (741694452970330608743601485496507344283/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (7436939928167975536110862989763886994729/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7436939928167975536110862989763886994729/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (14853884457871281623546877844728960437559/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14853884457871281623546877844728960437559/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1110 BracketBatch0069.bracket1111 (14853884457871281623546877844728960437559/20000000000000000000000000000000000000000) (28382061385460730381332038243091361079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1110 BracketBatch0069.bracket1111
  (14853884457871281623546877844728960437559/20000000000000000000000000000000000000000) (28382061385460730381332038243091361079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1110
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1111
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (3718469964083987768055431494881943497363/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3718469964083987768055431494881943497363/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0173.rows BesselBatch0173.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (3728499135943947423417129445006085289983/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3728499135943947423417129445006085289983/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0575.rows BesselBatch0575.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (3723484550013967595736280469944014393673/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3723484550013967595736280469944014393673/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0138.rows ScalarLogs0138.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0069.bracket1111 BracketBatch0069.bracket1112 (3723484550013967595736280469944014393673/5000000000000000000000000000000000000000) (114381347257515396670434902086122953679/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0069.bracket1111 BracketBatch0069.bracket1112
  (3723484550013967595736280469944014393673/5000000000000000000000000000000000000000) (114381347257515396670434902086122953679/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1111
