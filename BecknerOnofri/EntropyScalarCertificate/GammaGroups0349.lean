import BecknerOnofri.EntropyScalarCertificate.Bessel0436
import BecknerOnofri.EntropyScalarCertificate.Bessel0437
import BecknerOnofri.EntropyScalarCertificate.Bessel0707
import BecknerOnofri.EntropyScalarCertificate.Brackets0174
import BecknerOnofri.EntropyScalarCertificate.Brackets0175
import BecknerOnofri.EntropyScalarCertificate.Logs0349
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2792
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (46704543995067799081816634046159060973629/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46704543995067799081816634046159060973629/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (233958622188940909862348819423932854147823/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (233958622188940909862348819423932854147823/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (14608791942633747039732249676710254969249/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14608791942633747039732249676710254969249/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2792 BracketBatch0174.bracket2793 (14608791942633747039732249676710254969249/156250000000000000000000000000000000000) (1502149264336720864174182988145206730277/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2792 BracketBatch0174.bracket2793
  (14608791942633747039732249676710254969249/156250000000000000000000000000000000000) (1502149264336720864174182988145206730277/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2792
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2793
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (935834488755763639449395277695731416591289/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (935834488755763639449395277695731416591289/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (937584628016243584499458088877379356518661/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (937584628016243584499458088877379356518661/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (37468382335440144478977067331462215462199/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37468382335440144478977067331462215462199/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2793 BracketBatch0174.bracket2794 (37468382335440144478977067331462215462199/400000000000000000000000000000000000000) (3005732323598291829520730620252036806153/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2793 BracketBatch0174.bracket2794
  (37468382335440144478977067331462215462199/400000000000000000000000000000000000000) (3005732323598291829520730620252036806153/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2793
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2794
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (468792314008121792249729044438689678259329/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (468792314008121792249729044438689678259329/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (469670667219650708560789727588374817111539/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (469670667219650708560789727588374817111539/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (234615745306943125202629693006766123842717/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (234615745306943125202629693006766123842717/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2794 BracketBatch0174.bracket2795 (234615745306943125202629693006766123842717/2500000000000000000000000000000000000000) (6014337700102142111543295271427092820479/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2794 BracketBatch0174.bracket2795
  (234615745306943125202629693006766123842717/2500000000000000000000000000000000000000) (6014337700102142111543295271427092820479/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2794
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2795
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (37573653377572056684863178207069985368923/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (37573653377572056684863178207069985368923/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (470552322528903720758654057341251263282567/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (470552322528903720758654057341251263282567/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1880445979497108858638887569859252160788209/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1880445979497108858638887569859252160788209/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2795 BracketBatch0174.bracket2796 (1880445979497108858638887569859252160788209/20000000000000000000000000000000000000000) (3008608117963915453493737266053151980773/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2795 BracketBatch0174.bracket2796
  (1880445979497108858638887569859252160788209/20000000000000000000000000000000000000000) (3008608117963915453493737266053151980773/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2795
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2796
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0436.rows BesselBatch0436.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (941104645057807441517308114682502526565131/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (941104645057807441517308114682502526565131/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (942874597183598969934203664028932556619051/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (942874597183598969934203664028932556619051/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (941989621120703205725755889355717541592091/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (941989621120703205725755889355717541592091/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2796 BracketBatch0174.bracket2797 (941989621120703205725755889355717541592091/10000000000000000000000000000000000000000) (188128133582609031742980791004253481577/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2796 BracketBatch0174.bracket2797
  (941989621120703205725755889355717541592091/10000000000000000000000000000000000000000) (188128133582609031742980791004253481577/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2796
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2797
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (117859324647949871241775458003616569577381/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (117859324647949871241775458003616569577381/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (472325614205056043446336174038969996790261/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (472325614205056043446336174038969996790261/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (188752582559371105682687601210687255019957/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (188752582559371105682687601210687255019957/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2797 BracketBatch0174.bracket2798 (188752582559371105682687601210687255019957/2000000000000000000000000000000000000000) (6022989836325245050622659724734976199263/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2797 BracketBatch0174.bracket2798
  (188752582559371105682687601210687255019957/2000000000000000000000000000000000000000) (6022989836325245050622659724734976199263/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2797
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2798
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (944651228410112086892672348077939993580519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (944651228410112086892672348077939993580519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (946434576615043263290611953730344448270549/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (946434576615043263290611953730344448270549/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (472771451256288837545821075452071110462767/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (472771451256288837545821075452071110462767/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2798 BracketBatch0174.bracket2799 (472771451256288837545821075452071110462767/5000000000000000000000000000000000000000) (6025884941156245906943151149095693214759/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2798 BracketBatch0174.bracket2799
  (472771451256288837545821075452071110462767/5000000000000000000000000000000000000000) (6025884941156245906943151149095693214759/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2798
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2799
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (473217288307521631645305976865172224135273/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (473217288307521631645305976865172224135273/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0437.rows BesselBatch0437.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (118528084995380152015360277055417852752267/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (118528084995380152015360277055417852752267/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0707.rows BesselBatch0707.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (947329628289042239706747085086843635144341/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (947329628289042239706747085086843635144341/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0349.rows ScalarLogs0349.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0174.bracket2799 BracketBatch0175.bracket2800 (947329628289042239706747085086843635144341/10000000000000000000000000000000000000000) (3014392804713695665755302194175369979667/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0174.bracket2799 BracketBatch0175.bracket2800
  (947329628289042239706747085086843635144341/10000000000000000000000000000000000000000) (3014392804713695665755302194175369979667/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2799
