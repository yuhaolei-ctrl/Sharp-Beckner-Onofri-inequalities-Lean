import BecknerOnofri.EntropyScalarCertificate.Bessel0430
import BecknerOnofri.EntropyScalarCertificate.Bessel0431
import BecknerOnofri.EntropyScalarCertificate.Bessel0703
import BecknerOnofri.EntropyScalarCertificate.Bessel0704
import BecknerOnofri.EntropyScalarCertificate.Brackets0172
import BecknerOnofri.EntropyScalarCertificate.Logs0344
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2752
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (869310994855851799227607788265843695449617/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (869310994855851799227607788265843695449617/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (870820647179522001469135308600753088811081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (870820647179522001469135308600753088811081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (870065821017686900348371548433298392130349/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (870065821017686900348371548433298392130349/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2752 BracketBatch0172.bracket2753 (870065821017686900348371548433298392130349/10000000000000000000000000000000000000000) (5898157415582292177069993134595102878401/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2752 BracketBatch0172.bracket2753
  (870065821017686900348371548433298392130349/10000000000000000000000000000000000000000) (5898157415582292177069993134595102878401/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2752
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2753
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (435410323589761000734567654300376544405539/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (435410323589761000734567654300376544405539/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (872335559649203436286825582969470661934367/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (872335559649203436286825582969470661934367/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (348631241365745087551192178314044750149089/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (348631241365745087551192178314044750149089/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2753 BracketBatch0172.bracket2754 (348631241365745087551192178314044750149089/4000000000000000000000000000000000000000) (590082164321293840274492258997578295801/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2753 BracketBatch0172.bracket2754
  (348631241365745087551192178314044750149089/4000000000000000000000000000000000000000) (590082164321293840274492258997578295801/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2753
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2754
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (218083889912300859071706395742367665483591/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (218083889912300859071706395742367665483591/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (873855759804926294925827527960711782012767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (873855759804926294925827527960711782012767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (1746191319454129731212653110930182443947131/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1746191319454129731212653110930182443947131/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2754 BracketBatch0172.bracket2755 (1746191319454129731212653110930182443947131/20000000000000000000000000000000000000000) (5903490618267668467648409936276860553471/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2754 BracketBatch0172.bracket2755
  (1746191319454129731212653110930182443947131/20000000000000000000000000000000000000000) (5903490618267668467648409936276860553471/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2754
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2755
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (218463939951231573731456881990177945503191/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (218463939951231573731456881990177945503191/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (437690637689654196222024266434341363834377/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (437690637689654196222024266434341363834377/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (874618517592117343684938030414697254840759/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (874618517592117343684938030414697254840759/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2755 BracketBatch0172.bracket2756 (874618517592117343684938030414697254840759/10000000000000000000000000000000000000000) (5906164356919306129187737010976596399039/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2755 BracketBatch0172.bracket2756
  (874618517592117343684938030414697254840759/10000000000000000000000000000000000000000) (5906164356919306129187737010976596399039/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2755
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2756
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (875381275379308392444048532868682727668751/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (875381275379308392444048532868682727668751/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (438456067149620787112694262330400189418021/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (438456067149620787112694262330400189418021/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (1752293409678549966669437057529483106504793/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1752293409678549966669437057529483106504793/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2756 BracketBatch0172.bracket2757 (1752293409678549966669437057529483106504793/20000000000000000000000000000000000000000) (590884287542159956671965559407959132031/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2756 BracketBatch0172.bracket2757
  (1752293409678549966669437057529483106504793/20000000000000000000000000000000000000000) (590884287542159956671965559407959132031/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2756
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2757
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (876912134299241574225388524660800378836039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (876912134299241574225388524660800378836039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (439224182343797937070240881166344831502487/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (439224182343797937070240881166344831502487/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1755360498986837448365870286993490041841013/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1755360498986837448365870286993490041841013/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2757 BracketBatch0172.bracket2758 (1755360498986837448365870286993490041841013/20000000000000000000000000000000000000000) (5911526190109747303004636150515916032223/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2757 BracketBatch0172.bracket2758
  (1755360498986837448365870286993490041841013/20000000000000000000000000000000000000000) (5911526190109747303004636150515916032223/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2757
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2758
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (878448364687595874140481762332689663004971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (878448364687595874140481762332689663004971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (879989994864941642740768072610655737182989/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (879989994864941642740768072610655737182989/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (43960958988813437922031245873583635004699/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43960958988813437922031245873583635004699/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2758 BracketBatch0172.bracket2759 (43960958988813437922031245873583635004699/500000000000000000000000000000000000000) (5914214317400928242711070966114543798401/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2758 BracketBatch0172.bracket2759
  (43960958988813437922031245873583635004699/500000000000000000000000000000000000000) (5914214317400928242711070966114543798401/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2758
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2759
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (439994997432470821370384036305327868591493/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (439994997432470821370384036305327868591493/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0431.rows BesselBatch0431.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (220384263337822466736892970698063353427267/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (220384263337822466736892970698063353427267/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0704.rows BesselBatch0704.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (880763524108115754844169977701454575446027/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (880763524108115754844169977701454575446027/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0344.rows ScalarLogs0344.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0172.bracket2759 BracketBatch0172.bracket2760 (880763524108115754844169977701454575446027/10000000000000000000000000000000000000000) (2958453636897417932253700480052234529369/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0172.bracket2759 BracketBatch0172.bracket2760
  (880763524108115754844169977701454575446027/10000000000000000000000000000000000000000) (2958453636897417932253700480052234529369/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2759
