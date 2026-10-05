import BecknerOnofri.EntropyScalarCertificate.Bessel0162
import BecknerOnofri.EntropyScalarCertificate.Bessel0163
import BecknerOnofri.EntropyScalarCertificate.Bessel0570
import BecknerOnofri.EntropyScalarCertificate.Brackets0065
import BecknerOnofri.EntropyScalarCertificate.Logs0130
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1040
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (384399885741923023925763689642548943543/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (384399885741923023925763689642548943543/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1541727769841526752756628392892396376411/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1541727769841526752756628392892396376411/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (3079327312809218848459683151462592150583/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3079327312809218848459683151462592150583/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1040 BracketBatch0065.bracket1041 (3079327312809218848459683151462592150583/5000000000000000000000000000000000000000) (8196446857172226121382326710594066741/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1040 BracketBatch0065.bracket1041
  (3079327312809218848459683151462592150583/5000000000000000000000000000000000000000) (8196446857172226121382326710594066741/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1040
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1041
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (6166911079366107011026513571569585505641/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6166911079366107011026513571569585505641/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (6183463345818855313039249069437997917559/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6183463345818855313039249069437997917559/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (15437968031481202905082203301259479279/25000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15437968031481202905082203301259479279/25000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1041 BracketBatch0065.bracket1042 (15437968031481202905082203301259479279/25000000000000000000000000000000000000) (13222707629693569108112912941083149249/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1041 BracketBatch0065.bracket1042
  (15437968031481202905082203301259479279/25000000000000000000000000000000000000) (13222707629693569108112912941083149249/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1041
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1042
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1545865836454713828259812267359499479389/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1545865836454713828259812267359499479389/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1550013804143330950358094414039670622401/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1550013804143330950358094414039670622401/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (309587964059804477861790668139917010179/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (309587964059804477861790668139917010179/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1042 BracketBatch0065.bracket1043 (309587964059804477861790668139917010179/500000000000000000000000000000000000000) (13331827833149532113865570778885864521/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1042 BracketBatch0065.bracket1043
  (309587964059804477861790668139917010179/500000000000000000000000000000000000000) (13331827833149532113865570778885864521/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1042
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1043
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0162.rows BesselBatch0162.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (6200055216573323801432377656158682489601/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6200055216573323801432377656158682489601/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (97135733421742008158045403702169120263/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (97135733421742008158045403702169120263/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (12416742155564812323547283493097506186433/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12416742155564812323547283493097506186433/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1043 BracketBatch0065.bracket1044 (12416742155564812323547283493097506186433/20000000000000000000000000000000000000000) (4200524902625326507281982599749128011/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1043 BracketBatch0065.bracket1044
  (12416742155564812323547283493097506186433/20000000000000000000000000000000000000000) (4200524902625326507281982599749128011/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1043
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1044
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (6216686938991488522114905836938823696829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6216686938991488522114905836938823696829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (311667938123749588414009030828973130627/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (311667938123749588414009030828973130627/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (12450045701466480290395086453518286309369/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12450045701466480290395086453518286309369/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1044 BracketBatch0065.bracket1045 (12450045701466480290395086453518286309369/20000000000000000000000000000000000000000) (2710453465234145494600977074549263467/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1044 BracketBatch0065.bracket1045
  (12450045701466480290395086453518286309369/20000000000000000000000000000000000000000) (2710453465234145494600977074549263467/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1044
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1045
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (6233358762474991768280180616579462612537/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6233358762474991768280180616579462612537/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (3125035469243717056374310431539870029667/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3125035469243717056374310431539870029667/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (12483429700962425881028801479659202671871/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12483429700962425881028801479659202671871/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1045 BracketBatch0065.bracket1046 (12483429700962425881028801479659202671871/20000000000000000000000000000000000000000) (426987340673660303228327715673261271/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1045 BracketBatch0065.bracket1046
  (12483429700962425881028801479659202671871/20000000000000000000000000000000000000000) (426987340673660303228327715673261271/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1045
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1046
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (6250070938487434112748620863079740059331/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6250070938487434112748620863079740059331/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (6266823720576962307101853325658351251219/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6266823720576962307101853325658351251219/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (250337893181287928397009483774761826211/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (250337893181287928397009483774761826211/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1046 BracketBatch0065.bracket1047 (250337893181287928397009483774761826211/400000000000000000000000000000000000000) (13775666594248292837931309211926573693/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1046 BracketBatch0065.bracket1047
  (250337893181287928397009483774761826211/400000000000000000000000000000000000000) (13775666594248292837931309211926573693/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1046
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1047
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (391676482536060144193865832853646953201/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (391676482536060144193865832853646953201/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0163.rows BesselBatch0163.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (785452170549894709679100900208857989743/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (785452170549894709679100900208857989743/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0570.rows BesselBatch0570.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (313761027124402999613366513183230379229/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (313761027124402999613366513183230379229/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0130.rows ScalarLogs0130.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0065.bracket1047 BracketBatch0065.bracket1048 (313761027124402999613366513183230379229/500000000000000000000000000000000000000) (17360608260922515099487280144096117311/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0065.bracket1047 BracketBatch0065.bracket1048
  (313761027124402999613366513183230379229/500000000000000000000000000000000000000) (17360608260922515099487280144096117311/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1047
