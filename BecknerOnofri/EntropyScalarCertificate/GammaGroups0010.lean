import BecknerOnofri.EntropyScalarCertificate.Bessel0012
import BecknerOnofri.EntropyScalarCertificate.Bessel0013
import BecknerOnofri.EntropyScalarCertificate.Bessel0495
import BecknerOnofri.EntropyScalarCertificate.Brackets0005
import BecknerOnofri.EntropyScalarCertificate.Logs0010
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0080
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (726913778529184639253342642043147971203/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (726913778529184639253342642043147971203/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (728929707390429446026234463331180617537/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (728929707390429446026234463331180617537/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (72792174295980704263978855268716429437/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (72792174295980704263978855268716429437/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0080 BracketBatch0005.bracket0081 (72792174295980704263978855268716429437/1000000000000000000000000000000000000000) (21162354430770850383951208297106107/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0080 BracketBatch0005.bracket0081
  (72792174295980704263978855268716429437/1000000000000000000000000000000000000000) (21162354430770850383951208297106107/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0080
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0081
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (364464853695214723013117231665590308767/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (364464853695214723013117231665590308767/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (730945724786110010105154405974782167693/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (730945724786110010105154405974782167693/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (1459875432176539456131388869305962785227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1459875432176539456131388869305962785227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0081 BracketBatch0005.bracket0082 (1459875432176539456131388869305962785227/20000000000000000000000000000000000000000) (5350391454225715110786012481514763/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0081 BracketBatch0005.bracket0082
  (1459875432176539456131388869305962785227/20000000000000000000000000000000000000000) (5350391454225715110786012481514763/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0081
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0082
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (73094572478611001010515440597478216769/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (73094572478611001010515440597478216769/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (732961830967015230928387831147928277247/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (732961830967015230928387831147928277247/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1463907555753125241033542237122710444937/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1463907555753125241033542237122710444937/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0082 BracketBatch0005.bracket0083 (1463907555753125241033542237122710444937/20000000000000000000000000000000000000000) (2705345511536403773323865637539047/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0082 BracketBatch0005.bracket0083
  (1463907555753125241033542237122710444937/20000000000000000000000000000000000000000) (2705345511536403773323865637539047/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0082
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0083
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0012.rows BesselBatch0012.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (183240457741753807732096957786982069311/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (183240457741753807732096957786982069311/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (183744506545998607293268986005249149611/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (183744506545998607293268986005249149611/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (183492482143876207512682971896115609461/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (183492482143876207512682971896115609461/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0083 BracketBatch0005.bracket0084 (183492482143876207512682971896115609461/2500000000000000000000000000000000000000) (21885960263445691573207969558510257/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0083 BracketBatch0005.bracket0084
  (183492482143876207512682971896115609461/2500000000000000000000000000000000000000) (21885960263445691573207969558510257/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0083
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0084
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (734978026183994429173075944020996598441/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (734978026183994429173075944020996598441/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (736994310687957524322406050807511311987/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (736994310687957524322406050807511311987/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (367993084217987988373870498707126977607/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (367993084217987988373870498707126977607/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0084 BracketBatch0005.bracket0085 (367993084217987988373870498707126977607/5000000000000000000000000000000000000000) (22131165367762949030583368188772137/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0084 BracketBatch0005.bracket0085
  (367993084217987988373870498707126977607/5000000000000000000000000000000000000000) (22131165367762949030583368188772137/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0084
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0085
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (46062144417997345270150378175469456999/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46062144417997345270150378175469456999/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (184752671182468803083081915666827365019/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (184752671182468803083081915666827365019/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (73800249770891636832736685673741038603/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (73800249770891636832736685673741038603/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0085 BracketBatch0005.bracket0086 (73800249770891636832736685673741038603/1000000000000000000000000000000000000000) (22378390473532073926839031681562937/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0085 BracketBatch0005.bracket0086
  (73800249770891636832736685673741038603/1000000000000000000000000000000000000000) (22378390473532073926839031681562937/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0085
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0086
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (739010684729875212332327662667309460073/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (739010684729875212332327662667309460073/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (741027148560779143398101815028060125027/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (741027148560779143398101815028060125027/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (14800378332906543557304294776953695851/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14800378332906543557304294776953695851/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0086 BracketBatch0005.bracket0087 (14800378332906543557304294776953695851/200000000000000000000000000000000000000) (4525529335987982935317677395117273/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0086 BracketBatch0005.bracket0087
  (14800378332906543557304294776953695851/200000000000000000000000000000000000000) (4525529335987982935317677395117273/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0086
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0087
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (23157098392524348231190681719626878907/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23157098392524348231190681719626878907/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (743043702431762099820991270075056497941/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (743043702431762099820991270075056497941/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (296814170198508248643818617020623324593/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (296814170198508248643818617020623324593/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0010.rows ScalarLogs0010.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0087 BracketBatch0005.bracket0088 (296814170198508248643818617020623324593/4000000000000000000000000000000000000000) (11439472558538261244091960617773793/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0087 BracketBatch0005.bracket0088
  (296814170198508248643818617020623324593/4000000000000000000000000000000000000000) (11439472558538261244091960617773793/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0087
