module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0478
public import BecknerOnofri.EntropyScalarCertificate.Bessel0479
public import BecknerOnofri.EntropyScalarCertificate.Bessel0480
public import BecknerOnofri.EntropyScalarCertificate.Bessel0728
public import BecknerOnofri.EntropyScalarCertificate.Brackets0191
public import BecknerOnofri.EntropyScalarCertificate.Brackets0192
public import BecknerOnofri.EntropyScalarCertificate.Logs0383
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3064
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (947595938573522918706904966368952175219209/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (947595938573522918706904966368952175219209/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1902393158181084939405666821551773369239757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1902393158181084939405666821551773369239757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (151903401413125231072779070171587108787127/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (151903401413125231072779070171587108787127/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3064 BracketBatch0191.bracket3065 (151903401413125231072779070171587108787127/800000000000000000000000000000000000000) (1773093136702146894065568722899536106811/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3064 BracketBatch0191.bracket3065
  (151903401413125231072779070171587108787127/800000000000000000000000000000000000000) (1773093136702146894065568722899536106811/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3064
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3065
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0478.rows BesselBatch0478.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (951196579090542469702833410775886684619877/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (951196579090542469702833410775886684619877/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (477412352724587135586216933312572358354079/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (477412352724587135586216933312572358354079/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (381204256907943348175053455480206280265607/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (381204256907943348175053455480206280265607/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3065 BracketBatch0191.bracket3066 (381204256907943348175053455480206280265607/2000000000000000000000000000000000000000) (3549035604558205179674615646857240225427/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3065 BracketBatch0191.bracket3066
  (381204256907943348175053455480206280265607/2000000000000000000000000000000000000000) (3549035604558205179674615646857240225427/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3065
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3066
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1909649410898348542344867733250289433416313/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1909649410898348542344867733250289433416313/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (958480633578630883450930764842969438132393/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (958480633578630883450930764842969438132393/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (3826610678055610309246729262936228309681099/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3826610678055610309246729262936228309681099/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3066 BracketBatch0191.bracket3067 (3826610678055610309246729262936228309681099/20000000000000000000000000000000000000000) (177594723408171502462740483599601301229/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3066 BracketBatch0191.bracket3067
  (3826610678055610309246729262936228309681099/20000000000000000000000000000000000000000) (177594723408171502462740483599601301229/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3066
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3067
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1916961267157261766901861529685938876264783/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1916961267157261766901861529685938876264783/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (481082342134287145491038927978740865920863/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (481082342134287145491038927978740865920863/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (768258127138882069773203448320180467989647/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (768258127138882069773203448320180467989647/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3067 BracketBatch0191.bracket3068 (768258127138882069773203448320180467989647/4000000000000000000000000000000000000000) (3554762914054504092228272977207701299839/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3067 BracketBatch0191.bracket3068
  (768258127138882069773203448320180467989647/4000000000000000000000000000000000000000) (3554762914054504092228272977207701299839/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3067
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3068
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (1924329368537148581964155711914963463683449/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1924329368537148581964155711914963463683449/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (24146929581573674307040758328530782124273/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24146929581573674307040758328530782124273/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (3856083735063042526527416378197426033625289/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3856083735063042526527416378197426033625289/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3068 BracketBatch0191.bracket3069 (3856083735063042526527416378197426033625289/20000000000000000000000000000000000000000) (7115281984402514123381702606865645715631/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3068 BracketBatch0191.bracket3069
  (3856083735063042526527416378197426033625289/20000000000000000000000000000000000000000) (7115281984402514123381702606865645715631/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3068
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3069
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1931754366525893944563260666282462569941837/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1931754366525893944563260666282462569941837/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (969618461355985087806944216360849195299791/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (969618461355985087806944216360849195299791/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (3870991289237864120177149099004160960541419/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3870991289237864120177149099004160960541419/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3069 BracketBatch0191.bracket3070 (3870991289237864120177149099004160960541419/20000000000000000000000000000000000000000) (1780264376350427210983922201619663355531/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3069 BracketBatch0191.bracket3070
  (3870991289237864120177149099004160960541419/20000000000000000000000000000000000000000) (1780264376350427210983922201619663355531/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3069
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3070
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1939236922711970175613888432721698390599579/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1939236922711970175613888432721698390599579/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (973388854490473220850768720698348569956301/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (973388854490473220850768720698348569956301/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (3886014631692916617315425874118395530512181/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3886014631692916617315425874118395530512181/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3070 BracketBatch0191.bracket3071 (3886014631692916617315425874118395530512181/20000000000000000000000000000000000000000) (3563426245769414809457327421556831086387/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3070 BracketBatch0191.bracket3071
  (3886014631692916617315425874118395530512181/20000000000000000000000000000000000000000) (3563426245769414809457327421556831086387/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3070
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3071
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0479.rows BesselBatch0479.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1946777708980946441701537441396697139912599/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1946777708980946441701537441396697139912599/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0480.rows BesselBatch0480.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (78175096308664157113978950860350950379303/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (78175096308664157113978950860350950379303/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0728.rows BesselBatch0728.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1950577558348775184775505606452735449697587/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1950577558348775184775505606452735449697587/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0383.rows ScalarLogs0383.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0191.bracket3071 BracketBatch0192.bracket3072 (1950577558348775184775505606452735449697587/10000000000000000000000000000000000000000) (7132667043466370098965643626678347674193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0191.bracket3071 BracketBatch0192.bracket3072
  (1950577558348775184775505606452735449697587/10000000000000000000000000000000000000000) (7132667043466370098965643626678347674193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3071
