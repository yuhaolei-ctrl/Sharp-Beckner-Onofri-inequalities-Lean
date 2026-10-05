module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0053
public import BecknerOnofri.EntropyScalarCertificate.Bessel0054
public import BecknerOnofri.EntropyScalarCertificate.Bessel0055
public import BecknerOnofri.EntropyScalarCertificate.Bessel0515
public import BecknerOnofri.EntropyScalarCertificate.Bessel0516
public import BecknerOnofri.EntropyScalarCertificate.Brackets0021
public import BecknerOnofri.EntropyScalarCertificate.Brackets0022
public import BecknerOnofri.EntropyScalarCertificate.Logs0043
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0344
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (252593349267793197052871821431684881121/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (252593349267793197052871821431684881121/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (316253743540346054498314863306481084489/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (316253743540346054498314863306481084489/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (2527981720500350203257618560384348743561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2527981720500350203257618560384348743561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0344 BracketBatch0021.bracket0345 (2527981720500350203257618560384348743561/20000000000000000000000000000000000000000) (96417056578159936110050691304610413/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0344 BracketBatch0021.bracket0345
  (2527981720500350203257618560384348743561/20000000000000000000000000000000000000000) (96417056578159936110050691304610413/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0344
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0345
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1265014974161384217993259453225924337953/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1265014974161384217993259453225924337953/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (316765839846362935041306229633576995667/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (316765839846362935041306229633576995667/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (2532078333546835958158484371760232320621/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2532078333546835958158484371760232320621/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0345 BracketBatch0021.bracket0346 (2532078333546835958158484371760232320621/20000000000000000000000000000000000000000) (24259355178430719970307341322034901/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0345 BracketBatch0021.bracket0346
  (2532078333546835958158484371760232320621/20000000000000000000000000000000000000000) (24259355178430719970307341322034901/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0345
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0346
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (253412671877090348033044983706861596533/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (253412671877090348033044983706861596533/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (6345559511422195877184985041697270949/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6345559511422195877184985041697270949/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (507235052333978183120444385374752434493/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (507235052333978183120444385374752434493/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0346 BracketBatch0021.bracket0347 (507235052333978183120444385374752434493/4000000000000000000000000000000000000000) (195321554107763033452484026499486779/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0346 BracketBatch0021.bracket0347
  (507235052333978183120444385374752434493/4000000000000000000000000000000000000000) (195321554107763033452484026499486779/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0346
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0347
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1269111902284439175436997008339454189797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1269111902284439175436997008339454189797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1271160603131728903476126217516972224081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1271160603131728903476126217516972224081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1270136252708084039456561612928213206939/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1270136252708084039456561612928213206939/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0347 BracketBatch0021.bracket0348 (1270136252708084039456561612928213206939/10000000000000000000000000000000000000000) (196574270594267997221179093391823623/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0347 BracketBatch0021.bracket0348
  (1270136252708084039456561612928213206939/10000000000000000000000000000000000000000) (196574270594267997221179093391823623/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0347
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0348
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (635580301565864451738063108758486112039/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (635580301565864451738063108758486112039/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1273209462200815275591710252475135207159/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1273209462200815275591710252475135207159/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (2544370065332544179067836469992107431237/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2544370065332544179067836469992107431237/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0348 BracketBatch0021.bracket0349 (2544370065332544179067836469992107431237/20000000000000000000000000000000000000000) (39566602063367450440027398441329409/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0348 BracketBatch0021.bracket0349
  (2544370065332544179067836469992107431237/20000000000000000000000000000000000000000) (39566602063367450440027398441329409/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0348
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0349
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (318302365550203818897927563118783801789/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (318302365550203818897927563118783801789/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (79703654985331551909968795748734465553/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79703654985331551909968795748734465553/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (637116985491530026537802746113721664001/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (637116985491530026537802746113721664001/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0349 BracketBatch0021.bracket0350 (637116985491530026537802746113721664001/5000000000000000000000000000000000000000) (199097792738237540643044965171765209/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0349 BracketBatch0021.bracket0350
  (637116985491530026537802746113721664001/5000000000000000000000000000000000000000) (199097792738237540643044965171765209/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0349
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0350
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (255051695953060966111900146395950289769/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (255051695953060966111900146395950289769/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (319326914024729127660451045112341743241/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (319326914024729127660451045112341743241/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (2552566135864221341201304912429118421809/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2552566135864221341201304912429118421809/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0350 BracketBatch0021.bracket0351 (2552566135864221341201304912429118421809/20000000000000000000000000000000000000000) (20036863735413560823194001630020653/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0350 BracketBatch0021.bracket0351
  (2552566135864221341201304912429118421809/20000000000000000000000000000000000000000) (20036863735413560823194001630020653/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0350
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0351
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0054.rows BesselBatch0054.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1277307656098916510641804180449366972961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1277307656098916510641804180449366972961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (639678495737740938901301876093667651269/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (639678495737740938901301876093667651269/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (2556664647574398388444407932636702275499/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2556664647574398388444407932636702275499/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0043.rows ScalarLogs0043.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0351 BracketBatch0022.bracket0352 (2556664647574398388444407932636702275499/20000000000000000000000000000000000000000) (201645563693108084782267554805774657/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0351 BracketBatch0022.bracket0352
  (2556664647574398388444407932636702275499/20000000000000000000000000000000000000000) (201645563693108084782267554805774657/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0351
