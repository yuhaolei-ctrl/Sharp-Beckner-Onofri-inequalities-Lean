module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0042
public import BecknerOnofri.EntropyScalarCertificate.Bessel0043
public import BecknerOnofri.EntropyScalarCertificate.Bessel0510
public import BecknerOnofri.EntropyScalarCertificate.Brackets0017
public import BecknerOnofri.EntropyScalarCertificate.Logs0034
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0272
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (557945206029676227916101347222695733803/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (557945206029676227916101347222695733803/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (558964009066172987536614061612950414251/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (558964009066172987536614061612950414251/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (558454607547924607726357704417823074027/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (558454607547924607726357704417823074027/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0272 BracketBatch0017.bracket0273 (558454607547924607726357704417823074027/5000000000000000000000000000000000000000) (14751387614594492550005001034387161/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0272 BracketBatch0017.bracket0273
  (558454607547924607726357704417823074027/5000000000000000000000000000000000000000) (14751387614594492550005001034387161/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0272
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0273
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1117928018132345975073228123225900828499/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1117928018132345975073228123225900828499/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (22399315244228983046745312512445995097/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22399315244228983046745312512445995097/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (2237893780343795127410493748848200583349/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2237893780343795127410493748848200583349/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0273 BracketBatch0017.bracket0274 (2237893780343795127410493748848200583349/20000000000000000000000000000000000000000) (59434903614196474508984627668673109/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0273 BracketBatch0017.bracket0274
  (2237893780343795127410493748848200583349/20000000000000000000000000000000000000000) (59434903614196474508984627668673109/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0273
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0274
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1119965762211449152337265625622299754847/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1119965762211449152337265625622299754847/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (561001822281220381356942384808666547637/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (561001822281220381356942384808666547637/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (2241969406773889915051150395239632850121/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2241969406773889915051150395239632850121/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0274 BracketBatch0017.bracket0275 (2241969406773889915051150395239632850121/20000000000000000000000000000000000000000) (119733187158879504016543010049494219/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0274 BracketBatch0017.bracket0275
  (2241969406773889915051150395239632850121/20000000000000000000000000000000000000000) (119733187158879504016543010049494219/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0274
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0275
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0042.rows BesselBatch0042.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1122003644562440762713884769617333095271/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1122003644562440762713884769617333095271/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (224808333090239259163813496991624481149/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (224808333090239259163813496991624481149/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (280755663751704632316619031821931937627/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (280755663751704632316619031821931937627/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0275 BracketBatch0017.bracket0276 (280755663751704632316619031821931937627/2500000000000000000000000000000000000000) (120601257762525081373188321020674421/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0275 BracketBatch0017.bracket0276
  (280755663751704632316619031821931937627/2500000000000000000000000000000000000000) (120601257762525081373188321020674421/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0275
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0276
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (562020832725598147909533742479061202871/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (562020832725598147909533742479061202871/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1126079825143688158511792280061261441029/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1126079825143688158511792280061261441029/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2250121490594884454330859765019383846771/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2250121490594884454330859765019383846771/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0276 BracketBatch0017.bracket0277 (2250121490594884454330859765019383846771/20000000000000000000000000000000000000000) (121474036125858132932582080098351887/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0276 BracketBatch0017.bracket0277
  (2250121490594884454330859765019383846771/20000000000000000000000000000000000000000) (121474036125858132932582080098351887/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0276
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0277
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (563039912571844079255896140030630720513/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (563039912571844079255896140030630720513/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (282029530976496469443968193715538617683/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (282029530976496469443968193715538617683/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1127098974524837018143832527461707955879/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1127098974524837018143832527461707955879/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0277 BracketBatch0017.bracket0278 (1127098974524837018143832527461707955879/10000000000000000000000000000000000000000) (30587884841908660400924497270833739/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0277 BracketBatch0017.bracket0278
  (1127098974524837018143832527461707955879/10000000000000000000000000000000000000000) (30587884841908660400924497270833739/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0277
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0278
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (1128118123905985877775872774862154470729/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1128118123905985877775872774862154470729/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1130156562004256303767435290648465739607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1130156562004256303767435290648465739607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (70571083934695068173228377047206881573/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (70571083934695068173228377047206881573/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0278 BracketBatch0017.bracket0279 (70571083934695068173228377047206881573/625000000000000000000000000000000000000) (61616892319423347004116506365655397/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0278 BracketBatch0017.bracket0279
  (70571083934695068173228377047206881573/625000000000000000000000000000000000000) (61616892319423347004116506365655397/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0278
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0279
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (282539140501064075941858822662116434901/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (282539140501064075941858822662116434901/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0043.rows BesselBatch0043.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1132195139704763813028420757866332780007/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1132195139704763813028420757866332780007/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0510.rows BesselBatch0510.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (2262351701709020116795856048514798519611/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2262351701709020116795856048514798519611/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0034.rows ScalarLogs0034.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0017.bracket0279 BracketBatch0017.bracket0280 (2262351701709020116795856048514798519611/20000000000000000000000000000000000000000) (124120789122731070592355575740004417/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0017.bracket0279 BracketBatch0017.bracket0280
  (2262351701709020116795856048514798519611/20000000000000000000000000000000000000000) (124120789122731070592355575740004417/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0279
