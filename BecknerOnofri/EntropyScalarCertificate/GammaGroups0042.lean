module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0052
public import BecknerOnofri.EntropyScalarCertificate.Bessel0053
public import BecknerOnofri.EntropyScalarCertificate.Bessel0515
public import BecknerOnofri.EntropyScalarCertificate.Brackets0021
public import BecknerOnofri.EntropyScalarCertificate.Logs0042
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0336
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1246586557463228740675735919338089513273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1246586557463228740675735919338089513273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1248633535896855393138070108314390355809/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1248633535896855393138070108314390355809/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1247610046680042066906903013826239934541/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1247610046680042066906903013826239934541/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0336 BracketBatch0021.bracket0337 (1247610046680042066906903013826239934541/10000000000000000000000000000000000000000) (91560704460689696027372865133949117/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0336 BracketBatch0021.bracket0337
  (1247610046680042066906903013826239934541/10000000000000000000000000000000000000000) (91560704460689696027372865133949117/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0336
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0337
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (624316767948427696569035054157195177903/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (624316767948427696569035054157195177903/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1250680669549963750295495058691202480123/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1250680669549963750295495058691202480123/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (2499314205446819143433565167005592835929/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2499314205446819143433565167005592835929/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0337 BracketBatch0021.bracket0338 (2499314205446819143433565167005592835929/20000000000000000000000000000000000000000) (11519684766777464077343527906782221/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0337 BracketBatch0021.bracket0338
  (2499314205446819143433565167005592835929/20000000000000000000000000000000000000000) (11519684766777464077343527906782221/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0337
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0338
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (31267016738749093757387376467280062003/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31267016738749093757387376467280062003/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (626363979347469063620332551673214466439/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (626363979347469063620332551673214466439/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1251704314122450938768080081018815706499/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1251704314122450938768080081018815706499/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0338 BracketBatch0021.bracket0339 (1251704314122450938768080081018815706499/10000000000000000000000000000000000000000) (18551433403123589765414015586599549/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0338 BracketBatch0021.bracket0339
  (1251704314122450938768080081018815706499/10000000000000000000000000000000000000000) (18551433403123589765414015586599549/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0338
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0339
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0052.rows BesselBatch0052.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (10021823669559505017925320826771431463/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10021823669559505017925320826771431463/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (125477540360427287697751038734534624149/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (125477540360427287697751038734534624149/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (501500672459842200843635098138355034873/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (501500672459842200843635098138355034873/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0339 BracketBatch0021.bracket0340 (501500672459842200843635098138355034873/4000000000000000000000000000000000000000) (93359780672037457623493166006418523/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0339 BracketBatch0021.bracket0340
  (501500672459842200843635098138355034873/4000000000000000000000000000000000000000) (93359780672037457623493166006418523/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0339
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0340
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1254775403604272876977510387345346241487/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1254775403604272876977510387345346241487/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (628411502275286302256141036143917062553/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (628411502275286302256141036143917062553/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (2511598408154845481489792459633180366593/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2511598408154845481489792459633180366593/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0340 BracketBatch0021.bracket0341 (2511598408154845481489792459633180366593/20000000000000000000000000000000000000000) (1503445258992518319696909928622467/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0340 BracketBatch0021.bracket0341
  (2511598408154845481489792459633180366593/20000000000000000000000000000000000000000) (1503445258992518319696909928622467/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0340
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0341
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1256823004550572604512282072287834125103/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1256823004550572604512282072287834125103/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1258870761806552381135581820797854449553/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1258870761806552381135581820797854449553/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (39307715099330077900747873329463883979/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39307715099330077900747873329463883979/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0341 BracketBatch0021.bracket0342 (39307715099330077900747873329463883979/312500000000000000000000000000000000000) (18914764132112573709497650824665947/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0341 BracketBatch0021.bracket0342
  (39307715099330077900747873329463883979/312500000000000000000000000000000000000) (18914764132112573709497650824665947/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0341
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0342
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (25177415236131047622711636415957088991/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25177415236131047622711636415957088991/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1260918675645037958895796431480548298919/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1260918675645037958895796431480548298919/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (2519789437451590340031378252278402748469/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2519789437451590340031378252278402748469/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0342 BracketBatch0021.bracket0343 (2519789437451590340031378252278402748469/20000000000000000000000000000000000000000) (23796316552249948863683228768931661/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0342 BracketBatch0021.bracket0343
  (2519789437451590340031378252278402748469/20000000000000000000000000000000000000000) (23796316552249948863683228768931661/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0342
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0343
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (315229668911259489723949107870137074729/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (315229668911259489723949107870137074729/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0053.rows BesselBatch0053.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (157870843292370748158044888394803050701/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157870843292370748158044888394803050701/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0515.rows BesselBatch0515.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (630971355496000986040038884659743176131/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (630971355496000986040038884659743176131/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0042.rows ScalarLogs0042.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0021.bracket0343 BracketBatch0021.bracket0344 (630971355496000986040038884659743176131/5000000000000000000000000000000000000000) (191599349930259538544231781478159633/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0021.bracket0343 BracketBatch0021.bracket0344
  (630971355496000986040038884659743176131/5000000000000000000000000000000000000000) (191599349930259538544231781478159633/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0343
