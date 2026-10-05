module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0191
public import BecknerOnofri.EntropyScalarCertificate.Bessel0192
public import BecknerOnofri.EntropyScalarCertificate.Bessel0584
public import BecknerOnofri.EntropyScalarCertificate.Bessel0585
public import BecknerOnofri.EntropyScalarCertificate.Brackets0076
public import BecknerOnofri.EntropyScalarCertificate.Brackets0077
public import BecknerOnofri.EntropyScalarCertificate.Logs0153
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1224
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1025580834007989810747059534045018096289/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1025580834007989810747059534045018096289/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (10287665246755864939323756685803875684497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10287665246755864939323756685803875684497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (20543473586835763046794352026254056647387/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20543473586835763046794352026254056647387/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1224 BracketBatch0076.bracket1225 (20543473586835763046794352026254056647387/20000000000000000000000000000000000000000) (255554951480301842868585505494889983559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1224 BracketBatch0076.bracket1225
  (20543473586835763046794352026254056647387/20000000000000000000000000000000000000000) (255554951480301842868585505494889983559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1224
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1225
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (5143832623377932469661878342901937842247/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5143832623377932469661878342901937842247/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (2579923040462175290606761654101859667663/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2579923040462175290606761654101859667663/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (10303678704302283050875401651105657177573/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10303678704302283050875401651105657177573/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1225 BracketBatch0076.bracket1226 (10303678704302283050875401651105657177573/10000000000000000000000000000000000000000) (64329426806185306980349492414880969053/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1225 BracketBatch0076.bracket1226
  (10303678704302283050875401651105657177573/10000000000000000000000000000000000000000) (64329426806185306980349492414880969053/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1225
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1226
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (10319692161848701162427046616407438670649/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10319692161848701162427046616407438670649/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (5175945446798040395689598624367046319447/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5175945446798040395689598624367046319447/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (20671583055444781953806243865141531309543/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20671583055444781953806243865141531309543/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1226 BracketBatch0076.bracket1227 (20671583055444781953806243865141531309543/20000000000000000000000000000000000000000) (259092175811063222399280889780686962391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1226 BracketBatch0076.bracket1227
  (20671583055444781953806243865141531309543/20000000000000000000000000000000000000000) (259092175811063222399280889780686962391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1226
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1227
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (10351890893596080791379197248734092638891/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10351890893596080791379197248734092638891/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (10384263276726019717439876726336819356183/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10384263276726019717439876726336819356183/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (10368077085161050254409536987535455997537/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10368077085161050254409536987535455997537/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1227 BracketBatch0076.bracket1228 (10368077085161050254409536987535455997537/10000000000000000000000000000000000000000) (260878452009138703722607953528104897897/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1227 BracketBatch0076.bracket1228
  (10368077085161050254409536987535455997537/10000000000000000000000000000000000000000) (260878452009138703722607953528104897897/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1227
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1228
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0191.rows BesselBatch0191.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (519213163836300985871993836316840967809/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (519213163836300985871993836316840967809/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (2604202793236843548366712804682159965167/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2604202793236843548366712804682159965167/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1300067153104587119431670496566591201053/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1300067153104587119431670496566591201053/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1228 BracketBatch0076.bracket1229 (1300067153104587119431670496566591201053/1250000000000000000000000000000000000000) (65669157936566683242299041212388640481/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1228 BracketBatch0076.bracket1229
  (1300067153104587119431670496566591201053/1250000000000000000000000000000000000000) (65669157936566683242299041212388640481/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1228
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1229
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2083362234589474838693370243745727972133/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2083362234589474838693370243745727972133/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (2612384117862793202258911381148459031703/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2612384117862793202258911381148459031703/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0584.rows BesselBatch0584.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (20866347644398547002502496743322475987477/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20866347644398547002502496743322475987477/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1229 BracketBatch0076.bracket1230 (20866347644398547002502496743322475987477/20000000000000000000000000000000000000000) (66121703031679667742002989255288300119/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1229 BracketBatch0076.bracket1230
  (20866347644398547002502496743322475987477/20000000000000000000000000000000000000000) (66121703031679667742002989255288300119/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1229
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1230
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (10449536471451172809035645524593836126809/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10449536471451172809035645524593836126809/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2620610272355764326539209969505275180753/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2620610272355764326539209969505275180753/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (20931977560874230115192485402614936849821/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20931977560874230115192485402614936849821/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1230 BracketBatch0076.bracket1231 (20931977560874230115192485402614936849821/20000000000000000000000000000000000000000) (53261818290334678833179898935538044433/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1230 BracketBatch0076.bracket1231
  (20931977560874230115192485402614936849821/20000000000000000000000000000000000000000) (53261818290334678833179898935538044433/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1230
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1231
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (10482441089423057306156839878021100723009/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10482441089423057306156839878021100723009/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0192.rows BesselBatch0192.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2628881743141778858910247348909270674303/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2628881743141778858910247348909270674303/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0585.rows BesselBatch0585.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (20997968061990172741797829273658183420221/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20997968061990172741797829273658183420221/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0153.rows ScalarLogs0153.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0076.bracket1231 BracketBatch0077.bracket1232 (20997968061990172741797829273658183420221/20000000000000000000000000000000000000000) (134071784619776108972744793718725097279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0076.bracket1231 BracketBatch0077.bracket1232
  (20997968061990172741797829273658183420221/20000000000000000000000000000000000000000) (134071784619776108972744793718725097279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1231
