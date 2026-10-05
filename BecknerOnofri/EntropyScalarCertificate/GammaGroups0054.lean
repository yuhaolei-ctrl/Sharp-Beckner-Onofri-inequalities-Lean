module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0067
public import BecknerOnofri.EntropyScalarCertificate.Bessel0068
public import BecknerOnofri.EntropyScalarCertificate.Bessel0522
public import BecknerOnofri.EntropyScalarCertificate.Bessel0523
public import BecknerOnofri.EntropyScalarCertificate.Brackets0027
public import BecknerOnofri.EntropyScalarCertificate.Logs0054
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0432
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (360960896252176763653163460757913163013/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (360960896252176763653163460757913163013/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (144590672303054424335072331449718363881/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (144590672303054424335072331449718363881/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (1444875154019625648981688578764418145431/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1444875154019625648981688578764418145431/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0432 BracketBatch0027.bracket0433 (1444875154019625648981688578764418145431/10000000000000000000000000000000000000000) (6542642742403553600407551713003549/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0432 BracketBatch0027.bracket0433
  (1444875154019625648981688578764418145431/10000000000000000000000000000000000000000) (6542642742403553600407551713003549/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0432
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0433
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1445906723030544243350723314497183638807/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1445906723030544243350723314497183638807/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1447970042953780343687373507862537682751/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1447970042953780343687373507862537682751/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1446938382992162293519048411179860660779/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1446938382992162293519048411179860660779/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0433 BracketBatch0027.bracket0434 (1446938382992162293519048411179860660779/10000000000000000000000000000000000000000) (328977376937282509043503677561673023/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0433 BracketBatch0027.bracket0434
  (1446938382992162293519048411179860660779/10000000000000000000000000000000000000000) (328977376937282509043503677561673023/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0433
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0434
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (361992510738445085921843376965634420687/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (361992510738445085921843376965634420687/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1450033545062368290217710689947484356523/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1450033545062368290217710689947484356523/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (2898003588016148633905084197810022039271/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2898003588016148633905084197810022039271/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0434 BracketBatch0027.bracket0435 (2898003588016148633905084197810022039271/20000000000000000000000000000000000000000) (6616608701774048078558835226309559/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0434 BracketBatch0027.bracket0435
  (2898003588016148633905084197810022039271/20000000000000000000000000000000000000000) (6616608701774048078558835226309559/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0434
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0435
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0067.rows BesselBatch0067.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (36250838626559207255442767248687108913/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36250838626559207255442767248687108913/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (363024307410098135335658961222276088869/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (363024307410098135335658961222276088869/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (725532693675690207890086633709147177999/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (725532693675690207890086633709147177999/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0435 BracketBatch0027.bracket0436 (725532693675690207890086633709147177999/5000000000000000000000000000000000000000) (332691333904633821682525912398753079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0435 BracketBatch0027.bracket0436
  (725532693675690207890086633709147177999/5000000000000000000000000000000000000000) (332691333904633821682525912398753079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0435
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0436
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1452097229640392541342635844889104355473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1452097229640392541342635844889104355473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1454161096972069313706383432088147687421/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1454161096972069313706383432088147687421/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1453129163306230927524509638488626021447/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1453129163306230927524509638488626021447/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0436 BracketBatch0027.bracket0437 (1453129163306230927524509638488626021447/10000000000000000000000000000000000000000) (334560095749091774111722716863577427/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0436 BracketBatch0027.bracket0437
  (1453129163306230927524509638488626021447/10000000000000000000000000000000000000000) (334560095749091774111722716863577427/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0436
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0437
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (727080548486034656853191716044073843709/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (727080548486034656853191716044073843709/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1456225147341746816868472190291890839517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1456225147341746816868472190291890839517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (582077248862763226114971124476007705387/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (582077248862763226114971124476007705387/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0437 BracketBatch0027.bracket0438 (582077248862763226114971124476007705387/4000000000000000000000000000000000000000) (84109185754980336719789139978455337/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0437 BracketBatch0027.bracket0438
  (582077248862763226114971124476007705387/4000000000000000000000000000000000000000) (84109185754980336719789139978455337/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0437
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0438
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (728112573670873408434236095145945419757/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (728112573670873408434236095145945419757/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1458289381033905488210555166845814885139/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1458289381033905488210555166845814885139/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (2914514528375652305079027357137705724653/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2914514528375652305079027357137705724653/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0438 BracketBatch0027.bracket0439 (2914514528375652305079027357137705724653/20000000000000000000000000000000000000000) (67664259629761847663161631916398971/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0438 BracketBatch0027.bracket0439
  (2914514528375652305079027357137705724653/20000000000000000000000000000000000000000) (67664259629761847663161631916398971/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0438
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0439
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (91143086314619093013159697927863430321/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (91143086314619093013159697927863430321/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0068.rows BesselBatch0068.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1460353798333158228078656927318122861063/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1460353798333158228078656927318122861063/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0523.rows BesselBatch0523.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2918643179367063716289212094163937746199/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2918643179367063716289212094163937746199/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0054.rows ScalarLogs0054.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0027.bracket0439 BracketBatch0027.bracket0440 (2918643179367063716289212094163937746199/20000000000000000000000000000000000000000) (340213783601295317989842713814692257/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0027.bracket0439 BracketBatch0027.bracket0440
  (2918643179367063716289212094163937746199/20000000000000000000000000000000000000000) (340213783601295317989842713814692257/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0439
