module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0361
public import BecknerOnofri.EntropyScalarCertificate.Bessel0362
public import BecknerOnofri.EntropyScalarCertificate.Bessel0669
public import BecknerOnofri.EntropyScalarCertificate.Bessel0670
public import BecknerOnofri.EntropyScalarCertificate.Brackets0144
public import BecknerOnofri.EntropyScalarCertificate.Brackets0145
public import BecknerOnofri.EntropyScalarCertificate.Logs0289
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2312
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (75942456453221201123095734958076142377023/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (75942456453221201123095734958076142377023/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1222379601313833090622311951502141489391/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1222379601313833090622311951502141489391/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (304682363070671538573980463853919970927921/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (304682363070671538573980463853919970927921/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2312 BracketBatch0144.bracket2313 (304682363070671538573980463853919970927921/20000000000000000000000000000000000000000) (3321993380012416593685241579626891667023/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2312 BracketBatch0144.bracket2313
  (304682363070671538573980463853919970927921/20000000000000000000000000000000000000000) (3321993380012416593685241579626891667023/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2312
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2313
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (9549840635264321020486812121110480385867/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9549840635264321020486812121110480385867/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (3074422370695969844140540002768536581369/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3074422370695969844140540002768536581369/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (153259284349513814267407997038097257621161/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (153259284349513814267407997038097257621161/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2313 BracketBatch0144.bracket2314 (153259284349513814267407997038097257621161/10000000000000000000000000000000000000000) (666006121044710366498352325314896212963/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2313 BracketBatch0144.bracket2314
  (153259284349513814267407997038097257621161/10000000000000000000000000000000000000000) (666006121044710366498352325314896212963/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2313
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2314
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (153721118534798492207027000138426829068447/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (153721118534798492207027000138426829068447/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (154656122883004500329246249582158732390333/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (154656122883004500329246249582158732390333/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (15418862070890149626813662486029278072939/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15418862070890149626813662486029278072939/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2314 BracketBatch0144.bracket2315 (15418862070890149626813662486029278072939/1000000000000000000000000000000000000000) (1669058395397921268076261977295332771641/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2314 BracketBatch0144.bracket2315
  (15418862070890149626813662486029278072939/1000000000000000000000000000000000000000) (1669058395397921268076261977295332771641/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2314
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2315
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (15465612288300450032924624958215873239033/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15465612288300450032924624958215873239033/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (38900668283024171803727098722274224140411/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (38900668283024171803727098722274224140411/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (155129398007550593772077322235627814475987/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (155129398007550593772077322235627814475987/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2315 BracketBatch0144.bracket2316 (155129398007550593772077322235627814475987/10000000000000000000000000000000000000000) (1673126223305862029994185966796354853799/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2315 BracketBatch0144.bracket2316
  (155129398007550593772077322235627814475987/10000000000000000000000000000000000000000) (1673126223305862029994185966796354853799/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2315
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2316
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0361.rows BesselBatch0361.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (155602673132096687214908394889096896561641/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (155602673132096687214908394889096896561641/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (156560984420813090670985669429333981403511/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (156560984420813090670985669429333981403511/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (9755114298528430558934189509950964936411/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9755114298528430558934189509950964936411/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2316 BracketBatch0144.bracket2317 (9755114298528430558934189509950964936411/625000000000000000000000000000000000000) (1677219044302211803367527514872879135207/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2316 BracketBatch0144.bracket2317
  (9755114298528430558934189509950964936411/625000000000000000000000000000000000000) (1677219044302211803367527514872879135207/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2316
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2317
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (39140246105203272667746417357333495350877/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39140246105203272667746417357333495350877/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (157531277266364263133854303073934128656461/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157531277266364263133854303073934128656461/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0669.rows BesselBatch0669.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (314092261687177353804839972503268110059969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (314092261687177353804839972503268110059969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2317 BracketBatch0144.bracket2318 (314092261687177353804839972503268110059969/20000000000000000000000000000000000000000) (3362674238772838744702325958369648396891/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2317 BracketBatch0144.bracket2318
  (314092261687177353804839972503268110059969/20000000000000000000000000000000000000000) (3362674238772838744702325958369648396891/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2317
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2318
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (78765638633182131566927151536967064328229/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (78765638633182131566927151536967064328229/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (79256888866783807411005555473101255539607/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79256888866783807411005555473101255539607/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (39505631874991484744483176752517079966959/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39505631874991484744483176752517079966959/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2318 BracketBatch0144.bracket2319 (39505631874991484744483176752517079966959/2500000000000000000000000000000000000000) (842740356297674471252207784118458048167/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2318 BracketBatch0144.bracket2319
  (39505631874991484744483176752517079966959/2500000000000000000000000000000000000000) (842740356297674471252207784118458048167/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2318
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2319
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (158513777733567614822011110946202511079211/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (158513777733567614822011110946202511079211/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0362.rows BesselBatch0362.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (159508717610404580107484613455763521298521/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (159508717610404580107484613455763521298521/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0670.rows BesselBatch0670.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (79505623835993048732373931100491508094433/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (79505623835993048732373931100491508094433/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0289.rows ScalarLogs0289.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0144.bracket2319 BracketBatch0145.bracket2320 (79505623835993048732373931100491508094433/5000000000000000000000000000000000000000) (1689650091004732050740395138517643125997/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0144.bracket2319 BracketBatch0145.bracket2320
  (79505623835993048732373931100491508094433/5000000000000000000000000000000000000000) (1689650091004732050740395138517643125997/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2319
