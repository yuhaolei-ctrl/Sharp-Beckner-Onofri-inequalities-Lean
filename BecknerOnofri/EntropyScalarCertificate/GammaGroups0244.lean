module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0305
public import BecknerOnofri.EntropyScalarCertificate.Bessel0306
public import BecknerOnofri.EntropyScalarCertificate.Bessel0641
public import BecknerOnofri.EntropyScalarCertificate.Bessel0642
public import BecknerOnofri.EntropyScalarCertificate.Brackets0122
public import BecknerOnofri.EntropyScalarCertificate.Logs0244
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1952
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (10269012267680159850001644019671625493741/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10269012267680159850001644019671625493741/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (10348020164520459986641876896305346741967/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10348020164520459986641876896305346741967/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (5154258108050154959160880228994243058927/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5154258108050154959160880228994243058927/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1952 BracketBatch0122.bracket1953 (5154258108050154959160880228994243058927/1250000000000000000000000000000000000000) (1616733015088167116894447898301593509201/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1952 BracketBatch0122.bracket1953
  (5154258108050154959160880228994243058927/1250000000000000000000000000000000000000) (1616733015088167116894447898301593509201/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1952
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1953
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (8278416131616367989313501517044277393573/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8278416131616367989313501517044277393573/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (41713239681406612236048993359013173638337/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41713239681406612236048993359013173638337/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (41552660169744226091308250472117280303101/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41552660169744226091308250472117280303101/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1953 BracketBatch0122.bracket1954 (41552660169744226091308250472117280303101/10000000000000000000000000000000000000000) (1625973795847194931916291961793239197871/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1953 BracketBatch0122.bracket1954
  (41552660169744226091308250472117280303101/10000000000000000000000000000000000000000) (1625973795847194931916291961793239197871/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1953
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1954
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (20856619840703306118024496679506586819167/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20856619840703306118024496679506586819167/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (10509912733489603102551305609252129453617/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10509912733489603102551305609252129453617/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (41876445307682512323127107898010845726401/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41876445307682512323127107898010845726401/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1954 BracketBatch0122.bracket1955 (41876445307682512323127107898010845726401/10000000000000000000000000000000000000000) (817648728456924990772032730599552219319/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1954 BracketBatch0122.bracket1955
  (41876445307682512323127107898010845726401/10000000000000000000000000000000000000000) (817648728456924990772032730599552219319/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1954
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1955
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (8407930186791682482041044487401703562893/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8407930186791682482041044487401703562893/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (42371443304089517512693909929829187641661/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (42371443304089517512693909929829187641661/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (42205547119023964961449566183418852728063/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42205547119023964961449566183418852728063/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1955 BracketBatch0122.bracket1956 (42205547119023964961449566183418852728063/10000000000000000000000000000000000000000) (41117629786718980093911654535565354903/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1955 BracketBatch0122.bracket1956
  (42205547119023964961449566183418852728063/10000000000000000000000000000000000000000) (41117629786718980093911654535565354903/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1955
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1956
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (21185721652044758756346954964914593820829/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21185721652044758756346954964914593820829/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (42708749944545481096634449552559918391129/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (42708749944545481096634449552559918391129/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (85080193248634998609328359482389106032787/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (85080193248634998609328359482389106032787/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1956 BracketBatch0122.bracket1957 (85080193248634998609328359482389106032787/20000000000000000000000000000000000000000) (1654198218567618742747175948413618330291/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1956 BracketBatch0122.bracket1957
  (85080193248634998609328359482389106032787/20000000000000000000000000000000000000000) (1654198218567618742747175948413618330291/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1956
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1957
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (21354374972272740548317224776279959195563/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21354374972272740548317224776279959195563/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (21525854225112343607230357087487116439667/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21525854225112343607230357087487116439667/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (4288022919738508415554758186376707563523/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4288022919738508415554758186376707563523/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1957 BracketBatch0122.bracket1958 (4288022919738508415554758186376707563523/1000000000000000000000000000000000000000) (166377778381678993281913636257842539133/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1957 BracketBatch0122.bracket1958
  (4288022919738508415554758186376707563523/1000000000000000000000000000000000000000) (166377778381678993281913636257842539133/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1957
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1958
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (43051708450224687214460714174974232879331/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43051708450224687214460714174974232879331/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (10850115261222612791975316401089384851071/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10850115261222612791975316401089384851071/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (17290433899023027676472395955866354456723/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17290433899023027676472395955866354456723/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1958 BracketBatch0122.bracket1959 (17290433899023027676472395955866354456723/4000000000000000000000000000000000000000) (1673445160065026349992845286305597325829/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1958 BracketBatch0122.bracket1959
  (17290433899023027676472395955866354456723/4000000000000000000000000000000000000000) (1673445160065026349992845286305597325829/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1958
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1959
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (43400461044890451167901265604357539404281/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43400461044890451167901265604357539404281/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0306.rows BesselBatch0306.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (43755154777366874868936387771649215257249/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43755154777366874868936387771649215257249/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0642.rows BesselBatch0642.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (8715561582225732603683765337600675466153/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8715561582225732603683765337600675466153/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0244.rows ScalarLogs0244.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0122.bracket1959 BracketBatch0122.bracket1960 (8715561582225732603683765337600675466153/2000000000000000000000000000000000000000) (210400206013919971946335578882739564867/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0122.bracket1959 BracketBatch0122.bracket1960
  (8715561582225732603683765337600675466153/2000000000000000000000000000000000000000) (210400206013919971946335578882739564867/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1959
