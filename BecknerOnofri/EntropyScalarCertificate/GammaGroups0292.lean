import BecknerOnofri.EntropyScalarCertificate.Bessel0365
import BecknerOnofri.EntropyScalarCertificate.Bessel0366
import BecknerOnofri.EntropyScalarCertificate.Bessel0671
import BecknerOnofri.EntropyScalarCertificate.Bessel0672
import BecknerOnofri.EntropyScalarCertificate.Brackets0146
import BecknerOnofri.EntropyScalarCertificate.Logs0292
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2336
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (22166745211283757426778370513437897631479/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22166745211283757426778370513437897631479/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (178582386284804767095483723469813859143769/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (178582386284804767095483723469813859143769/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (355916347975074826509710687577317040195601/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (355916347975074826509710687577317040195601/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2336 BracketBatch0146.bracket2337 (355916347975074826509710687577317040195601/20000000000000000000000000000000000000000) (705899156431501997450079354138099446857/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2336 BracketBatch0146.bracket2337
  (355916347975074826509710687577317040195601/20000000000000000000000000000000000000000) (705899156431501997450079354138099446857/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2336
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2337
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (89291193142402383547741861734906929571883/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89291193142402383547741861734906929571883/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (179848648511732508800106939974476730061661/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (179848648511732508800106939974476730061661/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (358431034796537275895590663444290589205427/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (358431034796537275895590663444290589205427/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2337 BracketBatch0146.bracket2338 (358431034796537275895590663444290589205427/20000000000000000000000000000000000000000) (221178803445377010477519004137456916979/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2337 BracketBatch0146.bracket2338
  (358431034796537275895590663444290589205427/20000000000000000000000000000000000000000) (221178803445377010477519004137456916979/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2337
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2338
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (89924324255866254400053469987238365030829/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89924324255866254400053469987238365030829/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1132082083458705260852377448876663562869/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1132082083458705260852377448876663562869/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (180490890932562675268243665897371450060349/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (180490890932562675268243665897371450060349/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2338 BracketBatch0146.bracket2339 (180490890932562675268243665897371450060349/10000000000000000000000000000000000000000) (1774144367444920622751285067133290536607/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2338 BracketBatch0146.bracket2339
  (180490890932562675268243665897371450060349/10000000000000000000000000000000000000000) (1774144367444920622751285067133290536607/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2338
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2339
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (181133133353392841736380391820266170059037/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (181133133353392841736380391820266170059037/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (91218118475519061141809860183878735395761/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91218118475519061141809860183878735395761/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (363569370304430964020000112188023640850559/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (363569370304430964020000112188023640850559/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2339 BracketBatch0146.bracket2340 (363569370304430964020000112188023640850559/20000000000000000000000000000000000000000) (355778006094822547218506965877405898639/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2339 BracketBatch0146.bracket2340
  (363569370304430964020000112188023640850559/20000000000000000000000000000000000000000) (355778006094822547218506965877405898639/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2339
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2340
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (182436236951038122283619720367757470791519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (182436236951038122283619720367757470791519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (183758367012093083959903489604403582240997/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (183758367012093083959903489604403582240997/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (91548650990782801560880802493040263258129/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (91548650990782801560880802493040263258129/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2340 BracketBatch0146.bracket2341 (91548650990782801560880802493040263258129/5000000000000000000000000000000000000000) (1783667737943504342441748626537973921959/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2340 BracketBatch0146.bracket2341
  (91548650990782801560880802493040263258129/5000000000000000000000000000000000000000) (1783667737943504342441748626537973921959/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2340
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2341
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (91879183506046541979951744802201791120497/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (91879183506046541979951744802201791120497/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (46274985808845437443252717412365740910303/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46274985808845437443252717412365740910303/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (184429155123737416866457179626933272941103/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (184429155123737416866457179626933272941103/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2341 BracketBatch0146.bracket2342 (184429155123737416866457179626933272941103/10000000000000000000000000000000000000000) (357695562496706486926451002203421921153/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2341 BracketBatch0146.bracket2342
  (184429155123737416866457179626933272941103/10000000000000000000000000000000000000000) (357695562496706486926451002203421921153/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2341
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2342
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0365.rows BesselBatch0365.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (185099943235381749773010869649462963641209/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (185099943235381749773010869649462963641209/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (46615349438813329628693709786045247232481/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46615349438813329628693709786045247232481/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (371561340990635068287785708793643952571133/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (371561340990635068287785708793643952571133/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2342 BracketBatch0146.bracket2343 (371561340990635068287785708793643952571133/20000000000000000000000000000000000000000) (1793320577835356352013378667510672480841/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2342 BracketBatch0146.bracket2343
  (371561340990635068287785708793643952571133/20000000000000000000000000000000000000000) (1793320577835356352013378667510672480841/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2342
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2343
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (186461397755253318514774839144180988929921/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (186461397755253318514774839144180988929921/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0366.rows BesselBatch0366.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (4696079390139857120782866751988314789433/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4696079390139857120782866751988314789433/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0671.rows BesselBatch0671.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0672.rows BesselBatch0672.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (374304573360847603346089509223713580507241/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (374304573360847603346089509223713580507241/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0292.rows ScalarLogs0292.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0146.bracket2343 BracketBatch0146.bracket2344 (374304573360847603346089509223713580507241/20000000000000000000000000000000000000000) (1798196358601224819792319519280255096527/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0146.bracket2343 BracketBatch0146.bracket2344
  (374304573360847603346089509223713580507241/20000000000000000000000000000000000000000) (1798196358601224819792319519280255096527/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2343
