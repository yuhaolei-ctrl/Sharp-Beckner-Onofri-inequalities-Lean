module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0221
public import BecknerOnofri.EntropyScalarCertificate.Bessel0222
public import BecknerOnofri.EntropyScalarCertificate.Bessel0599
public import BecknerOnofri.EntropyScalarCertificate.Bessel0600
public import BecknerOnofri.EntropyScalarCertificate.Brackets0088
public import BecknerOnofri.EntropyScalarCertificate.Brackets0089
public import BecknerOnofri.EntropyScalarCertificate.Logs0177
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1416
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (16831235291723280112983485421921399592421/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16831235291723280112983485421921399592421/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (526249987643234321402134544249740943719/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (526249987643234321402134544249740943719/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (33671234896306778397851790837913109791429/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33671234896306778397851790837913109791429/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1416 BracketBatch0088.bracket1417 (33671234896306778397851790837913109791429/20000000000000000000000000000000000000000) (632701766873967327417329991264012050951/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1416 BracketBatch0088.bracket1417
  (33671234896306778397851790837913109791429/20000000000000000000000000000000000000000) (632701766873967327417329991264012050951/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1416
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1417
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3367999920916699656973661083198342039801/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3367999920916699656973661083198342039801/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (4212193576225137938324790476543534629737/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4212193576225137938324790476543534629737/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (33688773909484050038167467322165848717953/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33688773909484050038167467322165848717953/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1417 BracketBatch0088.bracket1418 (33688773909484050038167467322165848717953/20000000000000000000000000000000000000000) (633186173933389221009141022952844473053/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1417 BracketBatch0088.bracket1418
  (33688773909484050038167467322165848717953/20000000000000000000000000000000000000000) (633186173933389221009141022952844473053/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1417
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1418
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (3369754860980110350659832381234827703789/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3369754860980110350659832381234827703789/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (16857559412791484906043690029097946360811/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16857559412791484906043690029097946360811/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (8426583429423009164835712983818021219939/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8426583429423009164835712983818021219939/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1418 BracketBatch0088.bracket1419 (8426583429423009164835712983818021219939/5000000000000000000000000000000000000000) (316835531656546154648995095903149578223/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1418 BracketBatch0088.bracket1419
  (8426583429423009164835712983818021219939/5000000000000000000000000000000000000000) (316835531656546154648995095903149578223/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1418
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1419
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (2107194926598935613255461253637243295101/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2107194926598935613255461253637243295101/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (16866354948423512563511806025500268717111/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16866354948423512563511806025500268717111/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (33723914361214997469555496054598215077919/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33723914361214997469555496054598215077919/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1419 BracketBatch0088.bracket1420 (33723914361214997469555496054598215077919/20000000000000000000000000000000000000000) (158539108930128225300883182219844871541/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1419 BracketBatch0088.bracket1420
  (33723914361214997469555496054598215077919/20000000000000000000000000000000000000000) (158539108930128225300883182219844871541/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1419
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1420
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0221.rows BesselBatch0221.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (4216588737105878140877951506375067179277/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4216588737105878140877951506375067179277/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (1687516093201416935356913838388342086031/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1687516093201416935356913838388342086031/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (16870757940218840958540472204691844788709/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16870757940218840958540472204691844788709/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1420 BracketBatch0088.bracket1421 (16870757940218840958540472204691844788709/10000000000000000000000000000000000000000) (31732114593220157472131670921834902313/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1420 BracketBatch0088.bracket1421
  (16870757940218840958540472204691844788709/10000000000000000000000000000000000000000) (31732114593220157472131670921834902313/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1420
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1421
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (16875160932014169353569138383883420860307/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16875160932014169353569138383883420860307/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (2110497172978932450179357457059973193761/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2110497172978932450179357457059973193761/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0599.rows BesselBatch0599.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (6751827663169125791000799608072641282079/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6751827663169125791000799608072641282079/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1421 BracketBatch0088.bracket1422 (6751827663169125791000799608072641282079/4000000000000000000000000000000000000000) (635128632454833648215669850934670837293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1421 BracketBatch0088.bracket1422
  (6751827663169125791000799608072641282079/4000000000000000000000000000000000000000) (635128632454833648215669850934670837293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1421
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1422
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (3376795476766291920286971931295957110017/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3376795476766291920286971931295957110017/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (16892804324194007736722324102443756486183/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16892804324194007736722324102443756486183/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (8444195427006366834539295939730885509067/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8444195427006366834539295939730885509067/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1422 BracketBatch0088.bracket1423 (8444195427006366834539295939730885509067/5000000000000000000000000000000000000000) (635615458203196035879609733168499806427/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1422 BracketBatch0088.bracket1423
  (8444195427006366834539295939730885509067/5000000000000000000000000000000000000000) (635615458203196035879609733168499806427/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1422
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1423
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (844640216209700386836116205122187824309/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (844640216209700386836116205122187824309/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (16901641773471209219690637323449679175293/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16901641773471209219690637323449679175293/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (33794446097665216956412961425893435661473/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33794446097665216956412961425893435661473/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0177.rows ScalarLogs0177.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0088.bracket1423 BracketBatch0089.bracket1424 (33794446097665216956412961425893435661473/20000000000000000000000000000000000000000) (159025692455551400654844755270891899981/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0088.bracket1423 BracketBatch0089.bracket1424
  (33794446097665216956412961425893435661473/20000000000000000000000000000000000000000) (159025692455551400654844755270891899981/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1423
