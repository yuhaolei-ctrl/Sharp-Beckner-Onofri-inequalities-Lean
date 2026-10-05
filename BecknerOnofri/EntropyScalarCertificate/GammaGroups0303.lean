module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0378
public import BecknerOnofri.EntropyScalarCertificate.Bessel0379
public import BecknerOnofri.EntropyScalarCertificate.Bessel0380
public import BecknerOnofri.EntropyScalarCertificate.Bessel0678
public import BecknerOnofri.EntropyScalarCertificate.Brackets0151
public import BecknerOnofri.EntropyScalarCertificate.Brackets0152
public import BecknerOnofri.EntropyScalarCertificate.Logs0303
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2424
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (27659782154301451549172004803409680253613/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27659782154301451549172004803409680253613/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (34650696952624544418697394234047067842287/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34650696952624544418697394234047067842287/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (276901698582005435420649600953236672637213/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (276901698582005435420649600953236672637213/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2424 BracketBatch0151.bracket2425 (276901698582005435420649600953236672637213/10000000000000000000000000000000000000000) (1045164410986482186740898884857700803949/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2424 BracketBatch0151.bracket2425
  (276901698582005435420649600953236672637213/10000000000000000000000000000000000000000) (1045164410986482186740898884857700803949/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2424
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2425
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0378.rows BesselBatch0378.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (277205575620996355349579153872376542738293/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (277205575620996355349579153872376542738293/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (277816019054335846457756537263064345786357/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (277816019054335846457756537263064345786357/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (11100431893506644036146713822708817770493/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11100431893506644036146713822708817770493/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2425 BracketBatch0151.bracket2426 (11100431893506644036146713822708817770493/400000000000000000000000000000000000000) (104595414872261022815139019696326239631/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2425 BracketBatch0151.bracket2426
  (11100431893506644036146713822708817770493/400000000000000000000000000000000000000) (104595414872261022815139019696326239631/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2425
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2426
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (138908009527167923228878268631532172893177/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (138908009527167923228878268631532172893177/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (278429169732286042034454765095370372400243/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (278429169732286042034454765095370372400243/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (556245188786621888492211302358434718186597/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (556245188786621888492211302358434718186597/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2426 BracketBatch0151.bracket2427 (556245188786621888492211302358434718186597/20000000000000000000000000000000000000000) (4186982939891100788495522918954240370391/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2426 BracketBatch0151.bracket2427
  (556245188786621888492211302358434718186597/20000000000000000000000000000000000000000) (4186982939891100788495522918954240370391/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2426
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2427
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (3480364621653575525430684563692129655003/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3480364621653575525430684563692129655003/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (279045045703115587364576685690827359729471/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (279045045703115587364576685690827359729471/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (557474215435401629399031450786197732129711/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (557474215435401629399031450786197732129711/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2427 BracketBatch0151.bracket2428 (557474215435401629399031450786197732129711/20000000000000000000000000000000000000000) (209507835575191121491711688993253599023/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2427 BracketBatch0151.bracket2428
  (557474215435401629399031450786197732129711/20000000000000000000000000000000000000000) (209507835575191121491711688993253599023/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2427
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2428
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (69761261425778896841144171422706839932367/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69761261425778896841144171422706839932367/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (279663665175879494761851393412668155544123/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (279663665175879494761851393412668155544123/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (558708710878995082126428079103495515273591/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (558708710878995082126428079103495515273591/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2428 BracketBatch0151.bracket2429 (558708710878995082126428079103495515273591/20000000000000000000000000000000000000000) (838667588498559696057713280836124623457/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2428 BracketBatch0151.bracket2429
  (558708710878995082126428079103495515273591/20000000000000000000000000000000000000000) (838667588498559696057713280836124623457/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2428
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2429
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (6991591629396987369046284835316703888603/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6991591629396987369046284835316703888603/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (56057009304442726853412895565499121642649/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56057009304442726853412895565499121642649/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (111989742339618625805783174248032752751473/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (111989742339618625805783174248032752751473/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2429 BracketBatch0151.bracket2430 (111989742339618625805783174248032752751473/4000000000000000000000000000000000000000) (2098263332916110735606919925174049044207/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2429 BracketBatch0151.bracket2430
  (111989742339618625805783174248032752751473/4000000000000000000000000000000000000000) (2098263332916110735606919925174049044207/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2429
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2430
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (140142523261106817133532238913747804106621/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (140142523261106817133532238913747804106621/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (140454604139076655734879419288082554620431/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (140454604139076655734879419288082554620431/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (70149281850045868217102914550457589681763/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (70149281850045868217102914550457589681763/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2430 BracketBatch0151.bracket2431 (70149281850045868217102914550457589681763/2500000000000000000000000000000000000000) (1049930728677005539580938599544218734253/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2430 BracketBatch0151.bracket2431
  (70149281850045868217102914550457589681763/2500000000000000000000000000000000000000) (1049930728677005539580938599544218734253/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2430
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2431
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0379.rows BesselBatch0379.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (280909208278153311469758838576165109240859/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (280909208278153311469758838576165109240859/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0380.rows BesselBatch0380.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (56307233829195262100485828279963463815419/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56307233829195262100485828279963463815419/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0678.rows BesselBatch0678.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (281222688712064810986093989987991214158977/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (281222688712064810986093989987991214158977/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0303.rows ScalarLogs0303.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0151.bracket2431 BracketBatch0152.bracket2432 (281222688712064810986093989987991214158977/10000000000000000000000000000000000000000) (1050731680629906271245497918211471457207/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0151.bracket2431 BracketBatch0152.bracket2432
  (281222688712064810986093989987991214158977/10000000000000000000000000000000000000000) (1050731680629906271245497918211471457207/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2431
