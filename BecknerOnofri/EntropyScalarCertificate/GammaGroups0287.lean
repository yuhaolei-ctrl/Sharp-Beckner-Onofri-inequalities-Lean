module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0358
public import BecknerOnofri.EntropyScalarCertificate.Bessel0359
public import BecknerOnofri.EntropyScalarCertificate.Bessel0360
public import BecknerOnofri.EntropyScalarCertificate.Bessel0668
public import BecknerOnofri.EntropyScalarCertificate.Brackets0143
public import BecknerOnofri.EntropyScalarCertificate.Brackets0144
public import BecknerOnofri.EntropyScalarCertificate.Logs0287
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2296
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (138648430197560441798048624742805222907247/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (138648430197560441798048624742805222907247/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (139407133328281169458424751165138558823657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (139407133328281169458424751165138558823657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (34756945440730201407059171988492972716363/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34756945440730201407059171988492972716363/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2296 BracketBatch0143.bracket2297 (34756945440730201407059171988492972716363/2500000000000000000000000000000000000000) (3199663308124983554362540099867621944543/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2296 BracketBatch0143.bracket2297
  (34756945440730201407059171988492972716363/2500000000000000000000000000000000000000) (3199663308124983554362540099867621944543/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2296
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2297
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0358.rows BesselBatch0358.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (69703566664140584729212375582569279411827/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (69703566664140584729212375582569279411827/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (35043567226149288044356558378530288038401/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (35043567226149288044356558378530288038401/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (139790701116439160817925492339629855488629/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (139790701116439160817925492339629855488629/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2297 BracketBatch0143.bracket2298 (139790701116439160817925492339629855488629/10000000000000000000000000000000000000000) (641396339431705869226048470811855634649/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2297 BracketBatch0143.bracket2298
  (139790701116439160817925492339629855488629/10000000000000000000000000000000000000000) (641396339431705869226048470811855634649/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2297
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2298
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (140174268904597152177426233514121152153601/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (140174268904597152177426233514121152153601/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (70474989125150542671581363332862913902121/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (70474989125150542671581363332862913902121/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (281124247154898237520588960179846979957843/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (281124247154898237520588960179846979957843/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2298 BracketBatch0143.bracket2299 (281124247154898237520588960179846979957843/20000000000000000000000000000000000000000) (1607170841766007910377013860082863981971/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2298 BracketBatch0143.bracket2299
  (281124247154898237520588960179846979957843/20000000000000000000000000000000000000000) (1607170841766007910377013860082863981971/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2298
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2299
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (140949978250301085343162726665725827804239/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (140949978250301085343162726665725827804239/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (5669376234600203857424046117307997750751/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5669376234600203857424046117307997750751/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (141342192057653090889381939799212885786507/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (141342192057653090889381939799212885786507/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2299 BracketBatch0143.bracket2300 (141342192057653090889381939799212885786507/10000000000000000000000000000000000000000) (644348737086970643151540185101854237183/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2299 BracketBatch0143.bracket2300
  (141342192057653090889381939799212885786507/10000000000000000000000000000000000000000) (644348737086970643151540185101854237183/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2299
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2300
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (35433601466251274108900288233174985942193/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (35433601466251274108900288233174985942193/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (142527699513853145947399410334074699813579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (142527699513853145947399410334074699813579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (284262105378858242383000563266774643582351/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (284262105378858242383000563266774643582351/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2300 BracketBatch0143.bracket2301 (284262105378858242383000563266774643582351/20000000000000000000000000000000000000000) (3229188126405801503402931843618448971217/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2300 BracketBatch0143.bracket2301
  (284262105378858242383000563266774643582351/20000000000000000000000000000000000000000) (3229188126405801503402931843618448971217/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2300
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2301
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (17815962439231643243424926291759337476697/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17815962439231643243424926291759337476697/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (559882852813639865902665878647341728263/39062500000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (559882852813639865902665878647341728263/39062500000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (35732213729268118952310234408474272781113/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35732213729268118952310234408474272781113/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2301 BracketBatch0143.bracket2302 (35732213729268118952310234408474272781113/2500000000000000000000000000000000000000) (3236675435391177386141271424805041979681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2301 BracketBatch0143.bracket2302
  (35732213729268118952310234408474272781113/2500000000000000000000000000000000000000) (3236675435391177386141271424805041979681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2301
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2302
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (5733200412811672226843298597348779297413/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5733200412811672226843298597348779297413/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (28828298572404349889352244037449020686917/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28828298572404349889352244037449020686917/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (28747150318231355511784368512096458586991/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28747150318231355511784368512096458586991/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2302 BracketBatch0143.bracket2303 (28747150318231355511784368512096458586991/2000000000000000000000000000000000000000) (1622103023401055165757072584826020154181/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2302 BracketBatch0143.bracket2303
  (28747150318231355511784368512096458586991/2000000000000000000000000000000000000000) (1622103023401055165757072584826020154181/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2302
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2303
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0359.rows BesselBatch0359.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (72070746431010874723380610093622551717291/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (72070746431010874723380610093622551717291/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0360.rows BesselBatch0360.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (14496230527025791606663135825905494408437/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14496230527025791606663135825905494408437/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0668.rows BesselBatch0668.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (36137974766534958189174072305787505939869/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36137974766534958189174072305787505939869/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0287.rows ScalarLogs0287.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0143.bracket2303 BracketBatch0144.bracket2304 (36137974766534958189174072305787505939869/2500000000000000000000000000000000000000) (26014243204565533791795688609408203239/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0143.bracket2303 BracketBatch0144.bracket2304
  (36137974766534958189174072305787505939869/2500000000000000000000000000000000000000) (26014243204565533791795688609408203239/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2303
