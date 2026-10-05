module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0396
public import BecknerOnofri.EntropyScalarCertificate.Bessel0397
public import BecknerOnofri.EntropyScalarCertificate.Bessel0687
public import BecknerOnofri.EntropyScalarCertificate.Brackets0158
public import BecknerOnofri.EntropyScalarCertificate.Brackets0159
public import BecknerOnofri.EntropyScalarCertificate.Logs0317
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2536
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (73352025215319911084848853436420374269213/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (73352025215319911084848853436420374269213/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (367831926177749191367106784545562798500411/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (367831926177749191367106784545562798500411/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (183648013063587186697837762931916167461619/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (183648013063587186697837762931916167461619/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2536 BracketBatch0158.bracket2537 (183648013063587186697837762931916167461619/5000000000000000000000000000000000000000) (4589977500010665060879153692736802874079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2536 BracketBatch0158.bracket2537
  (183648013063587186697837762931916167461619/5000000000000000000000000000000000000000) (4589977500010665060879153692736802874079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2536
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2537
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (45978990772218648920888348068195349812551/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45978990772218648920888348068195349812551/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (368910031217851003350581534545295224087519/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (368910031217851003350581534545295224087519/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (736741957395600194717688319090858022587927/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (736741957395600194717688319090858022587927/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2537 BracketBatch0158.bracket2538 (736741957395600194717688319090858022587927/20000000000000000000000000000000000000000) (1148560450057531065188900950161935359979/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2537 BracketBatch0158.bracket2538
  (736741957395600194717688319090858022587927/20000000000000000000000000000000000000000) (1148560450057531065188900950161935359979/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2537
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2538
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (92227507804462750837645383636323806021879/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (92227507804462750837645383636323806021879/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (5781164015512313830499684167991689680221/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5781164015512313830499684167991689680221/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (36945226410531954425128066064838168181083/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36945226410531954425128066064838168181083/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2538 BracketBatch0158.bracket2539 (36945226410531954425128066064838168181083/1000000000000000000000000000000000000000) (4598519249399118724251104471982237047423/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2538 BracketBatch0158.bracket2539
  (36945226410531954425128066064838168181083/1000000000000000000000000000000000000000) (4598519249399118724251104471982237047423/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2538
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2539
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (369994496992788085151979786751468139534141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (369994496992788085151979786751468139534141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (371085379958749851087045779564636494145497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (371085379958749851087045779564636494145497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (370539938475768968119512783158052316839819/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (370539938475768968119512783158052316839819/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2539 BracketBatch0158.bracket2540 (370539938475768968119512783158052316839819/10000000000000000000000000000000000000000) (575351240291901013471980285299971590633/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2539 BracketBatch0158.bracket2540
  (370539938475768968119512783158052316839819/10000000000000000000000000000000000000000) (575351240291901013471980285299971590633/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2539
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2540
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (185542689979374925543522889782318247072747/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (185542689979374925543522889782318247072747/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (46522842155253608210650952831028339861273/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46522842155253608210650952831028339861273/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (371634058600389358386126701106431606517839/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (371634058600389358386126701106431606517839/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2540 BracketBatch0158.bracket2541 (371634058600389358386126701106431606517839/10000000000000000000000000000000000000000) (4607113894473239284493817497916510856629/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2540 BracketBatch0158.bracket2541
  (371634058600389358386126701106431606517839/10000000000000000000000000000000000000000) (4607113894473239284493817497916510856629/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2540
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2541
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (372182737242028865685207622648226718890181/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (372182737242028865685207622648226718890181/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (11665207082781019273496605834079797567741/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11665207082781019273496605834079797567741/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (745469363891021482437099009338780241057893/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (745469363891021482437099009338780241057893/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2541 BracketBatch0158.bracket2542 (745469363891021482437099009338780241057893/20000000000000000000000000000000000000000) (576428905233981128731730990829141715103/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2541 BracketBatch0158.bracket2542
  (745469363891021482437099009338780241057893/20000000000000000000000000000000000000000) (576428905233981128731730990829141715103/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2541
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2542
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (373286626648992616751891386690553522167709/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (373286626648992616751891386690553522167709/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (374397106676233887351359396504870254609069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (374397106676233887351359396504870254609069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (373841866662613252051625391597711888388389/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (373841866662613252051625391597711888388389/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2542 BracketBatch0158.bracket2543 (373841866662613252051625391597711888388389/10000000000000000000000000000000000000000) (1153940510305011660161390141779499713557/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2542 BracketBatch0158.bracket2543
  (373841866662613252051625391597711888388389/10000000000000000000000000000000000000000) (1153940510305011660161390141779499713557/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2542
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2543
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (187198553338116943675679698252435127304533/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (187198553338116943675679698252435127304533/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (37551423652090346980122143249089303874749/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (37551423652090346980122143249089303874749/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (187477835799284339288145207248940823339139/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (187477835799284339288145207248940823339139/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0317.rows ScalarLogs0317.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2543 BracketBatch0159.bracket2544 (187477835799284339288145207248940823339139/5000000000000000000000000000000000000000) (18480425479375510100675482027551667133/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2543 BracketBatch0159.bracket2544
  (187477835799284339288145207248940823339139/5000000000000000000000000000000000000000) (18480425479375510100675482027551667133/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2543
