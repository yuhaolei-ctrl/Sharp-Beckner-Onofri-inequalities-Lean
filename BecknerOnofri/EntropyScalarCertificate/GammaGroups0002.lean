module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0002
public import BecknerOnofri.EntropyScalarCertificate.Bessel0003
public import BecknerOnofri.EntropyScalarCertificate.Bessel0490
public import BecknerOnofri.EntropyScalarCertificate.Brackets0001
public import BecknerOnofri.EntropyScalarCertificate.Logs0002
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0016
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (634272431419512180318009946167489543279/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (634272431419512180318009946167489543279/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (31738772790088147824151903904939019461/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31738772790088147824151903904939019461/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1269047887221275136801048024266269932499/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1269047887221275136801048024266269932499/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0016 BracketBatch0001.bracket0017 (1269047887221275136801048024266269932499/20000000000000000000000000000000000000000) (12503517576115366927239688402824937/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0016 BracketBatch0001.bracket0017
  (1269047887221275136801048024266269932499/20000000000000000000000000000000000000000) (12503517576115366927239688402824937/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0016
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0017
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (634775455801762956483038078098780389217/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (634775455801762956483038078098780389217/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (9926226327947764677208947605437637221/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9926226327947764677208947605437637221/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (1270053940790419895824410724846789171361/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1270053940790419895824410724846789171361/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0017 BracketBatch0001.bracket0018 (1270053940790419895824410724846789171361/20000000000000000000000000000000000000000) (12543181942109030512299668921208127/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0017 BracketBatch0001.bracket0018
  (1270053940790419895824410724846789171361/20000000000000000000000000000000000000000) (12543181942109030512299668921208127/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0017
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0018
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (635278484988656939341372646748008782141/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (635278484988656939341372646748008782141/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (158945379746017833405081354073351850731/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (158945379746017833405081354073351850731/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (254212000794545654592339612608283237013/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (254212000794545654592339612608283237013/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0018 BracketBatch0001.bracket0019 (254212000794545654592339612608283237013/4000000000000000000000000000000000000000) (12582940490166797829024037645967563/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0018 BracketBatch0001.bracket0019
  (254212000794545654592339612608283237013/4000000000000000000000000000000000000000) (12582940490166797829024037645967563/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0018
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0019
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0002.rows BesselBatch0002.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (635781518984071333620325416293407402921/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (635781518984071333620325416293407402921/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (31814227889594177377292623865677978929/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31814227889594177377292623865677978929/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1272066076775954881166177893606966981501/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1272066076775954881166177893606966981501/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0019 BracketBatch0001.bracket0020 (1272066076775954881166177893606966981501/20000000000000000000000000000000000000000) (631139668480990805466482261929159/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0019 BracketBatch0001.bracket0020
  (1272066076775954881166177893606966981501/20000000000000000000000000000000000000000) (631139668480990805466482261929159/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0019
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0020
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (636284557791883547545852477313559578577/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (636284557791883547545852477313559578577/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (127357520283194238602330450351388718111/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (127357520283194238602330450351388718111/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (318268039801963685139376182267625792283/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (318268039801963685139376182267625792283/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0020 BracketBatch0001.bracket0021 (318268039801963685139376182267625792283/5000000000000000000000000000000000000000) (12662740729918954065036158803179457/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0020 BracketBatch0001.bracket0021
  (318268039801963685139376182267625792283/5000000000000000000000000000000000000000) (12662740729918954065036158803179457/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0020
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0021
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (79598450176996399126456531469617948819/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (79598450176996399126456531469617948819/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1593226624650530214370710643930265837/25000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1593226624650530214370710643930265837/25000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (159259781409522909844992063666131240669/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (159259781409522909844992063666131240669/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0021 BracketBatch0001.bracket0022 (159259781409522909844992063666131240669/2500000000000000000000000000000000000000) (396961960019837701022512001996329/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0021 BracketBatch0001.bracket0022
  (159259781409522909844992063666131240669/2500000000000000000000000000000000000000) (396961960019837701022512001996329/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0021
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0022
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (637290649860212085748284257572106334797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (637290649860212085748284257572106334797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (637793703128484245492308650941323465557/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (637793703128484245492308650941323465557/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (637542176494348165620296454256714900177/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (637542176494348165620296454256714900177/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0022 BracketBatch0001.bracket0023 (637542176494348165620296454256714900177/10000000000000000000000000000000000000000) (6371459745728849261154502852670209/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0022 BracketBatch0001.bracket0023
  (637542176494348165620296454256714900177/10000000000000000000000000000000000000000) (6371459745728849261154502852670209/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0022
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0023
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (318896851564242122746154325470661732777/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (318896851564242122746154325470661732777/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (638296761224665896155446564064460229371/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (638296761224665896155446564064460229371/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (51043618574126005665910208600231347797/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51043618574126005665910208600231347797/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0002.rows ScalarLogs0002.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0023 BracketBatch0001.bracket0024 (51043618574126005665910208600231347797/800000000000000000000000000000000000000) (6391575596098845384705002775372373/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0023 BracketBatch0001.bracket0024
  (51043618574126005665910208600231347797/800000000000000000000000000000000000000) (6391575596098845384705002775372373/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0023
