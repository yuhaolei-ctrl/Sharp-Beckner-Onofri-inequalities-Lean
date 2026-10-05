module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0132
public import BecknerOnofri.EntropyScalarCertificate.Bessel0133
public import BecknerOnofri.EntropyScalarCertificate.Bessel0555
public import BecknerOnofri.EntropyScalarCertificate.Brackets0053
public import BecknerOnofri.EntropyScalarCertificate.Logs0106
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0848
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (218617881733776333179259084920839609179/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (218617881733776333179259084920839609179/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (701963028312114190459999810022035898607/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (701963028312114190459999810022035898607/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (7007701249300992283168144408843613239899/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7007701249300992283168144408843613239899/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0848 BracketBatch0053.bracket0849 (7007701249300992283168144408843613239899/20000000000000000000000000000000000000000) (9652558149427116346042646822074072091/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0848 BracketBatch0053.bracket0849
  (7007701249300992283168144408843613239899/20000000000000000000000000000000000000000) (9652558149427116346042646822074072091/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0848
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0849
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (438726892695071369037499881263772436629/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (438726892695071369037499881263772436629/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1760878969058511391598927502728864925399/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1760878969058511391598927502728864925399/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (703157307967759373549785405556790934383/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (703157307967759373549785405556790934383/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0849 BracketBatch0053.bracket0850 (703157307967759373549785405556790934383/2000000000000000000000000000000000000000) (4886552530581841610954081069443481429/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0849 BracketBatch0053.bracket0850
  (703157307967759373549785405556790934383/2000000000000000000000000000000000000000) (4886552530581841610954081069443481429/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0849
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0850
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (704351587623404556639571001091545970159/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (704351587623404556639571001091545970159/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1766857284156757250602607803782456922857/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1766857284156757250602607803782456922857/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (7055472506430537284403070613022643696509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7055472506430537284403070613022643696509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0850 BracketBatch0053.bracket0851 (7055472506430537284403070613022643696509/20000000000000000000000000000000000000000) (1978961045268187924099331326865922451/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0850 BracketBatch0053.bracket0851
  (7055472506430537284403070613022643696509/20000000000000000000000000000000000000000) (1978961045268187924099331326865922451/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0850
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0851
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (3533714568313514501205215607564913845711/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3533714568313514501205215607564913845711/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (886421275852232313328997917319442234881/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (886421275852232313328997917319442234881/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1415879934344488750904241455368536557047/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1415879934344488750904241455368536557047/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0851 BracketBatch0053.bracket0852 (1415879934344488750904241455368536557047/4000000000000000000000000000000000000000) (2504416636993703527132580192481039813/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0851 BracketBatch0053.bracket0852
  (1415879934344488750904241455368536557047/4000000000000000000000000000000000000000) (2504416636993703527132580192481039813/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0851
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0852
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (3545685103408929253315991669277768939521/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3545685103408929253315991669277768939521/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (889417403755018283837443786561023388357/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (889417403755018283837443786561023388357/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (7103354718429002388665766815521862492949/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7103354718429002388665766815521862492949/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0852 BracketBatch0053.bracket0853 (7103354718429002388665766815521862492949/20000000000000000000000000000000000000000) (126771212074647727202986140294180497/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0852 BracketBatch0053.bracket0853
  (7103354718429002388665766815521862492949/20000000000000000000000000000000000000000) (126771212074647727202986140294180497/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0852
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0853
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (142306784600802925413991005849763742137/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (142306784600802925413991005849763742137/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (3569668175124477297147543600921991586347/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3569668175124477297147543600921991586347/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1781834447536137608124329686791521284943/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1781834447536137608124329686791521284943/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0853 BracketBatch0053.bracket0854 (1781834447536137608124329686791521284943/5000000000000000000000000000000000000000) (102669044572870719586539103144216423/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0853 BracketBatch0053.bracket0854
  (1781834447536137608124329686791521284943/5000000000000000000000000000000000000000) (102669044572870719586539103144216423/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0853
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0854
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (446208521890559662143442950115248948293/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (446208521890559662143442950115248948293/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (895420214015806235581514436429728715511/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (895420214015806235581514436429728715511/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1787837257796925559868400336660226612097/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1787837257796925559868400336660226612097/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0854 BracketBatch0053.bracket0855 (1787837257796925559868400336660226612097/5000000000000000000000000000000000000000) (5196648518041796244766143241999254831/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0854 BracketBatch0053.bracket0855
  (1787837257796925559868400336660226612097/5000000000000000000000000000000000000000) (5196648518041796244766143241999254831/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0854
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0855
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (3581680856063224942326057745718914862041/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3581680856063224942326057745718914862041/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0133.rows BesselBatch0133.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (898426932635950873689490934003849233191/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (898426932635950873689490934003849233191/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1435077717321405687416804296346862358961/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1435077717321405687416804296346862358961/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0106.rows ScalarLogs0106.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0053.bracket0855 BracketBatch0053.bracket0856 (1435077717321405687416804296346862358961/4000000000000000000000000000000000000000) (10520882753892856656488301070323451383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0053.bracket0855 BracketBatch0053.bracket0856
  (1435077717321405687416804296346862358961/4000000000000000000000000000000000000000) (10520882753892856656488301070323451383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0855
