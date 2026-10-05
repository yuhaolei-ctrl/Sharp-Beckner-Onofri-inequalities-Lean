module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0371
public import BecknerOnofri.EntropyScalarCertificate.Bessel0372
public import BecknerOnofri.EntropyScalarCertificate.Bessel0674
public import BecknerOnofri.EntropyScalarCertificate.Bessel0675
public import BecknerOnofri.EntropyScalarCertificate.Brackets0148
public import BecknerOnofri.EntropyScalarCertificate.Brackets0149
public import BecknerOnofri.EntropyScalarCertificate.Logs0297
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2376
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (61591917824183984436487176573865209586837/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (61591917824183984436487176573865209586837/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (24879418696580751088249212448786211580789/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (24879418696580751088249212448786211580789/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (247580929131271724314220415391661477077619/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (247580929131271724314220415391661477077619/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2376 BracketBatch0148.bracket2377 (247580929131271724314220415391661477077619/10000000000000000000000000000000000000000) (792899192414294551282673570435512157739/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2376 BracketBatch0148.bracket2377
  (247580929131271724314220415391661477077619/10000000000000000000000000000000000000000) (792899192414294551282673570435512157739/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2376
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2377
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (248794186965807510882492124487862115807887/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (248794186965807510882492124487862115807887/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (251269237005498656037559188337974480395499/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (251269237005498656037559188337974480395499/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (250031711985653083460025656412918298101693/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (250031711985653083460025656412918298101693/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2377 BracketBatch0148.bracket2378 (250031711985653083460025656412918298101693/10000000000000000000000000000000000000000) (3977240693518787063998268057053392984917/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2377 BracketBatch0148.bracket2378
  (250031711985653083460025656412918298101693/10000000000000000000000000000000000000000) (3977240693518787063998268057053392984917/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2377
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2378
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (31408654625687332004694898542246810049437/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31408654625687332004694898542246810049437/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (62942549881283625994844576312388707551189/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (62942549881283625994844576312388707551189/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (125759859132658290004234373396882327650063/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (125759859132658290004234373396882327650063/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2378 BracketBatch0148.bracket2379 (125759859132658290004234373396882327650063/5000000000000000000000000000000000000000) (32342532429228417053774495615875447547/80000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2378 BracketBatch0148.bracket2379
  (125759859132658290004234373396882327650063/5000000000000000000000000000000000000000) (32342532429228417053774495615875447547/80000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2378
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2379
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (251770199525134503979378305249554830204753/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (251770199525134503979378305249554830204753/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (252273174105222319381564302562882996257779/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (252273174105222319381564302562882996257779/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (126010843407589205840235651953109456615633/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126010843407589205840235651953109456615633/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2379 BracketBatch0148.bracket2380 (126010843407589205840235651953109456615633/5000000000000000000000000000000000000000) (1011416825077831490294921804030493023027/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2379 BracketBatch0148.bracket2380
  (126010843407589205840235651953109456615633/5000000000000000000000000000000000000000) (1011416825077831490294921804030493023027/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2379
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2380
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0371.rows BesselBatch0371.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (15767073381576394961347768910180187266111/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15767073381576394961347768910180187266111/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (252778172890969775078388682393304124443009/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (252778172890969775078388682393304124443009/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (101010269399238418891990596991237424140157/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (101010269399238418891990596991237424140157/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2380 BracketBatch0148.bracket2381 (101010269399238418891990596991237424140157/4000000000000000000000000000000000000000) (2024262071037997569949666712771821900561/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2380 BracketBatch0148.bracket2381
  (101010269399238418891990596991237424140157/4000000000000000000000000000000000000000) (2024262071037997569949666712771821900561/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2380
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2381
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (126389086445484887539194341196652062221503/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (126389086445484887539194341196652062221503/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (126642604062764887897862248586393497384659/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126642604062764887897862248586393497384659/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0674.rows BesselBatch0674.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (126515845254124887718528294891522779803081/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126515845254124887718528294891522779803081/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2381 BracketBatch0148.bracket2382 (126515845254124887718528294891522779803081/5000000000000000000000000000000000000000) (2025693551762284605537292769718827623567/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2381 BracketBatch0148.bracket2382
  (126515845254124887718528294891522779803081/5000000000000000000000000000000000000000) (2025693551762284605537292769718827623567/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2381
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2382
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (50657041625105955159144899434557398953863/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (50657041625105955159144899434557398953863/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (25379429215098980392281638548304958235631/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25379429215098980392281638548304958235631/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (811327200442431327549665412249338523401/32000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (811327200442431327549665412249338523401/32000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2382 BracketBatch0148.bracket2383 (811327200442431327549665412249338523401/32000000000000000000000000000000000000) (4054256209378717316412936410427769274691/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2382 BracketBatch0148.bracket2383
  (811327200442431327549665412249338523401/32000000000000000000000000000000000000) (4054256209378717316412936410427769274691/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2382
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2383
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (253794292150989803922816385483049582356307/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (253794292150989803922816385483049582356307/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0372.rows BesselBatch0372.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (50861087481874656325892184111403009052351/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (50861087481874656325892184111403009052351/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0675.rows BesselBatch0675.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (254049864780181542776138653020032313809031/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (254049864780181542776138653020032313809031/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0297.rows ScalarLogs0297.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0148.bracket2383 BracketBatch0149.bracket2384 (254049864780181542776138653020032313809031/10000000000000000000000000000000000000000) (2028565742252938568486720785602311881221/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0148.bracket2383 BracketBatch0149.bracket2384
  (254049864780181542776138653020032313809031/10000000000000000000000000000000000000000) (2028565742252938568486720785602311881221/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2383
