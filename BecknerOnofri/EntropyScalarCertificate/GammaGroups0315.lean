module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0393
public import BecknerOnofri.EntropyScalarCertificate.Bessel0394
public import BecknerOnofri.EntropyScalarCertificate.Bessel0395
public import BecknerOnofri.EntropyScalarCertificate.Bessel0685
public import BecknerOnofri.EntropyScalarCertificate.Bessel0686
public import BecknerOnofri.EntropyScalarCertificate.Brackets0157
public import BecknerOnofri.EntropyScalarCertificate.Brackets0158
public import BecknerOnofri.EntropyScalarCertificate.Logs0315
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2520
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (350425683082099298772738854600510381443553/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (350425683082099298772738854600510381443553/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (351403689034852516436213302987056150185803/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (351403689034852516436213302987056150185803/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (175457343029237953802238039396891632907339/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (175457343029237953802238039396891632907339/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2520 BracketBatch0157.bracket2521 (175457343029237953802238039396891632907339/5000000000000000000000000000000000000000) (4523478198461171165278447276544734457259/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2520 BracketBatch0157.bracket2521
  (175457343029237953802238039396891632907339/5000000000000000000000000000000000000000) (4523478198461171165278447276544734457259/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2520
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2521
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0393.rows BesselBatch0393.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1757018445174262582181066514935280750929/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1757018445174262582181066514935280750929/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (17619359481282996264228866647930583151877/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17619359481282996264228866647930583151877/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (35189543933025622086039531797283390661167/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35189543933025622086039531797283390661167/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2521 BracketBatch0157.bracket2522 (35189543933025622086039531797283390661167/1000000000000000000000000000000000000000) (4527541810989299231445309780978753355779/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2521 BracketBatch0157.bracket2522
  (35189543933025622086039531797283390661167/1000000000000000000000000000000000000000) (4527541810989299231445309780978753355779/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2521
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2522
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (352387189625659925284577332958611663037537/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (352387189625659925284577332958611663037537/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (7067524625760943806322426831422170891417/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7067524625760943806322426831422170891417/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0685.rows BesselBatch0685.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (705763420913707115600698674529720207608387/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (705763420913707115600698674529720207608387/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2522 BracketBatch0157.bracket2523 (705763420913707115600698674529720207608387/20000000000000000000000000000000000000000) (4531617454325229194767292320284394714369/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2522 BracketBatch0157.bracket2523
  (705763420913707115600698674529720207608387/20000000000000000000000000000000000000000) (4531617454325229194767292320284394714369/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2522
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2523
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (353376231288047190316121341571108544570847/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (353376231288047190316121341571108544570847/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (88592715245053148554058157983587445500871/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (88592715245053148554058157983587445500871/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (707747092268259784532353973505458326574331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (707747092268259784532353973505458326574331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2523 BracketBatch0157.bracket2524 (707747092268259784532353973505458326574331/20000000000000000000000000000000000000000) (4535705194232910624994692659420903918623/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2523 BracketBatch0157.bracket2524
  (707747092268259784532353973505458326574331/20000000000000000000000000000000000000000) (4535705194232910624994692659420903918623/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2523
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2524
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (354370860980212594216232631934349782003481/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (354370860980212594216232631934349782003481/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8884278154811466520781556573909475592609/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8884278154811466520781556573909475592609/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (709741987172671255047494894890728805707841/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (709741987172671255047494894890728805707841/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2524 BracketBatch0157.bracket2525 (709741987172671255047494894890728805707841/20000000000000000000000000000000000000000) (1134951274249901386237226108991423558597/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2524 BracketBatch0157.bracket2525
  (709741987172671255047494894890728805707841/20000000000000000000000000000000000000000) (1134951274249901386237226108991423558597/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2524
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2525
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (355371126192458660831262262956379023704357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (355371126192458660831262262956379023704357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (178188537477375227021259810628944096452883/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (178188537477375227021259810628944096452883/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (711748201147209114873781884214267216610123/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (711748201147209114873781884214267216610123/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2525 BracketBatch0157.bracket2526 (711748201147209114873781884214267216610123/20000000000000000000000000000000000000000) (908783445888248811576040333367390191499/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2525 BracketBatch0157.bracket2526
  (711748201147209114873781884214267216610123/20000000000000000000000000000000000000000) (908783445888248811576040333367390191499/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2525
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2526
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (356377074954750454042519621257888192905763/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (356377074954750454042519621257888192905763/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (44673594480550384791303218345550515986683/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44673594480550384791303218345550515986683/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (713765830799153532372945368022292320799227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (713765830799153532372945368022292320799227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2526 BracketBatch0157.bracket2527 (713765830799153532372945368022292320799227/20000000000000000000000000000000000000000) (555180866565899028507706626968240183/1220703125000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2526 BracketBatch0157.bracket2527
  (713765830799153532372945368022292320799227/20000000000000000000000000000000000000000) (555180866565899028507706626968240183/1220703125000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2526
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2527
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0394.rows BesselBatch0394.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (357388755844403078330425746764404127893461/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (357388755844403078330425746764404127893461/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (89601554498475241265657145338909379662513/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89601554498475241265657145338909379662513/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (715794973838304043393054328120041646543513/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (715794973838304043393054328120041646543513/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0315.rows ScalarLogs0315.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0157.bracket2527 BracketBatch0158.bracket2528 (715794973838304043393054328120041646543513/20000000000000000000000000000000000000000) (4552178453289001367351102993038781140069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0157.bracket2527 BracketBatch0158.bracket2528
  (715794973838304043393054328120041646543513/20000000000000000000000000000000000000000) (4552178453289001367351102993038781140069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2527
