module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0397
public import BecknerOnofri.EntropyScalarCertificate.Bessel0398
public import BecknerOnofri.EntropyScalarCertificate.Bessel0687
public import BecknerOnofri.EntropyScalarCertificate.Bessel0688
public import BecknerOnofri.EntropyScalarCertificate.Brackets0159
public import BecknerOnofri.EntropyScalarCertificate.Logs0318
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2544
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (375514236520903469801221432490893038747487/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (375514236520903469801221432490893038747487/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (376638076091229054693879226091158213892983/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (376638076091229054693879226091158213892983/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (75215231261213252449510065858205125264047/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (75215231261213252449510065858205125264047/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2544 BracketBatch0159.bracket2545 (75215231261213252449510065858205125264047/2000000000000000000000000000000000000000) (184978572228526752536680382129322767167/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2544 BracketBatch0159.bracket2545
  (75215231261213252449510065858205125264047/2000000000000000000000000000000000000000) (184978572228526752536680382129322767167/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2544
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2545
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (18831903804561452734693961304557910694649/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18831903804561452734693961304557910694649/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (377768686017224220321978138152611493058981/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (377768686017224220321978138152611493058981/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (754406762108453275015857364243769706951961/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (754406762108453275015857364243769706951961/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2545 BracketBatch0159.bracket2546 (754406762108453275015857364243769706951961/20000000000000000000000000000000000000000) (231441796372417902372385897232462073169/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2545 BracketBatch0159.bracket2546
  (754406762108453275015857364243769706951961/20000000000000000000000000000000000000000) (231441796372417902372385897232462073169/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2545
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2546
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (188884343008612110160989069076305746529489/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (188884343008612110160989069076305746529489/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (378906127661591542758101815793215804113329/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (378906127661591542758101815793215804113329/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (756674813678815763080079953945827297172307/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (756674813678815763080079953945827297172307/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2546 BracketBatch0159.bracket2547 (756674813678815763080079953945827297172307/20000000000000000000000000000000000000000) (463322131432740602334364213498177887003/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2546 BracketBatch0159.bracket2547
  (756674813678815763080079953945827297172307/20000000000000000000000000000000000000000) (463322131432740602334364213498177887003/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2546
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2547
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0397.rows BesselBatch0397.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (189453063830795771379050907896607902056663/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (189453063830795771379050907896607902056663/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (190025231565411972149778700122587168011311/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (190025231565411972149778700122587168011311/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (189739147698103871764414804009597535033987/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (189739147698103871764414804009597535033987/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2547 BracketBatch0159.bracket2548 (189739147698103871764414804009597535033987/5000000000000000000000000000000000000000) (2318810273146397433664741348651156075463/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2547 BracketBatch0159.bracket2548
  (189739147698103871764414804009597535033987/5000000000000000000000000000000000000000) (2318810273146397433664741348651156075463/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2547
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2548
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (380050463130823944299557400245174336022619/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (380050463130823944299557400245174336022619/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (95300438821627124528951599477826939370419/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (95300438821627124528951599477826939370419/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (152250443683466488483072759631296418700859/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (152250443683466488483072759631296418700859/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2548 BracketBatch0159.bracket2549 (152250443683466488483072759631296418700859/4000000000000000000000000000000000000000) (58025421299482655496343321575548255861/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2548 BracketBatch0159.bracket2549
  (152250443683466488483072759631296418700859/4000000000000000000000000000000000000000) (58025421299482655496343321575548255861/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2548
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2549
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (381201755286508498115806397911307757481673/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (381201755286508498115806397911307757481673/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (477950084696046262262728796168098002551/12500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (477950084696046262262728796168098002551/12500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (763561823043345507925989434845786159522473/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (763561823043345507925989434845786159522473/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2549 BracketBatch0159.bracket2550 (763561823043345507925989434845786159522473/20000000000000000000000000000000000000000) (580807608577215521410118802776046581743/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2549 BracketBatch0159.bracket2550
  (763561823043345507925989434845786159522473/20000000000000000000000000000000000000000) (580807608577215521410118802776046581743/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2549
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2550
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (382360067756837009810183036934478402040797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (382360067756837009810183036934478402040797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (11985170779635243822282047611613759345501/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11985170779635243822282047611613759345501/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (765885532705164812123208560506118701096829/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (765885532705164812123208560506118701096829/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2550 BracketBatch0159.bracket2551 (765885532705164812123208560506118701096829/20000000000000000000000000000000000000000) (4650902122249033447844299871658289978521/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2550 BracketBatch0159.bracket2551
  (765885532705164812123208560506118701096829/20000000000000000000000000000000000000000) (4650902122249033447844299871658289978521/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2550
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2551
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (383525464948327802313025523571640299056029/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (383525464948327802313025523571640299056029/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0398.rows BesselBatch0398.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (48087251507220404893384843959242307120591/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48087251507220404893384843959242307120591/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0688.rows BesselBatch0688.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (768223477006091041460104275245578756020757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (768223477006091041460104275245578756020757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0318.rows ScalarLogs0318.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0159.bracket2551 BracketBatch0159.bracket2552 (768223477006091041460104275245578756020757/20000000000000000000000000000000000000000) (4655357547524831669110536093325665211069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0159.bracket2551 BracketBatch0159.bracket2552
  (768223477006091041460104275245578756020757/20000000000000000000000000000000000000000) (4655357547524831669110536093325665211069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2551
