module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0317
public import BecknerOnofri.EntropyScalarCertificate.Bessel0318
public import BecknerOnofri.EntropyScalarCertificate.Bessel0647
public import BecknerOnofri.EntropyScalarCertificate.Bessel0648
public import BecknerOnofri.EntropyScalarCertificate.Brackets0127
public import BecknerOnofri.EntropyScalarCertificate.Logs0254
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2032
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (7174847461365631991044413746596369552011/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7174847461365631991044413746596369552011/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (11504899782774349598512716022149609824439/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11504899782774349598512716022149609824439/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (114923278604796803920918890083519005538283/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (114923278604796803920918890083519005538283/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2032 BracketBatch0127.bracket2033 (114923278604796803920918890083519005538283/20000000000000000000000000000000000000000) (2043688348588102008294346501398322979663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2032 BracketBatch0127.bracket2033
  (114923278604796803920918890083519005538283/20000000000000000000000000000000000000000) (2043688348588102008294346501398322979663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2032
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2033
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (3595281182116984249535223756921753070137/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3595281182116984249535223756921753070137/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (7206348215043644054459771369054584336823/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7206348215043644054459771369054584336823/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (14396910579277612553530218882898090477097/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14396910579277612553530218882898090477097/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2033 BracketBatch0127.bracket2034 (14396910579277612553530218882898090477097/2500000000000000000000000000000000000000) (2046466608732583693336329580372942953513/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2033 BracketBatch0127.bracket2034
  (14396910579277612553530218882898090477097/2500000000000000000000000000000000000000) (2046466608732583693336329580372942953513/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2033
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2034
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (57650785720349152435678170952436674694581/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57650785720349152435678170952436674694581/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (11555528790487472405128920323042891493589/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11555528790487472405128920323042891493589/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (57714214836393257230661386283825566081263/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57714214836393257230661386283825566081263/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2034 BracketBatch0127.bracket2035 (57714214836393257230661386283825566081263/10000000000000000000000000000000000000000) (2049251844335607852856438235078245611227/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2034 BracketBatch0127.bracket2035
  (57714214836393257230661386283825566081263/10000000000000000000000000000000000000000) (2049251844335607852856438235078245611227/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2034
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2035
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0317.rows BesselBatch0317.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (28888821976218681012822300807607228733971/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28888821976218681012822300807607228733971/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (28952538743495873379574033500373543179723/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28952538743495873379574033500373543179723/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (28920680359857277196198167153990385956847/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (28920680359857277196198167153990385956847/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2035 BracketBatch0127.bracket2036 (28920680359857277196198167153990385956847/5000000000000000000000000000000000000000) (2052044087486898790661892468794633923859/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2035 BracketBatch0127.bracket2036
  (28920680359857277196198167153990385956847/5000000000000000000000000000000000000000) (2052044087486898790661892468794633923859/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2035
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2036
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (57905077486991746759148067000747086359443/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (57905077486991746759148067000747086359443/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (11606618047207439689486601256510296487819/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11606618047207439689486601256510296487819/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0647.rows BesselBatch0647.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (57969083861514472603290536641649284399269/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (57969083861514472603290536641649284399269/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2036 BracketBatch0127.bracket2037 (57969083861514472603290536641649284399269/10000000000000000000000000000000000000000) (2054843370501268095188227474897478033231/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2036 BracketBatch0127.bracket2037
  (57969083861514472603290536641649284399269/10000000000000000000000000000000000000000) (2054843370501268095188227474897478033231/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2036
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2037
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (14508272559009299611858251570637870609773/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14508272559009299611858251570637870609773/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (5816168614716775151147619892767429753143/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5816168614716775151147619892767429753143/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (58097388191602474979454602605112889985261/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (58097388191602474979454602605112889985261/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2037 BracketBatch0127.bracket2038 (58097388191602474979454602605112889985261/10000000000000000000000000000000000000000) (1028824862960343049545470747901730725013/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2037 BracketBatch0127.bracket2038
  (58097388191602474979454602605112889985261/10000000000000000000000000000000000000000) (1028824862960343049545470747901730725013/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2037
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2038
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (58161686147167751511476198927674297531427/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58161686147167751511476198927674297531427/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (58290869203951665715161241833327345355869/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58290869203951665715161241833327345355869/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (909785588680620447083105005945325335057/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (909785588680620447083105005945325335057/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2038 BracketBatch0127.bracket2039 (909785588680620447083105005945325335057/156250000000000000000000000000000000000) (1006085540291199656451286248606829953/4882812500000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2038 BracketBatch0127.bracket2039
  (909785588680620447083105005945325335057/156250000000000000000000000000000000000) (1006085540291199656451286248606829953/4882812500000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2038
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2039
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (29145434601975832857580620916663672677933/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29145434601975832857580620916663672677933/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (58420643426342058130826753521167404947539/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58420643426342058130826753521167404947539/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (23342302526058744769197599070898950060681/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23342302526058744769197599070898950060681/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0254.rows ScalarLogs0254.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2039 BracketBatch0127.bracket2040 (23342302526058744769197599070898950060681/4000000000000000000000000000000000000000) (2063283785290937236881174739552046022243/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2039 BracketBatch0127.bracket2040
  (23342302526058744769197599070898950060681/4000000000000000000000000000000000000000) (2063283785290937236881174739552046022243/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2039
