module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0410
public import BecknerOnofri.EntropyScalarCertificate.Bessel0411
public import BecknerOnofri.EntropyScalarCertificate.Bessel0693
public import BecknerOnofri.EntropyScalarCertificate.Bessel0694
public import BecknerOnofri.EntropyScalarCertificate.Brackets0164
public import BecknerOnofri.EntropyScalarCertificate.Logs0328
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2624
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (493385632551978118046370003302416307594763/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (493385632551978118046370003302416307594763/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (495330756066766731707441316422562267338981/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (495330756066766731707441316422562267338981/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (61794774288671553109613207482811160933359/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61794774288671553109613207482811160933359/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2624 BracketBatch0164.bracket2625 (61794774288671553109613207482811160933359/1250000000000000000000000000000000000000) (5025524105357692184749396438749388809007/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2624 BracketBatch0164.bracket2625
  (61794774288671553109613207482811160933359/1250000000000000000000000000000000000000) (5025524105357692184749396438749388809007/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2624
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2625
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (247665378033383365853720658211281133669489/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (247665378033383365853720658211281133669489/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (497291317379123012213372445366061059309249/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (497291317379123012213372445366061059309249/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (992622073445889743920813761788623326648227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (992622073445889743920813761788623326648227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2625 BracketBatch0164.bracket2626 (992622073445889743920813761788623326648227/20000000000000000000000000000000000000000) (100626370359963344542677393468001483017/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2625 BracketBatch0164.bracket2626
  (992622073445889743920813761788623326648227/20000000000000000000000000000000000000000) (100626370359963344542677393468001483017/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2625
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2626
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (248645658689561506106686222683030529654623/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (248645658689561506106686222683030529654623/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (499267501004507343507368622239016905096449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (499267501004507343507368622239016905096449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (199311763676726071144148213521015592881139/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (199311763676726071144148213521015592881139/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2626 BracketBatch0164.bracket2627 (199311763676726071144148213521015592881139/4000000000000000000000000000000000000000) (5037135970835071222920137789663882624273/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2626 BracketBatch0164.bracket2627
  (199311763676726071144148213521015592881139/4000000000000000000000000000000000000000) (5037135970835071222920137789663882624273/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2626
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2627
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (249633750502253671753684311119508452548223/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (249633750502253671753684311119508452548223/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (501259494410627490818164200187189065554327/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (501259494410627490818164200187189065554327/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (1000526995415134834325532822426205970650773/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1000526995415134834325532822426205970650773/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2627 BracketBatch0164.bracket2628 (1000526995415134834325532822426205970650773/20000000000000000000000000000000000000000) (5042976629348984089685495978928519529061/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2627 BracketBatch0164.bracket2628
  (1000526995415134834325532822426205970650773/20000000000000000000000000000000000000000) (5042976629348984089685495978928519529061/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2627
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2628
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (125314873602656872704541050046797266388581/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (125314873602656872704541050046797266388581/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (251633744038360338290733677367978611163243/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (251633744038360338290733677367978611163243/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (100452698248734816739963155492314628788081/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (100452698248734816739963155492314628788081/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2628 BracketBatch0164.bracket2629 (100452698248734816739963155492314628788081/2000000000000000000000000000000000000000) (315552541289986390307171556486573923083/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2628 BracketBatch0164.bracket2629
  (100452698248734816739963155492314628788081/2000000000000000000000000000000000000000) (315552541289986390307171556486573923083/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2628
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2629
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (503267488076720676581467354735957222326483/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (503267488076720676581467354735957222326483/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (505291675554269900133704111210952796605553/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (505291675554269900133704111210952796605553/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (252139790907747644178792866486727504733009/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (252139790907747644178792866486727504733009/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2629 BracketBatch0164.bracket2630 (252139790907747644178792866486727504733009/5000000000000000000000000000000000000000) (1010945646688803299299213067739784476891/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2629 BracketBatch0164.bracket2630
  (252139790907747644178792866486727504733009/5000000000000000000000000000000000000000) (1010945646688803299299213067739784476891/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2629
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2630
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (10105833511085398002674082224219055932111/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10105833511085398002674082224219055932111/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (126833063382298786940675438295739494614313/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126833063382298786940675438295739494614313/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (506311964541732523948202932196955387531401/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (506311964541732523948202932196955387531401/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2630 BracketBatch0164.bracket2631 (506311964541732523948202932196955387531401/10000000000000000000000000000000000000000) (2530319759076200820722351691784492793221/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2630 BracketBatch0164.bracket2631
  (506311964541732523948202932196955387531401/10000000000000000000000000000000000000000) (2530319759076200820722351691784492793221/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2630
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2631
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (507332253529195147762701753182957978457249/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (507332253529195147762701753182957978457249/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (254694710942780730770051281493230268075569/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (254694710942780730770051281493230268075569/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (1016721675414756609302804316169418514608387/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1016721675414756609302804316169418514608387/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0328.rows ScalarLogs0328.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2631 BracketBatch0164.bracket2632 (1016721675414756609302804316169418514608387/20000000000000000000000000000000000000000) (1266643671706853222253556951759472110483/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2631 BracketBatch0164.bracket2632
  (1016721675414756609302804316169418514608387/20000000000000000000000000000000000000000) (1266643671706853222253556951759472110483/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2631
