module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0046
public import BecknerOnofri.EntropyScalarCertificate.Bessel0047
public import BecknerOnofri.EntropyScalarCertificate.Bessel0512
public import BecknerOnofri.EntropyScalarCertificate.Brackets0018
public import BecknerOnofri.EntropyScalarCertificate.Brackets0019
public import BecknerOnofri.EntropyScalarCertificate.Logs0037
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0296
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1164831586470030512724772800233911121189/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1164831586470030512724772800233911121189/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1166872578242509093056806690836118634797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1166872578242509093056806690836118634797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (1165852082356269802890789745535014877993/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1165852082356269802890789745535014877993/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0296 BracketBatch0018.bracket0297 (1165852082356269802890789745535014877993/10000000000000000000000000000000000000000) (27988966369143805382780115641850999/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0296 BracketBatch0018.bracket0297
  (1165852082356269802890789745535014877993/10000000000000000000000000000000000000000) (27988966369143805382780115641850999/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0296
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0297
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (583436289121254546528403345418059317397/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (583436289121254546528403345418059317397/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1168913714426893213633638703509989095841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1168913714426893213633638703509989095841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (467157258533880461338089078869221546127/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (467157258533880461338089078869221546127/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0297 BracketBatch0018.bracket0298 (467157258533880461338089078869221546127/4000000000000000000000000000000000000000) (140920477302018568037430408461241619/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0297 BracketBatch0018.bracket0298
  (467157258533880461338089078869221546127/4000000000000000000000000000000000000000) (140920477302018568037430408461241619/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0297
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0298
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (584456857213446606816819351754994547919/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (584456857213446606816819351754994547919/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1170954995291339086541256388746832450517/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1170954995291339086541256388746832450517/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (467973741943646460034979018451364309271/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (467973741943646460034979018451364309271/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0298 BracketBatch0018.bracket0299 (467973741943646460034979018451364309271/4000000000000000000000000000000000000000) (35475303647633521723129137174166827/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0298 BracketBatch0018.bracket0299
  (467973741943646460034979018451364309271/4000000000000000000000000000000000000000) (35475303647633521723129137174166827/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0298
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0299
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (585477497645669543270628194373416225257/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (585477497645669543270628194373416225257/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (23459928422082090999691420104106770019/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (23459928422082090999691420104106770019/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (292993927049430454565728424244021368933/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (292993927049430454565728424244021368933/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0299 BracketBatch0018.bracket0300 (292993927049430454565728424244021368933/2500000000000000000000000000000000000000) (28577412308245432866703218298271329/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0299 BracketBatch0018.bracket0300
  (292993927049430454565728424244021368933/2500000000000000000000000000000000000000) (28577412308245432866703218298271329/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0299
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0300
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0046.rows BesselBatch0046.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1172996421104104549984571005205338500947/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1172996421104104549984571005205338500947/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (235007598426709855015472154194465872373/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (235007598426709855015472154194465872373/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (587008603309413456265482944044416965703/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (587008603309413456265482944044416965703/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0300 BracketBatch0018.bracket0301 (587008603309413456265482944044416965703/5000000000000000000000000000000000000000) (143878036016488522860290210078721617/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0300 BracketBatch0018.bracket0301
  (587008603309413456265482944044416965703/5000000000000000000000000000000000000000) (143878036016488522860290210078721617/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0300
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0301
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (587518996066774637538680385486164680931/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (587518996066774637538680385486164680931/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1177079708648134972806848499428561246109/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1177079708648134972806848499428561246109/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2352117700781684247884209270400890607971/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2352117700781684247884209270400890607971/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0301 BracketBatch0018.bracket0302 (2352117700781684247884209270400890607971/20000000000000000000000000000000000000000) (14487415591114700400115018101147647/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0301 BracketBatch0018.bracket0302
  (2352117700781684247884209270400890607971/20000000000000000000000000000000000000000) (14487415591114700400115018101147647/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0301
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0302
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (588539854324067486403424249714280623053/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (588539854324067486403424249714280623053/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (294780392729106400293327804965698343001/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (294780392729106400293327804965698343001/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (235620127956456057398015971929135461811/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (235620127956456057398015971929135461811/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0302 BracketBatch0018.bracket0303 (235620127956456057398015971929135461811/2000000000000000000000000000000000000000) (18234429894059820430194544703087597/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0302 BracketBatch0018.bracket0303
  (235620127956456057398015971929135461811/2000000000000000000000000000000000000000) (18234429894059820430194544703087597/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0302
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0303
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1179121570916425601173311219862793372001/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1179121570916425601173311219862793372001/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0047.rows BesselBatch0047.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1181163579207087572505119936267736182917/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1181163579207087572505119936267736182917/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0512.rows BesselBatch0512.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1180142575061756586839215578065264777459/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1180142575061756586839215578065264777459/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0037.rows ScalarLogs0037.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0018.bracket0303 BracketBatch0019.bracket0304 (1180142575061756586839215578065264777459/10000000000000000000000000000000000000000) (146881903700215283911191035348139193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0018.bracket0303 BracketBatch0019.bracket0304
  (1180142575061756586839215578065264777459/10000000000000000000000000000000000000000) (146881903700215283911191035348139193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0303
