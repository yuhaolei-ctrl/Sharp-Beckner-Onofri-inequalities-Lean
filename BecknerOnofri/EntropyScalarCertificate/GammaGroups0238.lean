module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0297
public import BecknerOnofri.EntropyScalarCertificate.Bessel0298
public import BecknerOnofri.EntropyScalarCertificate.Bessel0637
public import BecknerOnofri.EntropyScalarCertificate.Bessel0638
public import BecknerOnofri.EntropyScalarCertificate.Brackets0119
public import BecknerOnofri.EntropyScalarCertificate.Logs0238
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1904
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (15103839696116888966545999846044998754071/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15103839696116888966545999846044998754071/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (7592981387233788058651241119284097792489/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7592981387233788058651241119284097792489/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (30289802470584465083848482084613194339049/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30289802470584465083848482084613194339049/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1904 BracketBatch0119.bracket1905 (30289802470584465083848482084613194339049/10000000000000000000000000000000000000000) (312957711320760206894905180035256289581/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1904 BracketBatch0119.bracket1905
  (30289802470584465083848482084613194339049/10000000000000000000000000000000000000000) (312957711320760206894905180035256289581/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1904
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1905
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (30371925548935152234604964477136391169953/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30371925548935152234604964477136391169953/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (30538112703124574664263573683029014403607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30538112703124574664263573683029014403607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1522750956301493172471713454004135139339/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1522750956301493172471713454004135139339/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1905 BracketBatch0119.bracket1906 (1522750956301493172471713454004135139339/500000000000000000000000000000000000000) (125812609587308087052774452023234547831/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1905 BracketBatch0119.bracket1906
  (1522750956301493172471713454004135139339/500000000000000000000000000000000000000) (125812609587308087052774452023234547831/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1905
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1906
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (7634528175781143666065893420757253600901/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7634528175781143666065893420757253600901/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (30706274770952959450554904163675755291631/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (30706274770952959450554904163675755291631/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (12248877494815506822963695569340953939047/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12248877494815506822963695569340953939047/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1906 BracketBatch0119.bracket1907 (12248877494815506822963695569340953939047/4000000000000000000000000000000000000000) (79029239285434402919452877333060277051/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1906 BracketBatch0119.bracket1907
  (12248877494815506822963695569340953939047/4000000000000000000000000000000000000000) (79029239285434402919452877333060277051/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1906
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1907
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (7676568692738239862638726040918938822907/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7676568692738239862638726040918938822907/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (3087644646115894631189732338391154671929/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3087644646115894631189732338391154671929/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (30791360616055952881226113773793651005459/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30791360616055952881226113773793651005459/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1907 BracketBatch0119.bracket1908 (30791360616055952881226113773793651005459/10000000000000000000000000000000000000000) (1270856537831217048356833800063216894473/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1907 BracketBatch0119.bracket1908
  (30791360616055952881226113773793651005459/10000000000000000000000000000000000000000) (1270856537831217048356833800063216894473/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1907
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1908
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (30876446461158946311897323383911546719287/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30876446461158946311897323383911546719287/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (48513536404183815295020117533935112281/15625000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48513536404183815295020117533935112281/15625000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (61925109759836588100710198605630018579127/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61925109759836588100710198605630018579127/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1908 BracketBatch0119.bracket1909 (61925109759836588100710198605630018579127/20000000000000000000000000000000000000000) (127729272611022932628307553634312971191/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1908 BracketBatch0119.bracket1909
  (61925109759836588100710198605630018579127/20000000000000000000000000000000000000000) (127729272611022932628307553634312971191/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1908
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1909
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (31048663298677641788812875221718471859837/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31048663298677641788812875221718471859837/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (780574041227431407642577432844118043307/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (780574041227431407642577432844118043307/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (62271624947774898094515972535483193592117/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (62271624947774898094515972535483193592117/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1909 BracketBatch0119.bracket1910 (62271624947774898094515972535483193592117/20000000000000000000000000000000000000000) (1604721130026718716396497942902808279/12500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1909 BracketBatch0119.bracket1910
  (62271624947774898094515972535483193592117/20000000000000000000000000000000000000000) (1604721130026718716396497942902808279/12500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1909
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1910
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (31222961649097256305703097313764721732277/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (31222961649097256305703097313764721732277/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (31399378743998975183228010175103189935631/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31399378743998975183228010175103189935631/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (15655585098274057872232776872216977916977/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (15655585098274057872232776872216977916977/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1910 BracketBatch0119.bracket1911 (15655585098274057872232776872216977916977/5000000000000000000000000000000000000000) (1290309590556010889555207891132904007541/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1910 BracketBatch0119.bracket1911
  (15655585098274057872232776872216977916977/5000000000000000000000000000000000000000) (1290309590556010889555207891132904007541/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1910
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1911
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (7849844685999743795807002543775797483907/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7849844685999743795807002543775797483907/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (31577952707217092375928046869828937847797/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31577952707217092375928046869828937847797/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2519093258048642702366242281797285111337/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2519093258048642702366242281797285111337/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0238.rows ScalarLogs0238.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1911 BracketBatch0119.bracket1912 (2519093258048642702366242281797285111337/800000000000000000000000000000000000000) (129689131328623449326973791491960099403/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1911 BracketBatch0119.bracket1912
  (2519093258048642702366242281797285111337/800000000000000000000000000000000000000) (129689131328623449326973791491960099403/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1911
