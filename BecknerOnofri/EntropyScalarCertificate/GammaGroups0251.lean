import BecknerOnofri.EntropyScalarCertificate.Bessel0313
import BecknerOnofri.EntropyScalarCertificate.Bessel0314
import BecknerOnofri.EntropyScalarCertificate.Bessel0315
import BecknerOnofri.EntropyScalarCertificate.Bessel0645
import BecknerOnofri.EntropyScalarCertificate.Bessel0646
import BecknerOnofri.EntropyScalarCertificate.Brackets0125
import BecknerOnofri.EntropyScalarCertificate.Brackets0126
import BecknerOnofri.EntropyScalarCertificate.Logs0251
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2008
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (54542377941725629764690213726837147188819/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54542377941725629764690213726837147188819/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (54655543796631437626666870310586994679043/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54655543796631437626666870310586994679043/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (54598960869178533695678542018712070933931/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54598960869178533695678542018712070933931/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2008 BracketBatch0125.bracket2009 (54598960869178533695678542018712070933931/10000000000000000000000000000000000000000) (1979023066675994861820210394044679424089/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2008 BracketBatch0125.bracket2009
  (54598960869178533695678542018712070933931/10000000000000000000000000000000000000000) (1979023066675994861820210394044679424089/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2008
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2009
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0313.rows BesselBatch0313.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (42699643591118310645833492430146089593/7812500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42699643591118310645833492430146089593/7812500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (5476919451930349710254742441401284088477/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5476919451930349710254742441401284088477/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (10942473831593493472921429472459983556381/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10942473831593493472921429472459983556381/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2009 BracketBatch0125.bracket2010 (10942473831593493472921429472459983556381/2000000000000000000000000000000000000000) (1981642991686897540999612609196977736567/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2009 BracketBatch0125.bracket2010
  (10942473831593493472921429472459983556381/2000000000000000000000000000000000000000) (1981642991686897540999612609196977736567/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2009
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2010
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (54769194519303497102547424414012840884767/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54769194519303497102547424414012840884767/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (54883333222875083471299090227099499121579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54883333222875083471299090227099499121579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (54826263871089290286923257320556170003173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54826263871089290286923257320556170003173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2010 BracketBatch0125.bracket2011 (54826263871089290286923257320556170003173/10000000000000000000000000000000000000000) (1984269184527600096503792426192529182353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2010 BracketBatch0125.bracket2011
  (54826263871089290286923257320556170003173/10000000000000000000000000000000000000000) (1984269184527600096503792426192529182353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2010
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2011
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (6860416652859385433912386278387437390197/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6860416652859385433912386278387437390197/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (54997963047207473758017368623420197397073/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54997963047207473758017368623420197397073/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (109881296270082557229316458850519696518649/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (109881296270082557229316458850519696518649/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2011 BracketBatch0125.bracket2012 (109881296270082557229316458850519696518649/20000000000000000000000000000000000000000) (1986901672451073124356555526140372102191/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2011 BracketBatch0125.bracket2012
  (109881296270082557229316458850519696518649/20000000000000000000000000000000000000000) (1986901672451073124356555526140372102191/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2011
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2012
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (5499796304720747375801736862342019739707/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5499796304720747375801736862342019739707/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (2204523486367092447107454768634016143621/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2204523486367092447107454768634016143621/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (22022210041276956987140747567854120197519/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22022210041276956987140747567854120197519/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2012 BracketBatch0125.bracket2013 (22022210041276956987140747567854120197519/4000000000000000000000000000000000000000) (1989540482891976164320517584511716031473/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2012 BracketBatch0125.bracket2013
  (22022210041276956987140747567854120197519/4000000000000000000000000000000000000000) (1989540482891976164320517584511716031473/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2012
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2013
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (27556543579588655588843184607925201795261/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27556543579588655588843184607925201795261/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (13807177188241921384463824818987566221753/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13807177188241921384463824818987566221753/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (55170897956072498357770834245900334238767/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (55170897956072498357770834245900334238767/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2013 BracketBatch0125.bracket2014 (55170897956072498357770834245900334238767/10000000000000000000000000000000000000000) (498046410867061994844976575240363062037/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2013 BracketBatch0125.bracket2014
  (55170897956072498357770834245900334238767/10000000000000000000000000000000000000000) (498046410867061994844976575240363062037/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2013
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2014
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (55228708752967685537855299275950264887009/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (55228708752967685537855299275950264887009/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (55344831050362985786207542443982606960939/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55344831050362985786207542443982606960939/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (27643384950832667831015710429983217961987/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (27643384950832667831015710429983217961987/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2014 BracketBatch0125.bracket2015 (27643384950832667831015710429983217961987/5000000000000000000000000000000000000000) (997418590991357013607451294603338191551/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2014 BracketBatch0125.bracket2015
  (27643384950832667831015710429983217961987/5000000000000000000000000000000000000000) (997418590991357013607451294603338191551/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2014
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2015
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0314.rows BesselBatch0314.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (6918103881295373223275942805497825870117/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6918103881295373223275942805497825870117/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0315.rows BesselBatch0315.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (108323158791108558323891744409834097961/19531250000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (108323158791108558323891744409834097961/19531250000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0646.rows BesselBatch0646.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (13850786043926320956005014447727208139621/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13850786043926320956005014447727208139621/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0251.rows ScalarLogs0251.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0125.bracket2015 BracketBatch0126.bracket2016 (13850786043926320956005014447727208139621/2500000000000000000000000000000000000000) (998747563212355672701207335354184769749/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0125.bracket2015 BracketBatch0126.bracket2016
  (13850786043926320956005014447727208139621/2500000000000000000000000000000000000000) (998747563212355672701207335354184769749/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2015
