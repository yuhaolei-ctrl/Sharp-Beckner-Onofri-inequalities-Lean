module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0441
public import BecknerOnofri.EntropyScalarCertificate.Bessel0442
public import BecknerOnofri.EntropyScalarCertificate.Bessel0709
public import BecknerOnofri.EntropyScalarCertificate.Bessel0710
public import BecknerOnofri.EntropyScalarCertificate.Brackets0176
public import BecknerOnofri.EntropyScalarCertificate.Brackets0177
public import BecknerOnofri.EntropyScalarCertificate.Logs0353
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2824
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (993318247112048145872043540358771429448711/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (993318247112048145872043540358771429448711/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (995290530842141992698081944333816296998671/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (995290530842141992698081944333816296998671/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (994304388977095069285062742346293863223691/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (994304388977095069285062742346293863223691/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2824 BracketBatch0176.bracket2825 (994304388977095069285062742346293863223691/10000000000000000000000000000000000000000) (6103172081928660673190310063924751721069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2824 BracketBatch0176.bracket2825
  (994304388977095069285062742346293863223691/10000000000000000000000000000000000000000) (6103172081928660673190310063924751721069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2824
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2825
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (248822632710535498174520486083454074249667/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (248822632710535498174520486083454074249667/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (623294170196505194848593387800619118973/6250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (623294170196505194848593387800619118973/6250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (498140300789137576113957841203701721838867/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (498140300789137576113957841203701721838867/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2825 BracketBatch0176.bracket2826 (498140300789137576113957841203701721838867/5000000000000000000000000000000000000000) (6106224893037427914609781898209640366867/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2825 BracketBatch0176.bracket2826
  (498140300789137576113957841203701721838867/5000000000000000000000000000000000000000) (6106224893037427914609781898209640366867/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2825
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2826
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (997270672314408311757749420480990590356797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (997270672314408311757749420480990590356797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (249814679645298495977488289034712980868367/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (249814679645298495977488289034712980868367/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (399305878179120459133540515323968502766053/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (399305878179120459133540515323968502766053/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2826 BracketBatch0176.bracket2827 (399305878179120459133540515323968502766053/4000000000000000000000000000000000000000) (1221856771805377215770516068244748287027/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2826 BracketBatch0176.bracket2827
  (399305878179120459133540515323968502766053/4000000000000000000000000000000000000000) (1221856771805377215770516068244748287027/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2826
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2827
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (199851743716238796781990631227770384694693/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (199851743716238796781990631227770384694693/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (12515683963390808314641058371623498314751/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12515683963390808314641058371623498314751/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (400102687130491729816247565173746357730709/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (400102687130491729816247565173746357730709/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2827 BracketBatch0176.bracket2828 (400102687130491729816247565173746357730709/4000000000000000000000000000000000000000) (122246980070581319720165213430113966237/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2827 BracketBatch0176.bracket2828
  (400102687130491729816247565173746357730709/4000000000000000000000000000000000000000) (122246980070581319720165213430113966237/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2827
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2828
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0441.rows BesselBatch0441.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1001254717071264665171284669729879865180077/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1001254717071264665171284669729879865180077/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (250814678898394129482502636791522031913181/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (250814678898394129482502636791522031913181/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (2004513432664841183101295216895967992832801/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2004513432664841183101295216895967992832801/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2828 BracketBatch0176.bracket2829 (2004513432664841183101295216895967992832801/20000000000000000000000000000000000000000) (1223084070061577201095620760981194442677/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2828 BracketBatch0176.bracket2829
  (2004513432664841183101295216895967992832801/20000000000000000000000000000000000000000) (1223084070061577201095620760981194442677/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2828
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2829
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1003258715593576517930010547166088127652721/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1003258715593576517930010547166088127652721/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1005270762341093384704810057278437072373113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1005270762341093384704810057278437072373113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0709.rows BesselBatch0709.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (1004264738967334951317410302222262600012917/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1004264738967334951317410302222262600012917/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2829 BracketBatch0176.bracket2830 (1004264738967334951317410302222262600012917/10000000000000000000000000000000000000000) (6118497923260091292158023719540252524377/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2829 BracketBatch0176.bracket2830
  (1004264738967334951317410302222262600012917/10000000000000000000000000000000000000000) (6118497923260091292158023719540252524377/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2829
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2830
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (100527076234109338470481005727843707237311/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (100527076234109338470481005727843707237311/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (503645452947325022242050575803852809895213/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (503645452947325022242050575803852809895213/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (125785104264733964324306950555383918260221/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (125785104264733964324306950555383918260221/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2830 BracketBatch0176.bracket2831 (125785104264733964324306950555383918260221/1250000000000000000000000000000000000000) (3060790873208100409989000715543948249469/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2830 BracketBatch0176.bracket2831
  (125785104264733964324306950555383918260221/1250000000000000000000000000000000000000) (3060790873208100409989000715543948249469/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2830
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2831
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1007290905894650044484101151607705619790423/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1007290905894650044484101151607705619790423/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0442.rows BesselBatch0442.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (126164899403357775250619385981442613704159/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126164899403357775250619385981442613704159/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0710.rows BesselBatch0710.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (403322020224302449297811247891849305884739/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (403322020224302449297811247891849305884739/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0353.rows ScalarLogs0353.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0176.bracket2831 BracketBatch0177.bracket2832 (403322020224302449297811247891849305884739/4000000000000000000000000000000000000000) (3062335921970731140512709637650966664661/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0176.bracket2831 BracketBatch0177.bracket2832
  (403322020224302449297811247891849305884739/4000000000000000000000000000000000000000) (3062335921970731140512709637650966664661/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2831
