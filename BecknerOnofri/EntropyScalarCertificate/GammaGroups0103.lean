module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0128
public import BecknerOnofri.EntropyScalarCertificate.Bessel0129
public import BecknerOnofri.EntropyScalarCertificate.Bessel0130
public import BecknerOnofri.EntropyScalarCertificate.Bessel0553
public import BecknerOnofri.EntropyScalarCertificate.Brackets0051
public import BecknerOnofri.EntropyScalarCertificate.Brackets0052
public import BecknerOnofri.EntropyScalarCertificate.Logs0103
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0824
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (3215539738237248979825945705898710424247/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3215539738237248979825945705898710424247/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (100848714392970501921455635749838900607/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (100848714392970501921455635749838900607/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (6442698598812305041312526049893555243671/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6442698598812305041312526049893555243671/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0824 BracketBatch0051.bracket0825 (6442698598812305041312526049893555243671/20000000000000000000000000000000000000000) (1771373233398378323807609118610349079/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0824 BracketBatch0051.bracket0825
  (6442698598812305041312526049893555243671/20000000000000000000000000000000000000000) (1771373233398378323807609118610349079/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0824
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0825
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0128.rows BesselBatch0128.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (3227158860575056061486580343994844819421/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3227158860575056061486580343994844819421/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (3238790143688906137360057404103608331753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3238790143688906137360057404103608331753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (3232974502131981099423318874049226575587/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3232974502131981099423318874049226575587/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0825 BracketBatch0051.bracket0826 (3232974502131981099423318874049226575587/10000000000000000000000000000000000000000) (7180639406775246352970023688685570299/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0825 BracketBatch0051.bracket0826
  (3232974502131981099423318874049226575587/10000000000000000000000000000000000000000) (7180639406775246352970023688685570299/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0825
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0826
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (12955160574755624549440229616414433327/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12955160574755624549440229616414433327/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (3250433650732674496719386041179730966247/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3250433650732674496719386041179730966247/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (6489223794421580634079443445283339297997/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6489223794421580634079443445283339297997/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0826 BracketBatch0051.bracket0827 (6489223794421580634079443445283339297997/20000000000000000000000000000000000000000) (727676013835249567631574296330410357/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0826 BracketBatch0051.bracket0827
  (6489223794421580634079443445283339297997/20000000000000000000000000000000000000000) (727676013835249567631574296330410357/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0826
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0827
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (812608412683168624179846510294932741561/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (812608412683168624179846510294932741561/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (3262089445155465248701054473192064918611/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3262089445155465248701054473192064918611/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (1302504619177627949084088102874359176971/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1302504619177627949084088102874359176971/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0827 BracketBatch0051.bracket0828 (1302504619177627949084088102874359176971/4000000000000000000000000000000000000000) (1474772438058401483785602272537295193/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0827 BracketBatch0051.bracket0828
  (1302504619177627949084088102874359176971/4000000000000000000000000000000000000000) (1474772438058401483785602272537295193/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0827
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0828
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (203880590322216578043815904574504057413/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (203880590322216578043815904574504057413/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (409219698837983817514142105559977458573/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (409219698837983817514142105559977458573/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (816980879482416973601773914708985573399/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (816980879482416973601773914708985573399/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0828 BracketBatch0051.bracket0829 (816980879482416973601773914708985573399/2500000000000000000000000000000000000000) (7471952658008068631110140091634977407/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0828 BracketBatch0051.bracket0829
  (816980879482416973601773914708985573399/2500000000000000000000000000000000000000) (7471952658008068631110140091634977407/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0828
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0829
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (3273757590703870540113136844479819668581/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3273757590703870540113136844479819668581/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (3285438151424248834932665407628922738449/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3285438151424248834932665407628922738449/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (655919574212811937504580225210874240703/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (655919574212811937504580225210874240703/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0829 BracketBatch0051.bracket0830 (655919574212811937504580225210874240703/2000000000000000000000000000000000000000) (7571038670493524756113222445793458223/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0829 BracketBatch0051.bracket0830
  (655919574212811937504580225210874240703/2000000000000000000000000000000000000000) (7571038670493524756113222445793458223/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0829
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0830
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1642719075712124417466332703814461369223/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1642719075712124417466332703814461369223/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (3297131191665022456839942638167531622271/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3297131191665022456839942638167531622271/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (6582569343089271291772608045796454360717/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6582569343089271291772608045796454360717/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0830 BracketBatch0051.bracket0831 (6582569343089271291772608045796454360717/20000000000000000000000000000000000000000) (7671127390451807886181688543519497371/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0830 BracketBatch0051.bracket0831
  (6582569343089271291772608045796454360717/20000000000000000000000000000000000000000) (7671127390451807886181688543519497371/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0830
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0831
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0129.rows BesselBatch0129.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (824282797916255614209985659541882905567/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (824282797916255614209985659541882905567/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0130.rows BesselBatch0130.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (661767355215798919705805781344506911237/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (661767355215798919705805781344506911237/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0553.rows BesselBatch0553.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (6605967967744017055368971544890066178453/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6605967967744017055368971544890066178453/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0103.rows ScalarLogs0103.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0051.bracket0831 BracketBatch0052.bracket0832 (6605967967744017055368971544890066178453/20000000000000000000000000000000000000000) (7772226014429984885479495914431352571/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0051.bracket0831 BracketBatch0052.bracket0832
  (6605967967744017055368971544890066178453/20000000000000000000000000000000000000000) (7772226014429984885479495914431352571/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0831
