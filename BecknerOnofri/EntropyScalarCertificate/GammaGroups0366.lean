module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0457
public import BecknerOnofri.EntropyScalarCertificate.Bessel0458
public import BecknerOnofri.EntropyScalarCertificate.Bessel0717
public import BecknerOnofri.EntropyScalarCertificate.Bessel0718
public import BecknerOnofri.EntropyScalarCertificate.Brackets0183
public import BecknerOnofri.EntropyScalarCertificate.Logs0366
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2928
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1251253768890135693103881819280673271559469/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1251253768890135693103881819280673271559469/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (627193295750325754324133545403159823834333/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (627193295750325754324133545403159823834333/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (501128072078157440350429782017398583845627/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (501128072078157440350429782017398583845627/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2928 BracketBatch0183.bracket2929 (501128072078157440350429782017398583845627/4000000000000000000000000000000000000000) (1291727415105149296418762252578122972127/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2928 BracketBatch0183.bracket2929
  (501128072078157440350429782017398583845627/4000000000000000000000000000000000000000) (1291727415105149296418762252578122972127/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2928
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2929
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1254386591500651508648267090806319647668663/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1254386591500651508648267090806319647668663/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1257535156986181870461674439242423771796469/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1257535156986181870461674439242423771796469/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (627980437121708344777485382512185854866283/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (627980437121708344777485382512185854866283/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2929 BracketBatch0183.bracket2930 (627980437121708344777485382512185854866283/5000000000000000000000000000000000000000) (3231242828941928110664881658802557343493/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2929 BracketBatch0183.bracket2930
  (627980437121708344777485382512185854866283/5000000000000000000000000000000000000000) (3231242828941928110664881658802557343493/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2929
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2930
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (628767578493090935230837219621211885898233/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (628767578493090935230837219621211885898233/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (630349792155257997908338351110162623748233/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (630349792155257997908338351110162623748233/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (629558685324174466569587785365687254823233/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (629558685324174466569587785365687254823233/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2930 BracketBatch0183.bracket2931 (629558685324174466569587785365687254823233/5000000000000000000000000000000000000000) (6466343771973729426647208506313307098853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2930 BracketBatch0183.bracket2931
  (629558685324174466569587785365687254823233/5000000000000000000000000000000000000000) (6466343771973729426647208506313307098853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2930
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2931
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0457.rows BesselBatch0457.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1260699584310515995816676702220325247496463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1260699584310515995816676702220325247496463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (31596999840977438466550923098146122214931/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31596999840977438466550923098146122214931/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (2524579577949613534478713626146170136093703/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2524579577949613534478713626146170136093703/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2931 BracketBatch0183.bracket2932 (2524579577949613534478713626146170136093703/20000000000000000000000000000000000000000) (6470211461926714062929224500919235753221/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2931 BracketBatch0183.bracket2932
  (2524579577949613534478713626146170136093703/20000000000000000000000000000000000000000) (6470211461926714062929224500919235753221/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2931
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2932
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1263879993639097538662036923925844888597237/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1263879993639097538662036923925844888597237/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1267076506354235405276819858578402361209767/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1267076506354235405276819858578402361209767/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0717.rows BesselBatch0717.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (632739124998333235984714195626061812451751/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (632739124998333235984714195626061812451751/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2932 BracketBatch0183.bracket2933 (632739124998333235984714195626061812451751/5000000000000000000000000000000000000000) (6474088772159116519573489233897038885873/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2932 BracketBatch0183.bracket2933
  (632739124998333235984714195626061812451751/5000000000000000000000000000000000000000) (6474088772159116519573489233897038885873/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2932
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2933
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (316769126588558851319204964644600590302441/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (316769126588558851319204964644600590302441/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1270289245070546206711114312287104575678717/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1270289245070546206711114312287104575678717/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (2537365751424781611987934170865506936888481/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2537365751424781611987934170865506936888481/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2933 BracketBatch0183.bracket2934 (2537365751424781611987934170865506936888481/20000000000000000000000000000000000000000) (809746968421793608357370184141163343547/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2933 BracketBatch0183.bracket2934
  (2537365751424781611987934170865506936888481/20000000000000000000000000000000000000000) (809746968421793608357370184141163343547/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2933
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2934
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (635144622535273103355557156143552287839357/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (635144622535273103355557156143552287839357/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (159189791706329059232429784007263462308013/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (159189791706329059232429784007263462308013/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1271903789360589340285276292172606137071409/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1271903789360589340285276292172606137071409/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2934 BracketBatch0183.bracket2935 (1271903789360589340285276292172606137071409/10000000000000000000000000000000000000000) (40511702703531815221446035892267160487/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2934 BracketBatch0183.bracket2935
  (1271903789360589340285276292172606137071409/10000000000000000000000000000000000000000) (40511702703531815221446035892267160487/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2934
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2935
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1273518333650632473859438272058107698464101/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1273518333650632473859438272058107698464101/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0458.rows BesselBatch0458.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (63838194861050042260691950729004637067019/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63838194861050042260691950729004637067019/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0718.rows BesselBatch0718.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2550282230871633319073277286638200439804481/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2550282230871633319073277286638200439804481/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0366.rows ScalarLogs0366.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0183.bracket2935 BracketBatch0183.bracket2936 (2550282230871633319073277286638200439804481/20000000000000000000000000000000000000000) (3242889436507731838793750561307672527789/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0183.bracket2935 BracketBatch0183.bracket2936
  (2550282230871633319073277286638200439804481/20000000000000000000000000000000000000000) (3242889436507731838793750561307672527789/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2935
