module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0390
public import BecknerOnofri.EntropyScalarCertificate.Bessel0391
public import BecknerOnofri.EntropyScalarCertificate.Bessel0683
public import BecknerOnofri.EntropyScalarCertificate.Bessel0684
public import BecknerOnofri.EntropyScalarCertificate.Brackets0156
public import BecknerOnofri.EntropyScalarCertificate.Logs0312
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2496
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (65697947507545750720990639095854849267969/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (65697947507545750720990639095854849267969/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (329348557154552328577171841044517569605123/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (329348557154552328577171841044517569605123/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (82229786836535135272765629565473976993121/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (82229786836535135272765629565473976993121/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2496 BracketBatch0156.bracket2497 (82229786836535135272765629565473976993121/2500000000000000000000000000000000000000) (4429392442610903232062509962816758758359/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2496 BracketBatch0156.bracket2497
  (82229786836535135272765629565473976993121/2500000000000000000000000000000000000000) (4429392442610903232062509962816758758359/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2496
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2497
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (128651780138497003350457750408014675627/3906250000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (128651780138497003350457750408014675627/3906250000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (330211897083949258224019126576220600657081/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (330211897083949258224019126576220600657081/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0683.rows BesselBatch0683.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (659560454238501586801190967620738170262201/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (659560454238501586801190967620738170262201/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2497 BracketBatch0156.bracket2498 (659560454238501586801190967620738170262201/20000000000000000000000000000000000000000) (2216593462502430333746997254744833563263/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2497 BracketBatch0156.bracket2498
  (659560454238501586801190967620738170262201/20000000000000000000000000000000000000000) (2216593462502430333746997254744833563263/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2497
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2498
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (165105948541974629112009563288110300328539/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (165105948541974629112009563288110300328539/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (206924870691702800968198752874208257097/6250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (206924870691702800968198752874208257097/6250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (330645845095336869886568565587476906006139/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (330645845095336869886568565587476906006139/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2498 BracketBatch0156.bracket2499 (330645845095336869886568565587476906006139/10000000000000000000000000000000000000000) (2218495940817604173018952541038590810233/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2498 BracketBatch0156.bracket2499
  (330645845095336869886568565587476906006139/10000000000000000000000000000000000000000) (2218495940817604173018952541038590810233/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2498
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2499
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (331079793106724481549118004598733211355197/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (331079793106724481549118004598733211355197/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (331952281382315804777355150551721172971707/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (331952281382315804777355150551721172971707/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (82879009311130035790809144393806798040863/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (82879009311130035790809144393806798040863/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2499 BracketBatch0156.bracket2500 (82879009311130035790809144393806798040863/2500000000000000000000000000000000000000) (222040368348168173574293869420015401487/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2499 BracketBatch0156.bracket2500
  (82879009311130035790809144393806798040863/2500000000000000000000000000000000000000) (222040368348168173574293869420015401487/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2499
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2500
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (41494035172789475597169393818965146621463/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41494035172789475597169393818965146621463/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (83207349613453889353244812836271558842049/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (83207349613453889353244812836271558842049/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (6647816798361313621903344018968074083399/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6647816798361313621903344018968074083399/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2500 BracketBatch0156.bracket2501 (6647816798361313621903344018968074083399/200000000000000000000000000000000000000) (4444633435862765798954385929260316208903/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2500 BracketBatch0156.bracket2501
  (6647816798361313621903344018968074083399/200000000000000000000000000000000000000) (4444633435862765798954385929260316208903/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2500
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2501
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (332829398453815557412979251345086235368193/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (332829398453815557412979251345086235368193/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (66742236250614476221428367112243923754783/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66742236250614476221428367112243923754783/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (166635144926721984630030271726576463535527/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (166635144926721984630030271726576463535527/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2501 BracketBatch0156.bracket2502 (166635144926721984630030271726576463535527/5000000000000000000000000000000000000000) (556058767952863669820343313090372054443/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2501 BracketBatch0156.bracket2502
  (166635144926721984630030271726576463535527/5000000000000000000000000000000000000000) (556058767952863669820343313090372054443/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2501
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2502
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0390.rows BesselBatch0390.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (41713897656634047638392729445152452346739/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41713897656634047638392729445152452346739/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (167298833552937323573661783614238299994383/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (167298833552937323573661783614238299994383/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (334154424179473514127232701394848109381339/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (334154424179473514127232701394848109381339/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2502 BracketBatch0156.bracket2503 (334154424179473514127232701394848109381339/10000000000000000000000000000000000000000) (4452317545953421515716940402473712726143/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2502 BracketBatch0156.bracket2503
  (334154424179473514127232701394848109381339/10000000000000000000000000000000000000000) (4452317545953421515716940402473712726143/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2502
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2503
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (334597667105874647147323567228476599988763/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (334597667105874647147323567228476599988763/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0391.rows BesselBatch0391.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (335488893737217030377077008989622273519361/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (335488893737217030377077008989622273519361/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0684.rows BesselBatch0684.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (167521640210772919381100144054524718377031/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (167521640210772919381100144054524718377031/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0312.rows ScalarLogs0312.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0156.bracket2503 BracketBatch0156.bracket2504 (167521640210772919381100144054524718377031/5000000000000000000000000000000000000000) (4456175698988189993831507907457224961569/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0156.bracket2503 BracketBatch0156.bracket2504
  (167521640210772919381100144054524718377031/5000000000000000000000000000000000000000) (4456175698988189993831507907457224961569/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2503
