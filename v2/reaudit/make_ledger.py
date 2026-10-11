#!/usr/bin/env python3
"""Build IMPLEMENTATION_STATUS_REAUDIT.csv: the 82-row ledger of 996404b with the 56 re-audit decisions
and four separate records per row (statement, written route, Lean compilation, axioms/kernel)."""
import csv, sys, json
base = '/home/user/v2wt/v2/IMPLEMENTATION_STATUS.csv'
dec  = '/mnt/project-files/v2/reaudit/input/extracted/beckner_v2_repository_reaudit_20261010T113542Z/decision_reaudit.csv'
old = {r['id']: r for r in csv.DictReader(open(base))}
decisions = {r['item']: r for r in csv.DictReader(open(dec))}
R = 'BecknerOnofri.V2.Reaudit.'
GENERIC_COMP = 'yes: clean full rebuild of all seven libraries, exit 0, 5890 jobs (logs/clean_full_build.log)'
GENERIC_AX = 'standard axioms only: scan of 4974 BecknerOnofri.V2 and SolutionRoute/SolutionV2 constants, union {propext, Classical.choice, Quot.sound}, 0 violations (logs/axiom_scan_v2.txt)'

# id -> dict(route, new, reused, wired, gaps, stmt(optional))
U = {}
def add(i, route, new='', reused='', wired='', gaps='', stmt=None):
    U[i] = dict(route=route, new=new, reused=reused, wired=wired, gaps=gaps, stmt=stmt)

ACC = 'Lean route accepted by decision; the written proof is replaced in the manuscript patch (ManuscriptPatch/fragments)'
for i, frag in [('S004','S004_U02.tex'),('U02','S004_U02.tex + U02_intro.tex'),('S005','S005.tex'),('S012','S012_A.tex, S012_B.tex'),
                ('U04','S012_A.tex (same lemma as S012)'),('S041','S041.tex'),('S045','S045_U09.tex'),('U09','S045_U09.tex'),('U22','U22.tex')]:
    add(i, ACC+' ('+frag+')', '', old[i]['resolved_lean_declarations'], 'not re-measured in this pass (declaration trace of the earlier delivery unchanged)',
        'Manuscript text must adopt the patch; no Lean obligation added by the decision.')
U['S045']['gaps'] = U['U09']['gaps'] = 'Unconditional modular identity: declaration trace (V2.ThetaTail.RouteM.twelve_square_routeM, Tn_le_Rn) has 0 forbidden-module hits and no sorry. The two classical theta formulas are proved by level-one modular-form uniqueness, not by the written Weierstrass-wp or triple-product steps (decided route difference); manuscript patch adopts the Lean route.'

add('S001','closed with difference, conditional on leaves (see S014-S016, S020-S023, S037, S043): Lean low-dimension assembly Mixtures.theorem_1_1_aligned and low_dim_* take the written-route leaves',
    R+'Mixtures.Assembly (theorem_1_1_aligned, low_dim_*)', 'V2.Section3.theorem_1_1_written; Final.low_dim_*',
    'yes: SolutionRoute.low_dim_* call Reaudit.Mixtures.low_dim_*; all 20 declarations of Mixtures.Assembly are reached from the 28 roots',
    'Section 3 module-level import closure still reaches Legacy LowDimensionMixtureEndpoint/EndpointThroughTen through V2.Vocab.Section2Bridge, FiniteEntropyPhysical, HeatRegularization (declaration trace: 0 forbidden-module hits, logs/traces/trace_lowdim.tsv). Conditional on U05/S015 partial status and on S006/U03 inputs where used.')
add('S002','statement-comparison and route aligned: Theorem 1.2 assembled from Section4 route declarations (prop41_route, prop49_route, strict_lower_route, theorem_1_2_route)',
    R+'Final.Section4; '+R+'Final.ManuscriptStatements.eleven_competitor_printed', 'V2.Eleven.theorem_1_2 (type-identical, via type_of%)',
    'yes: SolutionRoute.eleven_* are the *_route declarations; dim-11 closure (logs/traces/trace_eleven.tsv) has 0 forbidden hits and does not reach the old HighDim.Eleven.coexistence chain through ElevenCoexistence',
    'Both printed constants 8653/600 and 14475384292906/10^12 proved in eleven_competitor_printed. S032 Rellich/Adams strong convergence is a route difference (see S032).')
add('S003','partial: spectral part on written-route leaves; onset part still the C0 implicit function theorem route (Onset), not the Sobolev route',
    R+'Sobolev.*, '+R+'SobolevQuartic.*, '+R+'MorseBott.*, SpinChannel.WrittenEndpoint.high_dim_*_written', old['S003']['resolved_lean_declarations'],
    'high-dimensional spectral/threshold: yes via SpinChannel.WrittenEndpoint (12 of 24 declarations reached); onset: NO, Sobolev/MorseBott modules are not in the import closure of the 28 roots',
    'The H^s analytic IFT / embedded critical orbit / cosine correction / branch identification are proved standalone (S054, S055, S056, S057, U23) but high_dim_onset_branch, high_dim_pressure_onset, high_dim_defect_onset still use the old Onset chain. Pressure and defect parts of the branch interface are conditional on two named endpoint hypotheses.')
add('S006','closed with difference; finiteness of C(A_crit) conditional on V2.Vocab.CriticalAdamsInput',
    R+'Obstruction.* (10 files; tex/PROOF_S006)', 'V2.Section3 obstruction lemmas (earlier)', 'no: standalone package (Obstruction modules are not in the import closure of the 28 roots)',
    'Not consumed by final theorems. Differences: one-sided Mellin/Gaussian lower bound instead of the Robin-constant asymptotic; cube-indicator profile; first-shell entropy only as an upper bound t^2/4+2|t|^3.')
add('S007','external input: PositiveThresholdInput derived (positiveThreshold) as a corollary of the final threshold theorems, the reverse of the manuscript order; not an independent proof of the cited result',
    R+'ExternalInputs.PositiveThreshold', '', 'no: standalone (declaration closure of positiveThreshold has 0 forbidden hits, 111 V2.Section3 and 3941 Legacy constants)',
    'CdCRS2025 Thm 3 (beta_gm > 0) is not proved from first principles; the Lean derivation presupposes the low-dimension and dimension-11 assemblies.')
add('S009','closed with difference (Gibbs gap and Sobolev bootstrap on the printed route)', R+'Attainment.* (Pairing, GapIdentities, Correspondence, Regularity, Main)', '',
    'no: standalone package', 'Extremizers smooth only up to null sets; Euler-Lagrange as equality of Fourier coefficients; no weak convergence in H^{d/2}. Module imports reach EndpointThroughTen via V2.Vocab.Section2Bridge; declaration trace clean (attainment/trace_final.txt).')
add('S010','closed with difference (direct method)', R+'Attainment.Main (subcritical_attainment, exists_smooth_positive_minimizer)', '',
    'no: standalone package', 'Unconditional via CriticalAdamsAboveThreshold from the repository rough_bound (not re-audited); also stated under the printed CriticalAdamsInput.')
add('S011','closed with difference: Riesz inequality via the repository polarization proof, not Burchard-Hajaiej', R+'Obstruction.CircleRearrangementPrinted', '', 'no: standalone package', 'Citation-level route of the manuscript replaced by the repository proof; decision row asked for a precise citation, which is a manuscript change.')
add('U01','closed (printed entropy definition)', R+'Obstruction.PrintedEntropy (printedEntropy)', '', 'no: standalone package', '')
add('S014','closed (printed radial absolute-monotonicity route)', R+'HeatKernel.AbsMonotone, RadialExpansion, RadialTaylor, PositiveBernstein (positive_bernstein_multiindex, positive_bernstein, absMonotone_hasSum_taylor)', 'legacy closed_cube_expansion', 'no: standalone package', 'Not wired into Section 3 final chain.')
add('S015','NOT CLOSED, partial and conditional: positivity_step (one induction pass) with hypotheses hpos, hnn, hlt, symmetry, integral-operator representations, compactness, nonnegative fixed vector',
    R+'HeatKernel.PositivityStep', '', 'no: standalone package',
    'Trotter/Kato domination p_{B_alpha} <= p_{P_D}, Friedrichs operators, sine-system completeness, heat PDE, identification with the Friedrichs semigroup, Mellin representation of B^{-s}, potential domination for the csc^2 potential, 1-D Poincare/spectral gap, Lemma 2.10, Perron-Frobenius replacement for the Schur-test engine are not formalized.')
U['U05'] = dict(U['S015']); U['U05']['route']='partial: Dirichlet heat kernel by eigenfunction expansion with positivity via reflection and strict theta decrease (route difference: no parabolic comparison); domination step open'; U['U05']['new']=R+'HeatKernel.DirichletKernel, DirichletSemigroup, MixedKernel (dirichletKernel_pos, mixedKernel_pos, mixedKernel_lt_single)'
add('S016','closed with difference', R+'Mixtures.Selection (canonical_selection_written)', 'canonical_selection; coordinate_rearranged_minimizer', 'partial: 1 of 2 declarations of Mixtures.Selection reached from the 28 roots', '')
add('S018','external input: CircleLebedevMilinInput proved as circleLebedevMilin from Section3.circle_entropy_bound (legacy Milin/Euler recurrence); manuscript only cites Prop 2.2 of Mun-Rosenzweig',
    R+'ExternalInputs.CircleLM', 'V2.Section3.circle_entropy_bound', 'no: standalone; closure clean (0 forbidden hits)', 'No written proof exists in the manuscript for this lemma (cited result).')
add('S020','closed with difference (retained-shell certificate; kernel check uses legacy reciprocalUnits weights, transferred by retainedShellBound_mono; (3,2) legacy 388736063998 vs least 388736063997)',
    R+'ShellMargins.* (scalar_gap_171, dimension_two_large_printed, retainedShellBound)', 'Legacy FiniteScalar, LowScalarFull, ...', 'no: ShellMargins modules are not in the import closure of the 28 roots',
    'Certificate proved in parallel; final chain still uses the earlier certificates. Machin identity not formalized (needed bound proved from Mathlib pi_gt_d20).')
add('S021','closed: artanh series (lemma_3_5_artanh) and gaussian_binomial_printed; body of V2.Section3.lemma_3_5 replaced', R+'ScalarBridges.GaussianBinomial', 'V2.Section3.Scalar', 'no: V2.Section3.Scalar is not in the import closure of the 28 roots (lemma_3_5 not on the final path)', 'Replacement is type-preserving and compiled, but the module is not used by the final theorems.')
add('S022','closed (lem_theta_integral_certificate : thetaIntegral 10 <= 41/25; extra e^A factor refuted by shell_integral_extra_factor_false)', R+'ShellMargins.Theta', 'Legacy ThetaIntegralBound', 'no: standalone', '')
add('S023','closed with difference (chain rule at random-variable level; mixture_strict_entropy_gap 3/(2200 d))', R+'Mixtures.ChainRule, PrintedGap', 'V2.Section3.MixtureCountable', 'yes: Section3.MixtureCountable.axis_marginal_bound uses axis_marginal_bound_chain; 7 of 8 declarations reached from SolutionRoute roots', '')
add('U06','closed with difference (quantitative gap present as mixture_strict_entropy_gap)', R+'Mixtures.PrintedGap', '', 'partial: 5 of 22 declarations reached from SolutionV2 roots, 17 from SolutionRoute roots', '')
add('S024','closed: mixture_gap_eleven (printed 1/44000), smoothMixtureGap11_quantitative, uniform_unique_quantitative, beta0_le_globalTransition_quantitative', R+'ElevenBounds.LatentGap, GapParam, Interval', '', 'yes: strict_lower_route uses beta0_le_globalTransition_quantitative and uniform_unique_quantitative; LatentGap 26 of 26 reached', 'Dimension-11 non-strict bound / coexistence / strict bound trace: 0 forbidden-module hits (logs/traces/trace_eleven.tsv).')
add('S025','closed (entropy_bound_via_rv, entropy_bound_printed, torusEntropy_bound_printed)', R+'ElevenBounds.EntropyBound, LabelEntropy', '', 'yes: periodized_entropy_fine_route (3 of 5 EntropyBound declarations reached)', '')
add('S026','partial earlier; chain rule now at random-variable level via S028', R+'ElevenBounds.LabelChain, MutualInfo', '', 'LabelChain 11 of 11 reached; MutualInfo 0 of 11', 'Identification of JointLaw.shannonEntropy with the old labelEntropy still optional.')
add('S028','closed (condShannon_lt_printed, chain_rule_rv)', R+'ElevenBounds.LabelChain, LabelEntropy', '', 'yes: used by periodized_entropy_fine_route', '')
add('S029','closed with difference: full shell equality (hasSum_shell_expansion, energy_bound_via_shells) and the half-integer Bessel closed form (besselK_half_eleven, eta_fourier_bessel) are proved', R+'ElevenBounds.ShellExpansion, Bessel', '', 'partial: ShellExpansion 13 of 16 reached; Bessel 0 of 24 reached from the 28 roots', 'Bessel closed forms proved but not on the final path.')
add('S030','closed with difference (same retained-shell certificate as S020, omitted mass included; d11_scalar_gap_finite margin 111/200000, d11_coupling_factor)', R+'ShellMargins.RetainedShell, Checks', '', 'no: standalone', 'Checks.lean needs about 6 minutes and 5.4 GB; build it alone.')
add('S031','closed with difference (local_uniqueness_raw)', R+'Sobolev.LocalUniqueness', '', 'yes: 7 of 20 declarations reached through Compactness.prop49_manuscript', '')
add('S032','closed (Radon-Riesz, Vitali, Rellich; coexistence_with_convergence, coexistence, strict_lower_of_coexistence_manuscript in the U07 order, prop49_manuscript)', R+'Compactness.*', '', 'yes: all Compactness modules reached (prop49_route)', 'The closure of Compactness.coexistence reaches only generic OnsetWienerBounds.radialSize.')
add('U07','closed: dependency order explicit (strict_lower_of_coexistence_manuscript)', R+'Compactness.Coexistence', '', 'yes (3 of 4 declarations reached)', '')
add('S037','closed (spectral_marginal_energy_deletion_direct, _subset_direct)', R+'Mixtures.DirectTransfer, DirectRectangle', 'V2.Transfer.DimensionTransfer', 'yes: DimensionTransfer bodies call the direct versions', '')
add('S043','closed (harmonic_identity_printed, Rn_eq_positive_printed, layer_cake_permutation_comparison, tail_arbitrary_indices_direct, singular_fourier_tail_direct)', R+'Mixtures.HarmonicRecurrence, LayerCake, CountableTail, Radii', 'V2.Assembly.GlobalGap', 'yes: GlobalGap uses singular_fourier_tail_direct', 'TeX: workers/Mixtures/tex/PROOF_S043_layer_cake')
add('S040','closed (high_endpoint_written, high_dim_*_written; high_endpoint_written d hd = Final.Unconditional.high_endpoint by rfl)', R+'SpinChannel.WrittenEndpoint', 'V2.Final.Unconditional', 'yes: SolutionRoute.high_dim_* call high_dim_*_written; unconditional high-dimensional trace has 0 forbidden-module hits (logs/traces/trace_highdim.tsv)', '')
add('S044','closed with difference for part (i) (spin_entropy_jointLaw, spin_entropy_comparison_i_joint)', R+'SpinChannel.JointLaw, Prop512Joint, Conditional, Tower', 'V2.Channel.Prop512', 'yes: GlobalGap calls spin_entropy_comparison_i_joint', '')
add('U15','closed (nested_binaryCost_eq_expect, channel_entropy_le_conditional_joint, relEntropy_spinLaw_eq_spinRelEntropy)', R+'SpinChannel.*', '', 'yes (via S044)', '')
add('S051','partly: calculus versions feasible_printed stated but not wired (import cycle with FiniteState FamilyBounds/FamilyJensen upstream of FeasibleCalculus)', R+'ScalarBridges.FeasibleCalculus', 'V2.FiniteState.* (old route)', 'no: not in the import closure', 'Old famBias_bounds routes remain on the final path.')
add('S052','closed (perturb_printed, gibbs_variational_printed)', R+'ScalarBridges.VarianceChain', 'V2.Interval.FamilyScalar; V2.Assembly.CountForm', 'yes: both call perturb_printed (11 of 12 declarations reached)', '')
add('U17','closed (mgflower, log_integral_exp_le)', R+'ScalarBridges.VarianceChain', '', 'partly: shares the module reached for S052', '')
add('U19','closed (Krawtchouk bridges moment_one_spins, famOmega_sub_isBigO_four; TeX PROOF_U19_krawtchouk)', R+'ScalarBridges.KrawtchoukOrthogonality, OriginReflection', 'V2.FiniteState.OriginOrthogonality, OriginEntropy', 'yes: Origin* modules call the *_spins/_reflection bridges (33 of 39 and 5 of 5 reached)', '')
for i, frag in [('S053','S053.tex'),('U20','U20.tex'),('U21','U21.tex')]:
    add(i, 'hybrid: readable interval proof retained in print and the kernel-checked implementation documented ('+frag+')', '', old[i]['resolved_lean_declarations'], 'yes: IntervalKernel hc1-hc3 in Final.Unconditional (unchanged)', 'Manuscript patch adopts the hybrid text.')
add('S054','closed with difference (route only): Banach-algebra Sobolev space, analytic Gibbs map, implicit function theorem; section5_quartic_reduction_native', R+'SobolevQuartic.*, '+R+'Sobolev.Space, GibbsMap', 'V2.Onset (C0 IFT)', 'no: not consumed by high_dim_onset_branch (Onset still the C0 route)', 'Statement identical to Sobolev.Section5QuarticReduction d s (graph hd11) via the bridge section5_quartic_reduction_native\'.')
add('S055','closed with difference: embedded critical orbit (embeddedCriticalOrbit_of_fullMode, full_branch_embedded_orbit) fills the Morse-Bott manifold clause; analytic classification kept', R+'MorseBott.EmbeddedOrbit, CriticalSet, Tangent, OrbitMap, FullBranch', '', 'no: standalone', 'Morse-Bott manifold clause proved; not wired into the onset theorems.')
add('S056','hybrid/conditional: common branch (BranchIdentification, BranchInterface); pressure and derivative parts conditional on two named endpoint hypotheses (CoefficientEndpoint, DensityRigidity)', R+'MorseBott.BranchIdentification, BranchInterface, BranchRemainder', '', 'no: standalone', 'tex/NOTE_branch_interface; endpoint hypotheses not discharged.')
add('S057','closed with difference, conditional as S056 (analytic cubic remainder, one-sided derivatives)', R+'MorseBott.PressureDifferentiation, AnalyticRemainder', '', 'no: standalone', '')
add('U23','closed: cosine_correction_display, cosine_correction_kappa and the full Morse-Bott assertion', R+'MorseBott.CosineCorrection (lift renamed cosLift to avoid a duplicate declaration)', '', 'no: standalone', 'tex/PROOF_embedded_orbit.')
add('U03','external input: criticalAdams (hd : 0 < d) : CriticalAdamsInput d re-runs the Adams chain with the d=1 input from Legacy endpoint_one (Milin/Euler recurrence) instead of physical_green_endpoint',
    R+'ExternalInputs.CriticalAdams (critical_adams_bound_indep, circle_heatInteraction_entropy_indep, criticalAdams)', 'Legacy.BecknerOnofri.endpoint_one', 'no: standalone; closure of criticalAdams has 0 forbidden-module hits while HighDim.critical_adams_bound has 17 (via circle_heatInteraction_entropy -> physical_green_endpoint -> endpoint_through_ten)',
    'The final theorems still use the old critical_adams_bound chain; not re-routed. Sharp constant not an independent re-proof of the cited inequality.')
add('U24','external inputs: all three named propositions have Lean proofs (circleLebedevMilin, criticalAdams, positiveThreshold); positiveThreshold is derived from the final theorems (reverse order)', R+'ExternalInputs.*', '', 'no: standalone', 'See S007 and U03.')

STATEMENT_NOTE = 'carried from 996404b ledger; for the 28 Challenge theorems the pp.all type is identical in Challenge, Solution and SolutionRoute (statement_comparison/*.types)'
cols = ['id','source_label','reaudit_decision','reaudit_reason','statement_alignment','written_route_alignment','lean_compilation','axiom_kernel_check',
        'new_declarations_this_pass','reused_declarations','reached_from_final_theorems','remaining_gaps','previous_route_status_996404b']
w = csv.writer(open(sys.argv[1],'w',newline=''))
w.writerow(cols)
for i, o in old.items():
    d = decisions.get(i); u = U.get(i)
    if u is None:
        route = 'not in the 56 re-audit rows; carried forward unchanged: ' + o['proof_route_alignment'][:400]
        new = ''; reused = o['resolved_lean_declarations']; wired = 'not re-measured'; gaps = o['remaining_obligations']; stmt = o['statement_alignment']
    else:
        route = u['route']; new = u['new']; reused = u['reused']; wired = u['wired']; gaps = u['gaps']; stmt = u['stmt'] or o['statement_alignment']
    w.writerow([i, o['source_label'], d['decision'] if d else 'not re-audited', d['reason'] if d else '', stmt, route,
                GENERIC_COMP, GENERIC_AX, new, reused, wired, gaps, o['proof_route_alignment'][:300]])
missing = [i for i in decisions if i not in old]
print('rows', len(old), 'decisions', len(decisions), 'decision ids not in old ledger:', missing, 'undefined mapping for decisions:', [i for i in decisions if i not in U])
