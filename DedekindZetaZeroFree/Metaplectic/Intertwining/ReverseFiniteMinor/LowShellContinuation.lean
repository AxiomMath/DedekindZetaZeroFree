module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseOperatorEvaluation

@[expose] public section

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorTestIntegral
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

def testCompact (f : sectionSpace S.borel P .minus 0) :
    compactPicture S.borel P S.iwasawa .minus :=
  (compactTrivialization S.borel P S.iwasawa .minus 0).symm f

def testDeformation (f : sectionSpace S.borel P .minus 0) (s : ℂ) :
    sectionSpace S.borel P .minus (sourceParameter .minus s) :=
  compactTrivialization S.borel P S.iwasawa .minus (sourceParameter .minus s)
    (testCompact F ζ hζ q S P f)

def actualTestFamily (f : sectionSpace S.borel P .minus 0) (s : ℂ) :
    sectionSpace S.borel P .plus (targetParameter .minus s) :=
  transportToSections (LocalField F q) S.borel P S.iwasawa .minus s
    (actualCanonicalContinued F q ζ hζ S P μ hμ .minus s)
    (testDeformation F ζ hζ q S P f s)

theorem actual_test_family_zero
    (f : sectionSpace S.borel P .minus 0)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((actualTestFamily F ζ hζ q S P μ hμ f 0).val g).val h =
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f).val g).val h := by
  have hs : sourceParameter .minus (0 : ℂ) = 0 := by norm_num [sourceParameter]
  have ht : targetParameter .minus (0 : ℂ) = 0 := by
    norm_num [targetParameter, sourceParameter]
  unfold actualTestFamily testDeformation testCompact transportToSections
  simp only [sourceSign, targetSign, id_eq]
  rw [ht, hs]
  change ((compactTrivialization S.borel P S.iwasawa .plus 0
    (actualCanonicalContinued F q ζ hζ S P μ hμ .minus 0
      ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
        (compactTrivialization S.borel P S.iwasawa .minus 0
          ((compactTrivialization S.borel P S.iwasawa .minus 0).symm f))))).val g).val h = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem actual_test_family_chamber
    (f : sectionSpace S.borel P .minus 0) (s : ℂ)
    (hs : convergenceHalfPlane .minus s)
    (g : ActualCover F ζ hζ q) (h : actualTorus F ζ hζ q) :
    ((actualTestFamily F ζ hζ q S P μ hμ f s).val g).val h =
      ∫ u : LocalField F q,
        ((testDeformation F ζ hζ q S P f s).val
          (kernelW (LocalField F q) S.borel .minus *
            S.borel.upperRoot (Multiplicative.ofAdd u) * g)).val h ∂μ := by
  exact actualCanonicalContinued_chamber F q ζ hζ S P μ hμ .minus s hs
    (testCompact F ζ hζ q S P f) g h

end DedekindZetaZeroFree.ActualReverseMinorTestIntegral

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.ActualReverseMinorLowShell
open scoped NumberField Valued Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Set Filter
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneShellRepair KPRankOneRootParameter
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testCompact → testCompact
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming testDeformation → testDeformation
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actualTestFamily → actualTestFamily
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_zero → actual_test_family_zero
open _root_.DedekindZetaZeroFree.ActualReverseMinorTestIntegral renaming actual_test_family_chamber → actual_test_family_chamber
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

 abbrev lowShell : Set (LocalField F q) :=
  ((valuation (LocalField F q)).integer : Set (LocalField F q))

private theorem finite_family_integral {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (H : X → ℂ → ℂ) (hH : IsLocallyConstant H) (s : ℂ) :
    ∫ x, H x s ∂μ = ∑ y ∈ hH.range_finite.toFinset, μ.real (H ⁻¹' {y}) • y s := by
  classical
  let D := hH.range_finite.toFinset
  have hm (y : ℂ → ℂ) : MeasurableSet (H ⁻¹' {y}) := (hH.isOpen_fiber y).measurableSet
  have hi (y : ℂ → ℂ) : Integrable ((H ⁻¹' {y}).indicator (fun _ => y s)) μ :=
    (integrable_const _).indicator (hm y)
  have he (x : X) : H x s = ∑ y ∈ D, (H ⁻¹' {y}).indicator (fun _ => y s) x := by
    rw [Finset.sum_eq_single (H x)]
    · simp
    · intro y hy hne
      simp [Set.indicator_of_notMem, hne.symm]
    · intro hx
      exact False.elim (hx (hH.range_finite.mem_toFinset.mpr ⟨x, rfl⟩))
  simp_rw [he]
  rw [integral_finsetSum D (fun y _ => hi y)]
  exact Finset.sum_congr rfl (fun y _ => integral_indicator_const _ (hm y))
theorem numerator_family
    (f : sectionSpace S.borel P .minus 0) :
    ∃ H : ActualCover F ζ hζ q → ℂ → ℂ,
      IsLocallyConstant H ∧ (∀ g, Differentiable ℂ (H g)) ∧
      (∀ s, denominator (LocalField F q) .minus s ≠ 0 → ∀ g,
        H g s = denominator (LocalField F q) .minus s *
          ((actualTestFamily F ζ hζ q S P μ hμ f s).val g).val 1) := by
  let φ₀ := (compactTrivialization S.borel P S.iwasawa .minus 0).symm
    f
  let f₀ := f
  obtain ⟨U, hU⟩ := f₀.property.2
  let J : CompactOpenLevel (ActualCover F ζ hζ q) :=
    ⟨U ⊓ S.iwasawa.compact.toOpenSubgroup,
      S.iwasawa.compact.isCompact.of_isClosed_subset
        (U ⊓ S.iwasawa.compact.toOpenSubgroup).isClosed (fun _ hg => hg.2)⟩
  have hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup := fun _ hg => hg.2
  have hφ : φ₀ ∈ compactLevel S.borel P S.iwasawa .minus J := by
    apply (compact_level_identification S.borel P S.iwasawa .minus J hJ 0 φ₀).mpr
    simp only [φ₀, LinearEquiv.apply_symm_apply]
    intro j
    apply Subtype.ext
    exact hU j j.property.1
  let φ : compactLevel S.borel P S.iwasawa .minus J := ⟨φ₀, hφ⟩
  let p := actualCanonicalLevelNumerator F ζ hζ q S P J hJ μ hμ .minus
  let H : ActualCover F ζ hζ q → ℂ → ℂ := fun g s =>
    ∑ n ∈ p.support, (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n *
      ((compactTrivialization S.borel P S.iwasawa .plus s
        (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus)).val g).val 1
  refine ⟨H, ?_, ?_, ?_⟩
  · apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro g
    have hn : ∀ᶠ g' in 𝓝 g, g⁻¹ * g' ∈ J.toOpenSubgroup :=
      (J.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
        (by simp)
    filter_upwards [hn] with g' hg'
    funext s
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    have hh := (compact_level_identification S.borel P S.iwasawa .plus J hJ s
      (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus)).mp ((p n) φ).property
    have he := congrArg (fun v : sectionSpace S.borel P .plus s => (v.val g).val 1)
      (hh ⟨g⁻¹ * g', hg'⟩)
    simpa [principalSeries, vectorRightTranslation, Representation.subrepresentation_apply] using he
  · intro g
    apply Differentiable.fun_sum
    intro n hn
    apply Differentiable.mul
    · apply Differentiable.zpow _ (Or.inl (fun s => Units.ne_zero _))
      change Differentiable ℂ (fun s => (r (LocalField F q) s)⁻¹)
      apply Differentiable.inv _ (fun s => Complex.exp_ne_zero _)
      fun_prop
    · have hh := compact_level_holomorphic S.borel P S.iwasawa .plus J hJ ((p n) φ) g 1 1
      simpa [principalSeries, vectorRightTranslation, Representation.subrepresentation_apply] using hh
  · intro s hs g
    have hc := actualCanonicalContinued_eq_level F q ζ hζ S P μ hμ .minus s J hJ φ
    have he := congrArg (fun v : compactPicture S.borel P S.iwasawa .plus =>
      ((compactTrivialization S.borel P S.iwasawa .plus s v).val g).val 1) hc
    have hr : ((actualTestFamily F ζ hζ q S P μ hμ f s).val g).val 1 =
      ((compactTrivialization S.borel P S.iwasawa .plus s
        (actualCanonicalContinued F q ζ hζ S P μ hμ .minus s φ₀)).val g).val 1 := by
      unfold actualTestFamily testDeformation testCompact transportToSections
      simp only [LinearMap.comp_apply, sourceSign, targetSign]
      change ((compactTrivialization S.borel P S.iwasawa .plus
        (targetParameter .minus s)
        (actualCanonicalContinued F q ζ hζ S P μ hμ .minus s
          ((compactTrivialization S.borel P S.iwasawa .minus
            (sourceParameter .minus s)).symm
            (compactTrivialization S.borel P S.iwasawa .minus
              (sourceParameter .minus s) φ₀)))).val g).val 1 = _
      rw [LinearEquiv.symm_apply_apply]
      change (inducingAction S.borel P .plus (- -s) (S.iwasawa.borelPart g)
        ((actualCanonicalContinued F q ζ hζ S P μ hμ .minus s φ₀).val
          (S.iwasawa.compactPart g))).val 1 =
        (inducingAction S.borel P .plus s (S.iwasawa.borelPart g)
          ((actualCanonicalContinued F q ζ hζ S P μ hμ .minus s φ₀).val
            (S.iwasawa.compactPart g))).val 1
      rw [neg_neg]
    rw [hr, he]
    have hv : ((continuedLevel (LocalField F q) S.borel P S.iwasawa J .minus p s φ).val :
        compactPicture S.borel P S.iwasawa .plus) =
        (denominator (LocalField F q) .minus s)⁻¹ •
          ∑ n ∈ p.support, (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n •
            (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus) := by
      simp only [continuedLevel, evaluate, Finsupp.sum, LinearMap.smul_apply,
        LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum]
    rw [hv]
    change H g s = denominator (LocalField F q) .minus s *
      (((compactTrivialization S.borel P S.iwasawa .plus s).toLinearMap
        ((denominator (LocalField F q) .minus s)⁻¹ •
          ∑ n ∈ p.support, (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n •
            (((p n) φ).val : compactPicture S.borel P S.iwasawa .plus))).val g).val 1
    simp only [map_smul, map_sum, Submodule.coe_smul, Submodule.coe_sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [H]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
private theorem outer_family
    (f : sectionSpace S.borel P .minus 0) (a : ActualCover F ζ hζ q) :
    ∃ B : ℂ → ℂ, Differentiable ℂ B ∧ ∀ s, denominator (LocalField F q) .minus s ≠ 0 →
      B s = denominator (LocalField F q) .minus s *
        ∫ x in lowShell F q, ((actualTestFamily F ζ hζ q S P μ hμ f s).val
          (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
            KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ := by
  obtain ⟨H, hH, hdH, heH⟩ := numerator_family F ζ hζ q S P μ hμ f
  let O : Set (LocalField F q) := lowShell F q
  letI : CompactSpace O := by
    apply isCompact_iff_compactSpace.mp
    exact IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1
  have hO : MeasurableSet (lowShell F q) := (valuation (LocalField F q)).isOpen_integer.measurableSet
  let ν := μ.comap (Subtype.val : O → LocalField F q)
  letI : IsFiniteMeasure (μ.restrict (lowShell F q)) := isFiniteMeasure_restrict.mpr (by simp [lowShell, hμ])
  letI : IsFiniteMeasure ν := ⟨by
    change μ.comap (Subtype.val : O → LocalField F q) Set.univ < ⊤
    rw [comap_subtype_coe_apply (show MeasurableSet (O : Set (LocalField F q)) from hO) μ Set.univ]
    simpa [O, lowShell, hμ]⟩
  let g : O → ActualCover F ζ hζ q := fun x => a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
    KPPGLLocalCover.N F ζ hζ (Sum.inr q) x
  have hg : Continuous g := by
    have hn : Continuous (fun x : LocalField F q => KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) := by
      have he := (S.openCell P).upper_eq
      have hc := continuous_subtype_val.comp (S.borel.upperRoot_continuous.comp continuous_ofAdd)
      change Continuous (fun x : LocalField F q =>
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)) at hc
      simpa only [he, KPRankOneOpenCellKernel.nLift] using hc
    exact continuous_const.mul (hn.comp continuous_subtype_val)
  have hG : IsLocallyConstant (H ∘ g) := hH.comp_continuous hg
  let B : ℂ → ℂ := fun s => ∑ y ∈ hG.range_finite.toFinset, ν.real ((H ∘ g) ⁻¹' {y}) • y s
  refine ⟨B, ?_, ?_⟩
  · apply Differentiable.fun_sum
    intro y hy
    obtain ⟨x, rfl⟩ := hG.range_finite.mem_toFinset.mp hy
    exact (hdH (g x)).const_smul (ν.real ((H ∘ g) ⁻¹' {(H ∘ g) x}))
  · intro s hs
    dsimp only [B]
    rw [← finite_family_integral ν (H ∘ g) hG s]
    simp only [Function.comp_apply]
    simp_rw [heH s hs]
    rw [integral_const_mul]
    congr 1
    exact integral_subtype_comap hO (fun x =>
      ((actualTestFamily F ζ hζ q S P μ hμ f s).val
        (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1)

theorem actual_lowShell_continuation_of_numerator
    (a : ActualCover F ζ hζ q)
    (f : sectionSpace S.borel P .minus 0) (p : ℤ →₀ ℂ)
    (hp : ∀ s : ℂ, convergenceHalfPlane .minus s →
      denominator (LocalField F q) .minus s *
        (∫ x in lowShell F q, ∫ u : LocalField F q,
          ((testDeformation F ζ hζ q S P f s).val
            (kernelW (LocalField F q) S.borel .minus *
              S.borel.upperRoot (Multiplicative.ofAdd u) *
              (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
                KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 ∂μ ∂μ) =
        p.sum (fun n c => (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n * c)) :
    ∫ x in lowShell F q,
      ((actualCanonicalReverseMap F ζ hζ q S P μ hμ f).val
        (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)).val 1 ∂μ =
      (denominator (LocalField F q) .minus 0)⁻¹ * p.sum (fun _ c => c) := by
  obtain ⟨B, hB, heB⟩ := outer_family F ζ hζ q S P μ hμ f a
  let Q : ℂ → ℂ := fun s => p.sum
    (fun n c => (evaluationUnit (LocalField F q) .minus s : ℂ) ^ n * c)
  have hQ : Differentiable ℂ Q := by
    apply Differentiable.fun_sum
    intro n hn
    apply Differentiable.mul _ (differentiable_const _)
    apply Differentiable.zpow _ (Or.inl (fun s => Units.ne_zero _))
    change Differentiable ℂ (fun s => (r (LocalField F q) s)⁻¹)
    apply Differentiable.inv _ (fun s => Complex.exp_ne_zero _)
    fun_prop
  have hch : ∀ s, convergenceHalfPlane .minus s → B s = Q s := by
    intro s hs
    rw [heB s (denominator_ne_zero_of_convergence (LocalField F q) .minus s hs)]
    dsimp only [Q]
    rw [← hp s hs]
    congr 1
    apply setIntegral_congr_fun (valuation (LocalField F q)).isOpen_integer.measurableSet
    intro x hx
    exact actual_test_family_chamber F ζ hζ q S P μ hμ f s hs _ 1
  have hev : B =ᶠ[𝓝 (-1 : ℂ)] Q := by
    have hn : ∀ᶠ s : ℂ in 𝓝 (-1 : ℂ), s.re < -(1 / 6 : ℝ) :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by norm_num)
    filter_upwards [hn] with s hs
    exact hch s hs
  have he := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun s _ => hB.analyticAt s) (fun s _ => hQ.analyticAt s)
    isPreconnected_univ (Set.mem_univ (-1 : ℂ)) hev (Set.mem_univ (0 : ℂ))
  have hd := denominator_ne_zero_at_zero (LocalField F q) .minus
  rw [heB 0 hd] at he
  have hQ0 : Q 0 = p.sum (fun _ c => c) := by
    simp [Q, evaluationUnit, rUnit, r]
  rw [hQ0] at he
  simp_rw [actual_test_family_zero F ζ hζ q S P μ hμ f] at he
  rw [← he, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

end DedekindZetaZeroFree.ActualReverseMinorLowShell

end

end
