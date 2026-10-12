module

public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.TameNormalizedCharacterExtension
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.ConjugatedBorelChartsAndCharacterRatios
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TorusValuedSectionReconstruction
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.TameCubicHilbertDetection

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLowShellSupport

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates KPTameTransposeKernelUnfoldingRaw

set_option backward.isDefEq.respectTransparency false in

theorem minusTest_unit_eigen_of_chart_normalization
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (a t : ActualCover F ζ hζ q) (m : ℕ)
    (hnormalW : ∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m)
    (hnormalT : ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      t⁻¹ * k * t ∈ splitCongruenceSet F ζ hζ q m)
    (b : BL F ζ hζ q S P)
    (hb : a * KPPGLLocalCover.W F ζ hζ (Sum.inr q) * t =
      b * (a * KPPGLLocalCover.W F ζ hζ (Sum.inr q)))
    (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) :
    ∀ x, f.val (x * t) = chi F ζ hζ q S P hP .minus b * f.val x := by
  let w := KPPGLLocalCover.W F ζ hζ (Sum.inr q)
  have hfixed (k) (hk : k ∈ splitCongruenceSet F ζ hζ q m) (x) :
      f.val (x * k) = f.val x :=
    congrArg (fun v : scalarSections F ζ hζ q S P hP .minus => v.val x) (hf.1 k hk)
  have hinSupport (x) (hx : x ∈ testSupport F ζ hζ q S P a m) :
      f.val (x * t) = chi F ζ hζ q S P hP .minus b * f.val x := by
    obtain ⟨c, k, hk, rfl⟩ := hx
    let k' := w⁻¹ * k * w
    have hk' : k' ∈ splitCongruenceSet F ζ hζ q m := hnormalW k hk
    have he : (c : ActualCover F ζ hζ q) * a * k * w = c * (a * w) * k' := by dsimp [k']; group
    change f.val ((c : ActualCover F ζ hζ q) * a * k * w * t) = _
    rw [he]
    have he' : (c : ActualCover F ζ hζ q) * (a * w) * k' * t =
        c * ((a * w) * t) * (t⁻¹ * k' * t) := by group
    rw [he', hfixed _ ((hnormalT k').mp hk'), hb, f.property.1,
      f.property.1, hfixed k' hk', f.property.1]
    ring
  intro x
  by_cases hx : x ∈ testSupport F ζ hζ q S P a m
  · exact hinSupport x hx
  · have hx0 : f.val x = 0 := by by_contra h; exact hx (hf.2.1 h)
    rw [hx0, mul_zero]
    by_contra hxt
    obtain ⟨c, k, hk, he⟩ := hf.2.1 hxt
    let k' := w⁻¹ * k * w
    have hk' : k' ∈ splitCongruenceSet F ζ hζ q m := hnormalW k hk
    have he' : x * t = c * (a * w) * k' := by rw [he]; dsimp [k', w]; group
    have hb' : (a * w) * t⁻¹ = (b⁻¹ : BL F ζ hζ q S P) * (a * w) := by
      change (a * w) * t⁻¹ = (b : ActualCover F ζ hζ q)⁻¹ * (a * w)
      apply (mul_left_cancel (a := (b : ActualCover F ζ hζ q)))
      calc
        _ = ((b : ActualCover F ζ hζ q) * (a * w)) * t⁻¹ := by group
        _ = a * w := by rw [← hb]; dsimp [w]; group
        _ = _ := by group
    let k'' := t * k' * t⁻¹
    have hk'' : k'' ∈ splitCongruenceSet F ζ hζ q m := by
      apply (hnormalT k'').mpr
      convert hk' using 1 <;> dsimp [k''] <;> group
    have hWeq : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using KPPGLLocalCover.W_sq F ζ hζ (Sum.inr q))
    have hWk : w * k'' * w⁻¹ ∈ splitCongruenceSet F ζ hζ q m := by
      have h := hnormalW k'' hk''
      change w⁻¹ * k'' * w ∈ _ at h
      simpa only [hWeq] using h
    apply hx
    refine ⟨c * b⁻¹, w * k'' * w⁻¹, hWk, ?_⟩
    calc
      x = (x * t) * t⁻¹ := by group
      _ = ((c : ActualCover F ζ hζ q) * (a * w) * k') * t⁻¹ := by rw [he']
      _ = (c : ActualCover F ζ hζ q) * ((a * w) * t⁻¹) * k'' := by dsimp [k'']; group
      _ = _ := by rw [hb']; simp only [Subgroup.coe_mul, Subgroup.coe_inv]; dsimp [w]; group

set_option backward.isDefEq.respectTransparency false in
theorem compact_normalizes_splitCongruenceSet
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m)
    (g : KPTameCompact.K0 F q) :
    ∀ k, k ∈ splitCongruenceSet F ζ hζ q m ↔
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPGoodCompactSplitting.kStar F ζ hζ q ht g))⁻¹ * k *
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPGoodCompactSplitting.kStar F ζ hζ q ht g) ∈ splitCongruenceSet F ζ hζ q m := by
  let C := (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
    (KPGoodCompactSplitting.kStar F ζ hζ q ht)
  have hf (g : KPTameCompact.K0 F q) (k)
      (hk : k ∈ splitCongruenceSet F ζ hζ q m) :
      (C g)⁻¹ * k * C g ∈ splitCongruenceSet F ζ hζ q m := by
    obtain ⟨⟨kg, hkg⟩, rfl⟩ := hk
    obtain ⟨kg0, hkg0, he⟩ := hkg
    have hkg : kg ∈ KPLocalCube.Gamma F q m := ⟨_, hkg0, he⟩
    letI : (KPLocalCube.integerCongruence F q m).Normal := by
      unfold KPLocalCube.integerCongruence; infer_instance
    have hc : g⁻¹ * kg0 * g ∈ KPLocalCube.integerCongruence F q m := by
      simpa only [inv_inv] using
        (inferInstance : (KPLocalCube.integerCongruence F q m).Normal).conj_mem kg0 hkg0 g⁻¹
    have hc' : KPTameCompact.inclusion F q (g⁻¹ * kg0 * g) ∈ KPLocalCube.Gamma F q m :=
      ⟨_, hc, rfl⟩
    refine ⟨⟨_, hc'⟩, ?_⟩
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) _) = _
    rw [← KPGoodCompactSplitting.kStar_eq_section_on_Gamma F ζ hζ q ht m hm _ hc']
    have he' : KPLocalCover.sectionMap F ζ hζ (Sum.inr q) kg =
        KPGoodCompactSplitting.kStar F ζ hζ q ht kg0 := by
      rw [← he]
      exact (KPGoodCompactSplitting.kStar_eq_section_on_Gamma F ζ hζ q ht m hm kg0
        (he.symm ▸ hkg)).symm
    change C (g⁻¹ * kg0 * g) = (C g)⁻¹ *
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) kg) * C g
    rw [he']
    exact C.map_mul _ _ |>.trans (by rw [map_mul, map_inv]; rfl)
  intro k
  change k ∈ _ ↔ (C g)⁻¹ * k * C g ∈ _
  constructor
  · exact hf g k
  · intro hk
    have h := hf g⁻¹ _ hk
    simpa only [map_inv, inv_inv, mul_assoc, mul_inv_cancel, mul_one,
      inv_mul_cancel, one_mul, mul_inv_cancel_left] using h

def unitDilation (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F)) (u : (KPTameCompact.O F q)ˣ) :
    LocalField F q ≃ₜ+ LocalField F q :=
  { (LinearEquiv.smulOfUnit (R := LocalField F q) (M := LocalField F q)
      (KPTameCompact.unitInclusion F q u)).toAddEquiv with
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }

private theorem unitDilation_preimage_lowShell
    (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F)) (u : (KPTameCompact.O F q)ˣ) :
    unitDilation F q u ⁻¹' lowShell F q = lowShell F q := by
  ext x
  change valuation (LocalField F q)
      ((KPTameCompact.unitInclusion F q u : LocalField F q) * x) ≤ 1 ↔
    valuation (LocalField F q) x ≤ 1
  have hu : valuation (LocalField F q)
      (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
    (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
  rw [map_mul, hu, one_mul]

private theorem unitDilation_preservesHaar
    (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F))
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (u : (KPTameCompact.O F q)ˣ) :
    MeasurePreserving (unitDilation F q u) μ μ := by
  let e := unitDilation F q u
  let : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hscalar := Measure.isAddLeftInvariant_eq_smul (μ.map e) μ
  have hmass : (μ.map e) (lowShell F q) = 1 := by
    have hm : Measurable (e : LocalField F q → LocalField F q) := e.continuous.measurable
    rw [Measure.map_apply hm (show MeasurableSet (lowShell F q) from
      (valuation (LocalField F q)).isOpen_integer.measurableSet)]
    change μ (unitDilation F q u ⁻¹' lowShell F q) = 1
    rw [unitDilation_preimage_lowShell]
    exact hμ
  have hone : (μ.map e).addHaarScalarFactor μ = 1 := by
    apply ENNReal.coe_injective
    have heval := hmass
    rw [hscalar, Measure.smul_apply, show μ (lowShell F q) = 1 from hμ] at heval
    simpa only [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_one] using heval
  refine ⟨e.continuous.measurable, ?_⟩
  rw [hscalar, hone, one_smul]

theorem unitDilation_preservesLowShellHaar
    (F : Type) [Field F] [NumberField F]
    (q : HeightOneSpectrum (𝓞 F))
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (u : (KPTameCompact.O F q)ˣ) :
    MeasurePreserving (unitDilation F q u)
      (μ.restrict (lowShell F q)) (μ.restrict (lowShell F q)) := by
  have h := (unitDilation_preservesHaar F q μ hμ u).restrict_preimage
    (show MeasurableSet (lowShell F q) from
      (valuation (LocalField F q)).isOpen_integer.measurableSet)
  rwa [unitDilation_preimage_lowShell] at h

set_option backward.isDefEq.respectTransparency false in
private theorem actual_compact_normalizers
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    (∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m) ∧
    ∀ u : (KPTameCompact.O F q)ˣ, ∀ k,
      k ∈ splitCongruenceSet F ζ hζ q m ↔
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u))⁻¹ * k *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) ∈
            splitCongruenceSet F ζ hζ q m := by
  have hW : KPPGLLocalCover.W F ζ hζ (Sum.inr q) =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPGoodCompactSplitting.kStar F ζ hζ q ht
          (KPStandardLocalRootLifts.integralW F q)) := by
    rw [KPPGLLocalCover.W, KPStandardLocalRootLifts.W_eq_compact F ζ hζ q ht]
    rfl
  constructor
  · intro k hk
    rw [hW]
    exact (compact_normalizes_splitCongruenceSet F ζ hζ q ht m hm
      (KPStandardLocalRootLifts.integralW F q) k).mp hk
  · intro u k
    have hA : KPPGLLocalCover.A F ζ hζ (Sum.inr q)
        (KPTameCompact.unitInclusion F q u) =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (KPGoodCompactSplitting.kStar F ζ hζ q ht
            (KPStandardLocalRootLifts.integralA F q u)) := by
      rw [KPPGLLocalCover.A, KPStandardLocalRootLifts.A_eq_compact F ζ hζ q ht u]
      rfl
    rw [hA]
    exact compact_normalizes_splitCongruenceSet F ζ hζ q ht m hm
      (KPStandardLocalRootLifts.integralA F q u) k

theorem eventual_actual_compact_normalizers
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3) :
    ∃ M : ℕ, ∀ m ≥ M,
    (∀ k ∈ splitCongruenceSet F ζ hζ q m,
      (KPPGLLocalCover.W F ζ hζ (Sum.inr q))⁻¹ * k *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) ∈ splitCongruenceSet F ζ hζ q m) ∧
    ∀ u : (KPTameCompact.O F q)ˣ, ∀ k,
      k ∈ splitCongruenceSet F ζ hζ q m ↔
        (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u))⁻¹ * k *
          KPPGLLocalCover.A F ζ hζ (Sum.inr q) (KPTameCompact.unitInclusion F q u) ∈
            splitCongruenceSet F ζ hζ q m := by
  obtain ⟨M, hM⟩ := KPTameJacquetBruhatTests.TestConstruction.eventually_matrixChartDepth F q
  exact ⟨M, fun m hm => actual_compact_normalizers F ζ hζ q ht m (hM m hm)⟩

end DedekindZetaZeroFree.KPTameTransposeLowShellSupport

end
