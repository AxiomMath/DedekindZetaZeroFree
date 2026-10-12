module

public import DedekindZetaZeroFree.Metaplectic.Weil.DyadicHilbertDefect

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

open MeasureTheory Filter
open scoped ENNReal

local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
private lemma normalizedHaar (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ μ : Measure (v.adicCompletion F), μ.IsAddHaarMeasure ∧
      μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 ∧
      A.finiteTraceHaar v = ENNReal.ofReal (PoissonS.integerVolume F v) • μ := by
  let K := v.adicCompletion F
  letI : LocallyCompactSpace K :=
    (PoissonS.finite_components_locallyCompact F {v}).1 ⟨v, Finset.mem_singleton_self v⟩
  let μ₀ : Measure K := Measure.addHaar
  have hO : (v.adicCompletionIntegers F : Set K) = {x | ‖x‖ ≤ (1 : ℝ)} := by
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers v,
      mem_adicCompletionIntegers_of_norm_le_one v⟩
  have hp : 0 < μ₀ (v.adicCompletionIntegers F : Set K) := by
    rw [hO]
    apply IsOpen.measure_pos
    · simpa [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : K) one_ne_zero
    · exact ⟨0, by simp⟩
  have hf : μ₀ (v.adicCompletionIntegers F : Set K) ≠ ⊤ := by
    rw [hO]
    have hc : IsCompact {x : K | ‖x‖ ≤ (1 : ℝ)} := by
      simpa [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : K) (1 : ℝ)
    exact hc.measure_lt_top.ne
  refine ⟨(μ₀ (v.adicCompletionIntegers F : Set K))⁻¹ • μ₀, ?_, ?_, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.mpr hf)
      (ENNReal.inv_ne_top.mpr hp.ne')
  · simp [Measure.smul_apply, ENNReal.inv_mul_cancel hp.ne' hf]
  · simp only [finiteTraceHaar, div_eq_mul_inv, hO, smul_smul]
    rfl
private lemma cutoff_scale (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) (c : ℝ≥0∞)
    (a : (v.adicCompletion F)ˣ) (n : ℕ) :
    exteriorRawQuadraticCutoff v (c • μ) a n =
      (c.toReal : ℂ) * exteriorRawQuadraticCutoff v μ a n := by
  unfold exteriorRawQuadraticCutoff
  rw [Measure.restrict_smul, integral_smul_measure]
  simp [smul_eq_mul]
  ring

theorem finiteWeilCutoff_stabilizes (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    A.FiniteQuadraticStabilizes v a :=
  A.finiteQuadratic_stabilizes v a

private lemma normalizedRatio_eventually (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (μ : Measure (v.adicCompletion F))
    (hμ : A.finiteTraceHaar v = ENNReal.ofReal (PoissonS.integerVolume F v) • μ) :
    ∀ᶠ n : ℕ in atTop,
      exteriorRawQuadraticCutoff v μ a n / exteriorRawQuadraticCutoff v μ 1 n =
        A.finiteWeilPhase v a := by
  have hc : (PoissonS.integerVolume F v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (PoissonS.integerVolume_pos F v).ne'
  have ha := A.finiteQuadraticCutoff_eventually_eq_gamma v a (A.finiteWeilCutoff_stabilizes v a)
  have h1 := A.finiteQuadraticCutoff_eventually_eq_gamma v 1 (A.finiteWeilCutoff_stabilizes v 1)
  filter_upwards [ha, h1] with n han h1n
  change exteriorRawQuadraticCutoff v (A.finiteTraceHaar v) a n = _ at han
  change exteriorRawQuadraticCutoff v (A.finiteTraceHaar v) 1 n = _ at h1n
  rw [hμ, cutoff_scale, ENNReal.toReal_ofReal (PoissonS.integerVolume_pos F v).le] at han h1n
  unfold finiteWeilPhase
  rw [← han, ← h1n, mul_div_mul_left _ _ hc]

def finiteWeilIndex (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) : Circle :=
  ⟨A.finiteWeilPhase v a, (mem_sphere_zero_iff_norm).2
    (A.finiteWeilPhase_norm v a)⟩

def infiniteWeilIndex (A : SArithmeticData F)
    (v : InfinitePlace F) (a : v.Completionˣ) : Circle :=
  ⟨A.complexWeilPhase v a, by simp [complexWeilPhase, complexGamma]⟩

private lemma quadCoeff (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    A.finiteQuadraticHilbertCoefficient v a b =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : rootsOfUnity 2 F) : Fˣ) : F) := by
  let r := A.actualLocalSymbol v 2 (Or.inl rfl) a b
  have hr : (r : Fˣ) ∈ rootsOfUnity 2 F := r.property
  have hs : ((r : Fˣ) : F)^2 = 1 := by
    exact congrArg Units.val ((mem_rootsOfUnity 2 _).mp hr)
  change (if r = 1 then (1 : ℂ) else -1) = σ ((r : Fˣ) : F)
  rcases (sq_eq_one_iff).mp hs with h | h
  · have he : r = 1 := rootsOfUnity.coe_injective h
    rw [if_pos he, h, map_one]
  · have he : r ≠ 1 := by
      intro he
      have : (1 : F) = -1 := by simpa [he] using h
      exact (neg_ne_self.mpr (one_ne_zero : (1 : F) ≠ 0)) this.symm
    rw [if_neg he, h, map_neg, map_one]
private lemma oddOfNonDyadic (v : HeightOneSpectrum (𝓞 F))
    (hv : (2 : 𝓞 F) ∉ v.asIdeal) : ringChar (OddLocalResidue v) ≠ 2 := by
  let e : (𝓞 F ⧸ v.asIdeal) ≃+* OddLocalResidue v :=
    (finitePlaceIdealResidueEquivCompletion v).trans
      (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))
  intro hc
  have hz : (2 : OddLocalResidue v) = 0 := by
    haveI : CharP (OddLocalResidue v) 2 := ringChar.of_eq hc
    exact CharP.cast_eq_zero _ 2
  have hq : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := e.injective (by simpa only [map_ofNat, map_zero] using hz)
  exact hv ((Ideal.Quotient.eq_zero_iff_mem).mp hq)

theorem finiteWeilIndex_mul (A : SArithmeticData F) (σ : F →+* ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (a b : (v.adicCompletion F)ˣ) :
    (A.finiteWeilIndex v a : ℂ) * (A.finiteWeilIndex v b : ℂ) =
      σ (((A.actualLocalSymbol v 2 (Or.inl rfl) a b : rootsOfUnity 2 F) : Fˣ) : F) *
        (A.finiteWeilIndex v (a * b) : ℂ) := by
  change A.finiteWeilPhase v a * A.finiteWeilPhase v b = _ * A.finiteWeilPhase v (a*b)
  by_cases hv : (2 : 𝓞 F) ∈ v.asIdeal
  · exact A.finiteWeilPhase_mul_dyadic σ v hv a b
  · rw [← quadCoeff]
    exact A.finiteWeilPhase_odd_hilbert_defect v (oddOfNonDyadic v hv) a b

theorem normalizedWeilIndex_product (A : SArithmeticData F) (a : Fˣ) :
    (∏ w : InfinitePlace F,
      A.infiniteWeilIndex w
        (Units.map (algebraMap F w.Completion).toMonoidHom a)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        A.finiteWeilIndex v
          (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) = 1 := by
  have hinf (w : InfinitePlace F) : A.infiniteWeilIndex w
      (Units.map (algebraMap F w.Completion).toMonoidHom a) = 1 := by
    apply Circle.ext
    simp [infiniteWeilIndex, complexWeilPhase, complexGamma]
  simp only [hinf, Finset.prod_const_one, one_mul]
  apply Circle.ext
  change Circle.coeHom (∏ᶠ v : HeightOneSpectrum (𝓞 F),
    A.finiteWeilIndex v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) = 1
  rw [Circle.coeHom.map_finprod_of_injective Subtype.val_injective]
  have hp := (A.globalQuadraticWeilPhase_product a).2
  have hg : ∏ᶠ v : QuadraticGlobalPlace F, A.globalQuadraticWeilPhase a v =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), A.globalQuadraticWeilPhase a (Sum.inr v) := by
    rw [← finprod_mem_range Sum.inr_injective, ← finprod_mem_univ]
    apply finprod_mem_inter_mulSupport_eq'
    intro v hv
    cases v with
    | inl w =>
      exfalso
      apply hv
      simp [globalQuadraticWeilPhase, globalQuadraticGamma, complexGamma]
    | inr v => simp
  rw [hg] at hp
  change (∏ᶠ v : HeightOneSpectrum (𝓞 F),
    A.finiteWeilPhase v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)) = 1
  simpa [finiteWeilPhase, globalQuadraticWeilPhase, globalQuadraticGamma] using hp

theorem finiteWeilIndex_exterior_unit (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    (u : (v.adicCompletionIntegers F)ˣ) :
    A.finiteWeilIndex v
      (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
  obtain ⟨μ, hhaar, hvol, hμ⟩ := normalizedHaar A v
  letI := hhaar
  have h := (normalizedRatio_eventually A v
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) μ hμ).and
      (A.exterior_raw_quadratic_ratio_unit_eventually I v hIv hgood hzero μ hvol u)
  obtain ⟨n, hn, h1⟩ := h.exists
  apply Circle.ext
  exact hn.symm.trans h1

theorem finiteWeilIndex_exterior_inv_generator
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    (A.finiteWeilIndex v
        ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⁻¹) : ℂ) =
      A.exteriorQuadraticGauss hS I v hIv p hp ∧
    A.exteriorQuadraticGauss hS I v hIv p hp =
      A.idealGauss σ hS I p hp 3 := by
  have he := A.exteriorQuadraticGauss_eq_idealGauss_three σ hS B I v hIv hgood hzero p hp a hap ha
  refine ⟨?_, he⟩
  obtain ⟨μ, hhaar, hvol, hμ⟩ := normalizedHaar A v
  letI := hhaar
  have h := (normalizedRatio_eventually A v
    ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⁻¹) μ hμ).and
      (A.exterior_raw_quadratic_ratio_eq_gamma_three σ hS B I v hIv hgood hzero p hp a hap ha μ hvol)
  obtain ⟨n, hn, h1⟩ := h.exists
  exact (hn.symm.trans h1).trans he.symm

end
end DedekindZetaZeroFree.SArithmeticData
