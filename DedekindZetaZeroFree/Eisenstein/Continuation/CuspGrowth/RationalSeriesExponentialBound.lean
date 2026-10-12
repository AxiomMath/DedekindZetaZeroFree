module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.RadialHeightLowerBound
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.NormalSeries

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
set_option maxHeartbeats 1600000

namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

private theorem norm_flat_between
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K₀ : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀)
    (φ : KPLiteralRaw.Flat F ζ hζ K₀) (s s₀ s₁ : ℂ)
    (hlo : s₀.re ≤ s.re) (hhi : s.re ≤ s₁.re) (g : KPLiteralRaw.G F ζ hζ) :
    ‖φ.val s g‖ ≤ ‖φ.val s₀ g‖ + ‖φ.val s₁ g‖ := by
  obtain ⟨t, x, k, rfl⟩ := hK₀.2.1 g
  simp only [KPLiteralExceptionalResidue.val_torus_root_compact, KPLiteralExceptionalResidue.norm_val_torus_compact]
  let δ : ℝ := ((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)
  have hδ : 0 < δ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hp : 0 ≤ KPLiteralExceptionalResidue.normalizedTorusProfile F ζ hζ K₀ φ t k :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hδ.le _)
  by_cases hδ1 : 1 ≤ δ
  · exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hδ1 (by linarith : 2/3+s.re ≤ 2/3+s₁.re)) hp).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hδ.le _) hp))
  · exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ (le_of_not_ge hδ1)
        (by linarith : 2/3+s₀.re ≤ 2/3+s.re)) hp).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hδ.le _) hp))

private theorem fixed_parameter_majorant
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K₀ : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀)
    (φ : KPLiteralRaw.Flat F ζ hζ K₀) (z : ℂ) (hz : (1 : ℝ)/3 < z.re)
    (B : Set (KPCuspCharts.Cross F)) (hB : IsCompact B)
    (D : Set (KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)) (hD : IsCompact D) :
    ∃ b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ,
      Summable b ∧ (∀ q, 0 ≤ b q) ∧ ∀ q xb, xb ∈ B → ∀ c ∈ D, ∀ t : ℝ, 0 ≤ t →
        ‖φ.val z (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) *
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
            (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val))‖ ≤
        b q * Real.exp ((2 * (KPCuspLogShape.dimension F : ℝ) * (2/3 + z.re)) * t) := by
  obtain ⟨m, hm, hlow⟩ := movingRowHeight_lower F ζ hζ B hB D hD
  obtain ⟨C, hC, hdec⟩ := KPLiteralExceptionalResidue.actualScalarHeightDecay F ζ hζ K₀ hK₀ φ z hz
  let a : ℝ := 2/3 + z.re
  have ha : 1 < a := by dsimp [a]; linarith
  let b := fun q => (C * m ^ (-2*a)) *
    KPHeightSeries.term Projectivization.mulHeight a (KPLiteralExceptionalResidue.chamberCosetIndex F q)
  have hb : Summable b :=
    ((KPHeightSeries.relativeHeight_summable_tail F a ha).1.comp_injective
      (KPLiteralExceptionalResidue.chamberCosetIndex_injective F)).mul_left (C * m ^ (-2*a))
  refine ⟨b, hb, ?_, ?_⟩
  · intro q
    dsimp [b, KPHeightSeries.term]
    positivity
  · intro q xb hxb c hc t ht
    let g := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val
    have h := hdec (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) * g)
    rw [KPLiteralExceptionalResidue.actualBaseRowHeight_rational_mul] at h
    have hl := hlow (KPChamberHeight.bottomRow F (Quotient.out q)) xb hxb c hc t ht
    rw [← KPLiteralExceptionalResidue.chamberCosetIndex_mulHeight_out] at hl
    have hp := Real.rpow_le_rpow_of_nonpos
      (mul_pos (mul_pos hm (Real.exp_pos _)) (Projectivization.mulHeight_pos _)) hl
      (by dsimp [a]; linarith : -2*a ≤ 0)
    refine h.trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq ?_)
    rw [Real.mul_rpow (mul_nonneg hm.le (Real.exp_pos _).le) (Projectivization.mulHeight_pos _).le,
      Real.mul_rpow hm.le (Real.exp_pos _).le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    dsimp [b, KPHeightSeries.term, a]
    rw [show (-↑(KPCuspLogShape.dimension F) * t) * (-2 * (2/3+z.re)) =
      (2 * ↑(KPCuspLogShape.dimension F) * (2/3+z.re)) * t by ring]
    ring

private theorem compact_parameter_majorant
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (K₀ : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀)
    (φ : KPLiteralRaw.Flat F ζ hζ K₀)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ KPContActualChamberNormalSeries.V)
    (B : Set (KPCuspCharts.Cross F)) (hB : IsCompact B)
    (D : Set (KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)) (hD : IsCompact D) :
    ∃ (M : ℝ) (b : KPChamberBruhatTwoCells.RationalQuotient F → ℝ),
      0 ≤ M ∧ Summable b ∧ (∀ q, 0 ≤ b q) ∧
      ∀ s ∈ K, ∀ q xb, xb ∈ B → ∀ c ∈ D, ∀ t : ℝ, 0 ≤ t →
        ‖φ.val s (KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) *
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
            (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val))‖ ≤
        b q * Real.exp (M * t) := by
  by_cases hne : K.Nonempty
  · obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨s₁, hs₁, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨b₀, hb₀, hb₀pos, hbound₀⟩ := fixed_parameter_majorant F ζ hζ K₀ hK₀ φ s₀ (hKV hs₀) B hB D hD
    obtain ⟨b₁, hb₁, hb₁pos, hbound₁⟩ := fixed_parameter_majorant F ζ hζ K₀ hK₀ φ s₁ (hKV hs₁) B hB D hD
    let M := 2 * (KPCuspLogShape.dimension F : ℝ) * (2/3+s₁.re)
    have hM : 0 ≤ M := by
      have hh : (1:ℝ)/3 < s₁.re := hKV hs₁
      dsimp [M]; positivity
    refine ⟨M, b₀+b₁, hM, hb₀.add hb₁, fun q => add_nonneg (hb₀pos q) (hb₁pos q), ?_⟩
    intro s hs q xb hxb c hc t ht
    have he : Real.exp ((2 * (KPCuspLogShape.dimension F : ℝ) * (2/3+s₀.re)) * t) ≤
        Real.exp (M*t) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ ht
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * (KPCuspLogShape.dimension F : ℝ))
      have hh : s₀.re ≤ s₁.re := hmin hs₁
      linarith
    calc
      _ ≤ ‖φ.val s₀ _‖ + ‖φ.val s₁ _‖ := norm_flat_between F ζ hζ K₀ hK₀ φ s s₀ s₁ (hmin hs) (hmax hs) _
      _ ≤ b₀ q * Real.exp (M*t) + b₁ q * Real.exp (M*t) :=
        add_le_add ((hbound₀ q xb hxb c hc t ht).trans (mul_le_mul_of_nonneg_left he (hb₀pos q)))
          (hbound₁ q xb hxb c hc t ht)
      _ = _ := by simp only [Pi.add_apply]; ring
  · refine ⟨0, 0, le_rfl, summable_zero, fun _ => le_rfl, ?_⟩
    intro s hs
    exact (hne ⟨s, hs⟩).elim

theorem actualSeries_exponential_bound
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (K : Set ℂ) (hK : IsCompact K) (hKV : K ⊆ KPContActualChamberNormalSeries.V)
    (B : Set (KPCuspCharts.Cross F)) (hB : IsCompact B)
    (D : Set (KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ))
    (hD : IsCompact D) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ (s : ℂ), s ∈ K → ∀ (xb : KPCuspCharts.Cross F), xb ∈ B →
        ∀ c ∈ D, ∀ (t : ℝ), 0 ≤ t →
          ‖KPContActualChamberNormalSeries.E F ζ hζ U ι f s
              (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
                (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
                  (KPCuspCharts.toArch F (xb, t))) * c.val)‖ ≤
            C * Real.exp (M * t) := by
  let B₀ := Module.finBasis ℂ S
  have hKΩ : K ⊆ KPContinuation.spectralDomain := by
    intro s hs
    have hh : (1:ℝ)/3 < s.re := hKV hs
    change -(1:ℝ)/6 < s.re
    linarith
  have hcoef : ∀ i : Fin (Module.finrank ℂ S), ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ K, ‖B₀.repr (f s) i‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (fun s => B₀.repr (f s) i) K :=
      (B₀.coord i).continuous_of_finiteDimensional.comp_continuousOn
        (hf.continuousOn.mono hKΩ)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
    exact ⟨max 0 C, le_max_left _ _, fun s hs => (hC s hs).trans (le_max_right _ _)⟩
  choose C hC hCb using hcoef
  let K₀ := (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).K
  have hK₀ : KPLiteralRaw.IwasawaCompact F ζ hζ K₀ :=
    ⟨(KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).compact,
      (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ).decomposition,
      KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ⟩
  have hmajor : ∀ i : Fin (Module.finrank ℂ S),
      ∃ (M : ℝ) (b : KPContActualChamberNormalSeries.Q F → ℝ),
      0 ≤ M ∧ Summable b ∧ (∀ q, 0 ≤ b q) ∧
      ∀ s ∈ K, ∀ q xb, xb ∈ B → ∀ c ∈ D, ∀ t : ℝ, 0 ≤ t →
        ‖KPContActualSphericalFlatStage.L F ζ hζ U ι s (B₀ i)
          (KPContActualChamberNormalSeries.lift F ζ hζ q *
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
              (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val))‖ ≤
        b q * Real.exp (M*t) := by
    intro i
    obtain ⟨φ, hφ⟩ := ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι (B₀ i)
    obtain ⟨M, b, hM, hb, hbpos, hbound⟩ := compact_parameter_majorant F ζ hζ K₀ hK₀ φ K hK hKV B hB D hD
    refine ⟨M, b, hM, hb, hbpos, ?_⟩
    intro s hs q xb hxb c hc t ht
    have hl : KPContActualChamberNormalSeries.lift F ζ hζ q =
        KPLiteralRaw.rationalLift F ζ hζ (Quotient.out q) := by
      unfold KPContActualChamberNormalSeries.lift KPContFlatRationalCosetCovariance.matrixRationalHom
      change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
          (Quotient.out q)) = _
      rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift]
      exact (KPLiteralExceptionalResidue.rationalLift_eq_constructed F ζ hζ (Quotient.out q)).symm
    rw [hl, ← hφ]
    exact hbound s hs q xb hxb c hc t ht
  choose M b hM hb hbpos hbound using hmajor
  let M₀ := ∑ i, M i
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg (fun i _ => hM i)
  have hMle : ∀ i, M i ≤ M₀ := fun i =>
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  let b₀ := fun q => ∑ i, C i * b i q
  have hb₀ : Summable b₀ := summable_sum (fun i _ => (hb i).mul_left (C i))
  have hb₀pos : ∀ q, 0 ≤ b₀ q := fun q => Finset.sum_nonneg (fun i _ => mul_nonneg (hC i) (hbpos i q))
  refine ⟨∑' q, b₀ q, M₀, tsum_nonneg hb₀pos, hM₀, ?_⟩
  intro s hs xb hxb c hc t ht
  let g := KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ (KPCuspCharts.toArch F (xb,t))) * c.val
  have hterm : ∀ q, ‖KPContActualChamberNormalSeries.term F ζ hζ U ι f q s g‖ ≤
      b₀ q * Real.exp (M₀*t) := by
    intro q
    have heq : KPContActualChamberNormalSeries.term F ζ hζ U ι f q s g = ∑ i,
        B₀.repr (f s) i * KPContActualSphericalFlatStage.L F ζ hζ U ι s (B₀ i)
          (KPContActualChamberNormalSeries.lift F ζ hζ q * g) := by
      unfold KPContActualChamberNormalSeries.term
      conv_lhs => rw [← B₀.sum_repr (f s)]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    calc
      _ ≤ ∑ i, ‖B₀.repr (f s) i * KPContActualSphericalFlatStage.L F ζ hζ U ι s (B₀ i)
          (KPContActualChamberNormalSeries.lift F ζ hζ q * g)‖ := norm_sum_le _ _
      _ ≤ ∑ i, C i * (b i q * Real.exp (M₀*t)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        have he : Real.exp (M i*t) ≤ Real.exp (M₀*t) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hMle i) ht)
        exact mul_le_mul (hCb i s hs)
          ((hbound i s hs q xb hxb c hc t ht).trans (mul_le_mul_of_nonneg_left he (hbpos i q)))
          (norm_nonneg _) (hC i)
      _ = _ := by simp only [b₀, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i hi; ring
  have hsum : Summable (fun q => ‖KPContActualChamberNormalSeries.term F ζ hζ U ι f q s g‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hb₀.mul_right _)
  exact (norm_tsum_le_tsum_norm hsum).trans
    ((hsum.tsum_le_tsum hterm (hb₀.mul_right _)).trans_eq (hb₀.tsum_mul_right _))

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
