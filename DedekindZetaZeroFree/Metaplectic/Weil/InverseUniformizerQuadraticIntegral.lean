module

public import DedekindZetaZeroFree.Metaplectic.Weil.LocalUnitQuadraticIntegral
public import DedekindZetaZeroFree.Arithmetic.LocalFields.BallQuotients

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.ExteriorGauss
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private theorem two_norm (v : HeightOneSpectrum (𝓞 F)) (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6) :
    ‖(2 : v.adicCompletion F)‖ = 1 := by
  have hnot : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    have hz : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
      simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    have hd : (ResidueTrace.rationalPrimeBelow v).val ∣ 2 :=
      (ringChar.spec (𝓞 F ⧸ v.asIdeal) 2).mp hz
    exact hgood (hd.trans (by norm_num))
  simpa only [map_ofNat] using
    (FinitePlace.norm_eq_one_iff_notMem F v (2 : 𝓞 F)).mpr hnot
private theorem cutoff_set (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (n : ℕ) :
    (finiteCompletionBall F v (-(n:ℤ)) : Set (v.adicCompletion F)) =
      {x : v.adicCompletion F | ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ)^n} := by
  have han : ‖(a : v.adicCompletion F)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, ha, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp
  ext x
  have hv : Valued.v ((a : v.adicCompletion F)^(-(n:ℤ))) = WithZero.exp (n:ℤ) := by
    rw [map_zpow₀, ha, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hn : ‖(a : v.adicCompletion F)^(-(n:ℤ))‖ = (Ideal.absNorm v.asIdeal : ℝ)^n := by
    simp [norm_zpow, han]
  rw [SetLike.mem_coe, mem_finiteCompletionBall, neg_neg, ← hv,
    ← Valued.toNormedField.norm_le_iff, hn]
  rfl

set_option maxHeartbeats 800000 in
private theorem restrict_integral (v : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (n : ℕ) :
    (∫ x in (finiteCompletionBall F v (-(n:ℤ)) : Set (v.adicCompletion F)),
      (ResidueTrace.localTraceCharacter v ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ) ∂μ) =
    ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
      (ResidueTrace.localTraceCharacter v ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ) ∂μ := by
  let K := v.adicCompletion F
  let O := (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  let H := finiteCompletionBall F v 1
  let U := finiteCompletionBall F v (-(n:ℤ))
  let f : K → ℂ := fun x =>
    (ResidueTrace.localTraceCharacter v ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ)
  have hHO : H ≤ O := by
    change _ ≤ (v.adicCompletionIntegers F).toSubring.toAddSubgroup
    rw [← finiteCompletionBall_zero F v]
    exact (finiteCompletionBall_le_iff F v 0 1).mpr (by omega)
  have hOU : O ≤ U := by
    change (v.adicCompletionIntegers F).toSubring.toAddSubgroup ≤ _
    rw [← finiteCompletionBall_zero F v]
    exact (finiteCompletionBall_le_iff F v (-(n:ℤ)) 0).mpr (by omega)
  have hHU : H ≤ U := hHO.trans hOU
  have hOc : IsCompact (O : Set K) := by
    simpa only [finiteCompletionBall_zero, O] using isCompact_finiteCompletionBall F v 0
  have hUc : IsCompact (U : Set K) := isCompact_finiteCompletionBall F v _
  have hf : Continuous f := (continuous_subtype_val.comp
    (ResidueTrace.continuous_localTraceCharacter v)).comp (by fun_prop)
  have htriv (t : K) (ht : t ∈ O) : ResidueTrace.localTraceCharacter v t = 1 := by
    simpa using (hzero t).mpr ht (1 : v.adicCompletionIntegers F)
  have hq (h : K) (hh : h ∈ H) :
      ResidueTrace.localTraceCharacter v ((a⁻¹ : (v.adicCompletion F)ˣ) * h ^ 2) = 1 := by
    apply htriv
    have hhh : h ∈ (fun o : K => (a : K)^ (1:ℤ) * o) '' (v.adicCompletionIntegers F : Set K) := by
      change h ∈ (finiteCompletionBall F v 1 : Set K) at hh
      rw [finiteCompletionBall_eq_uniformizer_image F v (a : K) ha 1] at hh
      exact hh
    obtain ⟨o, ho, rfl⟩ := hhh
    have he : (a⁻¹ : (v.adicCompletion F)ˣ) * ((a : K)^ (1:ℤ) * o)^2 =
        (a : K) * o^2 := by
      simp only [zpow_one, Units.val_inv_eq_inv_val]
      field_simp
      <;> ring
    rw [he]
    apply (v.adicCompletionIntegers F).toSubring.mul_mem _ ((v.adicCompletionIntegers F).toSubring.pow_mem ho 2)
    change Valued.v (a : K) ≤ 1
    rw [ha]
    exact le_of_lt (by simpa using (show (-1:ℤ) < 0 by omega))
  let Q := U ⧸ H.comap U.subtype
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  letI : Finite Q := AddSubgroup.quotient_finite_of_isOpen _
    ((isOpen_finiteCompletionBall F v 1).preimage continuous_subtype_val)
  letI : Fintype Q := Fintype.ofFinite Q
  let r : Q → U := Quotient.out
  let C : Q → Set K := fun i => {x | x - r i ∈ H}
  have hr (i : Q) : QuotientAddGroup.mk (r i) = i := Quotient.out_eq _
  have hdis : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hs : (r i : K) - r j ∈ H := by
      convert H.sub_mem hj hi using 1 <;> abel
    have he : (QuotientAddGroup.mk (r i) : Q) = QuotientAddGroup.mk (r j) :=
      QuotientAddGroup.eq_iff_sub_mem.mpr hs
    rw [hr, hr] at he
    exact hij he
  have hunion : (U : Set K) = ⋃ i, C i := by
    ext x
    constructor
    · intro hx
      let y : U := ⟨x, hx⟩
      let i : Q := QuotientAddGroup.mk y
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have he : (QuotientAddGroup.mk y : Q) = QuotientAddGroup.mk (r i) := (hr i).symm
      exact QuotientAddGroup.eq_iff_sub_mem.mp he
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      simpa only [sub_add_cancel, SetLike.mem_coe] using U.add_mem (hHU hi) (r i).property
  have hCc (i : Q) : IsCompact (C i) := isCompact_finiteCompletionBall_coset F v (r i) 1
  have hrestrict (i : Q) : (∫ x in C i, f x ∂μ) = ∫ x in C i ∩ (O : Set K), f x ∂μ := by
    by_cases hi : (r i : K) ∈ O
    · have hsub : C i ⊆ (O : Set K) := by
        intro x hx
        simpa only [sub_add_cancel, SetLike.mem_coe] using O.add_mem (hHO hx) hi
      rw [Set.inter_eq_left.mpr hsub]
    · have hempty : C i ∩ (O : Set K) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxO⟩
        apply hi
        convert O.sub_mem hxO (hHO hx) using 1 <;> abel
      rw [hempty, setIntegral_empty]
      have hz : (2 : K) * (r i : K) ∉ O := by
        intro hz
        apply hi
        apply mem_adicCompletionIntegers_of_norm_le_one v
        simpa [norm_mul, two_norm v hgood] using norm_le_one_of_mem_adicCompletionIntegers v hz
      obtain ⟨o, ho⟩ : ∃ o : v.adicCompletionIntegers F,
          ResidueTrace.localTraceCharacter v ((2 : K) * (r i : K) * (o : K)) ≠ 1 := by
        simpa only [not_forall] using mt (hzero ((2:K) * (r i : K))).mp hz
      let h : K := (a : K) * (o : K)
      have hh : h ∈ H := by
        change h ∈ (finiteCompletionBall F v 1 : Set K)
        rw [finiteCompletionBall_eq_uniformizer_image F v (a : K) ha 1]
        exact ⟨o, o.property, by simp [h]⟩
      have hmem (x : K) : h + x ∈ C i ↔ x ∈ C i := by
        constructor
        · intro hx
          change h + x - (r i : K) ∈ H at hx
          change x - (r i : K) ∈ H
          convert H.sub_mem hx hh using 1 <;> abel
        · intro hx
          change x - (r i : K) ∈ H at hx
          change h + x - (r i : K) ∈ H
          convert H.add_mem hh hx using 1 <;> abel
      let c : ℂ := (ResidueTrace.localTraceCharacter v ((2:K) * (r i : K) * (o : K)) : ℂ)
      have hc : c ≠ 1 := fun he => ho (Circle.coe_eq_one.mp he)
      have hphase (x : K) (hx : x ∈ C i) : f (h + x) = c * f x := by
        have hexp : (a⁻¹ : (v.adicCompletion F)ˣ) * (h + x)^2 =
            (a⁻¹ : (v.adicCompletion F)ˣ) * h^2 +
            (a⁻¹ : (v.adicCompletion F)ˣ) * x^2 + (2:K) * x * (o : K) := by
          dsimp [h]
          simp only [Units.val_inv_eq_inv_val]
          field_simp
          <;> ring
        have ht : ResidueTrace.localTraceCharacter v ((2:K) * (x - r i) * (o:K)) = 1 := by
          apply htriv
          exact (v.adicCompletionIntegers F).toSubring.mul_mem
            ((v.adicCompletionIntegers F).toSubring.mul_mem (show (2:K) ∈ (v.adicCompletionIntegers F).toSubring from by simpa only [one_add_one_eq_two] using (v.adicCompletionIntegers F).toSubring.add_mem (v.adicCompletionIntegers F).toSubring.one_mem (v.adicCompletionIntegers F).toSubring.one_mem) (hHO hx)) o.property
        have helin : (2:K) * x * (o:K) = (2:K) * (r i : K) * (o:K) +
            (2:K) * (x - r i) * (o:K) := by ring
        change (ResidueTrace.localTraceCharacter v ((a⁻¹ : (v.adicCompletion F)ˣ) * (h+x)^2) : ℂ) = _
        rw [hexp, helin]
        simp only [AddChar.map_add_eq_mul, hq h hh, ht, mul_one, one_mul, Circle.coe_mul]
        exact mul_comm _ _
      have htranslate : (fun x : K => (C i).indicator f (h + x)) =
          (fun x : K => c * (C i).indicator f x) := by
        funext x
        by_cases hx : x ∈ C i
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mpr hx)]
          exact hphase x hx
        · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).mp hx), mul_zero]
      have heq := integral_add_left_eq_self (μ := μ) ((C i).indicator f) h
      rw [htranslate, integral_const_mul, integral_indicator (hCc i).measurableSet] at heq
      by_contra hI
      exact hc ((mul_eq_right₀ hI).mp heq)
  have hUL : (U : Set K) ∩ O = O := Set.inter_eq_right.mpr hOU
  change (∫ x in (U : Set K), f x ∂μ) = ∫ x in (O : Set K), f x ∂μ
  rw [hunion, integral_iUnion_fintype (fun i => (hCc i).measurableSet) hdis
    (fun i => hf.continuousOn.integrableOn_compact (hCc i))]
  rw [show (∑ i, ∫ x in C i, f x ∂μ) = ∑ i, ∫ x in C i ∩ (O : Set K), f x ∂μ from Finset.sum_congr rfl (fun i _ => hrestrict i)]
  rw [← integral_iUnion_fintype
    (fun i => (hCc i).measurableSet.inter hOc.measurableSet)
    (fun i j hij => (hdis hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun i => hf.continuousOn.integrableOn_compact ((hCc i).inter hOc))]
  rw [← Set.iUnion_inter, ← hunion, hUL]

theorem inverse_uniformizer_cutoff_eventually
    (v : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      rawCutoff v μ a⁻¹ n =
        (Real.sqrt ‖(2 : v.adicCompletion F) * (a⁻¹ : (v.adicCompletion F)ˣ)‖ : ℂ) *
          ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
            (ResidueTrace.localTraceCharacter v
              ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ) ∂μ := by
  apply Filter.Eventually.of_forall
  intro n
  unfold rawCutoff
  rw [← cutoff_set v a ha n, restrict_integral v hgood hzero μ a ha n]

end
end DedekindZetaZeroFree.ExteriorGauss
