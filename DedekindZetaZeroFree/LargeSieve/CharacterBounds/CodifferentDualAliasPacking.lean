module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.FiniteWindowLatticeNormalization
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DualBallFibers

@[expose] public section

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking
noncomputable section
open NumberField
open scoped Classical nonZeroDivisors

theorem codifferent_finite_colors (F : Type) [Field F] [NumberField F] :
    ∃ n : ℕ, 0 < n ∧ ∃ col : F → Fin n,
      ∀ u v : F, u ∈ (PoissonArch.codifferentIdeal F :
        FractionalIdeal (𝓞 F)⁰ F) →
        v ∈ (PoissonArch.codifferentIdeal F :
        FractionalIdeal (𝓞 F)⁰ F) →
        col u = col v → ∃ m : 𝓞 F, u - v = (m : F) := by
  let I : FractionalIdeal (𝓞 F)⁰ F := PoissonArch.codifferentIdeal F
  obtain ⟨d, hd, hden⟩ := I.isFractional
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hnum : ∀ u : F, u ∈ I → ∃ a : 𝓞 F, (a : F) = (d : F) * u := by
    intro u hu
    obtain ⟨a, ha⟩ := hden u hu
    exact ⟨a, ha⟩
  let num : F → 𝓞 F := fun u => if hu : u ∈ I then (hnum u hu).choose else 0
  have hnum_eq (u : F) (hu : u ∈ I) : (num u : F) = (d : F) * u := by
    dsimp [num]
    rw [dif_pos hu]
    exact (hnum u hu).choose_spec
  let J : Ideal (𝓞 F) := Ideal.span {d}
  have hJ : J ≠ ⊥ := fun h => hd0 (Ideal.span_singleton_eq_bot.mp h)
  letI : Finite ((𝓞 F) ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ
  letI : Fintype ((𝓞 F) ⧸ J) := Fintype.ofFinite _
  let e := Fintype.equivFin ((𝓞 F) ⧸ J)
  refine ⟨Fintype.card ((𝓞 F) ⧸ J), Fintype.card_pos,
    fun u => e (Ideal.Quotient.mk J (num u)), ?_⟩
  intro u v hu hv hcol
  have hq : Ideal.Quotient.mk J (num u) = Ideal.Quotient.mk J (num v) :=
    e.injective hcol
  have hsub : num u - num v ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hq
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hsub
  refine ⟨m, ?_⟩
  have hcast := congrArg (fun a : 𝓞 F => (a : F)) hm
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd0
  apply mul_left_cancel₀ hdF
  rw [mul_sub]
  rw [← hnum_eq u hu, ← hnum_eq v hv]
  simpa only [map_mul, map_sub, mul_comm] using hcast.symm

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking

end

section
open scoped ENNReal

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking
noncomputable section

private theorem ball_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} (x : ι → E) (T : Finset ι)
    (a : E) (ρ r : ℝ) (hρ : 0 ≤ ρ) (hr : 0 < r)
    (hb : ∀ i ∈ T, ‖x i - a‖ ≤ ρ)
    (hs : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 2 * r ≤ ‖x i - x j‖) :
    (T.card : ℝ) * r ^ Module.finrank ℝ E ≤ (ρ + r) ^ Module.finrank ℝ E := by
  classical
  borelize E
  let μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar
  have D : Set.Pairwise (T : Set ι) (fun i j => Disjoint (Metric.ball (x i) r) (Metric.ball (x j) r)) := by
    intro i hi j hj hij
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [two_mul] using hs i hi j hj hij
  have hsub : (⋃ i ∈ T, Metric.ball (x i) r) ⊆ Metric.ball a (ρ + r) := by
    refine Set.iUnion₂_subset fun i hi => ?_
    apply Metric.ball_subset_ball'
    rw [dist_eq_norm]
    linarith [hb i hi]
  have hI : (T.card : ℝ≥0∞) * ENNReal.ofReal (r ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal ((ρ + r) ^ Module.finrank ℝ E) * μ (Metric.ball 0 1) := by
    calc
      _ = μ (⋃ i ∈ T, Metric.ball (x i) r) := by
        rw [MeasureTheory.measure_biUnion_finset D (fun i _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball a (ρ + r)) := MeasureTheory.measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ (by linarith)
  have hJ := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos μ (0 : E) zero_lt_one).ne'
    MeasureTheory.measure_ball_lt_top.ne).1 hI
  have hK := ENNReal.toReal_le_of_le_ofReal (pow_nonneg (by linarith : 0 ≤ ρ + r) _) hJ
  simpa [ENNReal.toReal_ofReal (pow_nonneg hr.le _)] using hK

theorem colored_euclidean_power_packing
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : 0 < Module.finrank ℝ E)
    (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) {ι : Type*}
      (x : ι → E) (col : ι → Fin n) (T : Finset ι)
      (a : E) (ρ W : ℝ), 0 ≤ ρ → 0 < W →
      (∀ i ∈ T, ‖x i - a‖ ≤ ρ) →
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j → col i = col j →
        c ≤ ‖x i - x j‖ ^ Module.finrank ℝ E * W) →
      (T.card : ℝ) ≤ K * (n : ℝ) *
        (1 + ρ ^ Module.finrank ℝ E * W) := by
  classical
  let d := Module.finrank ℝ E
  let q : ℝ := c / 2 ^ d
  have hq : 0 < q := by dsimp [q]; positivity
  let K : ℝ := 2 ^ d * (1 + 1 / q)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n ι x col T a ρ W hρ hW hb hs
  let s : ℝ := (c / W) ^ ((d : ℝ)⁻¹)
  have hspos : 0 < s := by dsimp [s]; positivity
  have hspow : s ^ d = c / W := Real.rpow_inv_natCast_pow (by positivity) (Nat.ne_of_gt hd)
  let r : ℝ := s / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrpow : r ^ d * W = q := by
    dsimp [r, q]
    rw [div_pow, hspow]
    field_simp
  have hcolor (k : Fin n) : ((T.filter (fun i => col i = k)).card : ℝ) ≤
      K * (1 + ρ ^ d * W) := by
    let U := T.filter (fun i => col i = k)
    have hp : (U.card : ℝ) * r ^ d ≤ (ρ + r) ^ d := by
      apply ball_count x U a ρ r hρ hr
      · intro i hi
        exact hb i (Finset.mem_filter.mp hi).1
      · intro i hi j hj hij
        have hi' := Finset.mem_filter.mp hi
        have hj' := Finset.mem_filter.mp hj
        have hsep := hs i hi'.1 j hj'.1 hij (hi'.2.trans hj'.2.symm)
        have hpow : s ^ d ≤ ‖x i - x j‖ ^ d := by
          rw [hspow]
          exact (div_le_iff₀ hW).2 hsep
        have hle : s ≤ ‖x i - x j‖ := le_of_pow_le_pow_left₀ (Nat.ne_of_gt hd) (norm_nonneg _) hpow
        dsimp [r]
        linarith
    have hadd : (ρ + r) ^ d ≤ 2 ^ d * (ρ ^ d + r ^ d) := by
      calc
        _ ≤ 2 ^ (d - 1) * (ρ ^ d + r ^ d) := add_pow_le hρ hr.le d
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le d 1)) (by positivity)
    have hmul := mul_le_mul_of_nonneg_right (hp.trans hadd) hW.le
    have hbnd : (U.card : ℝ) * q ≤ 2 ^ d * (ρ ^ d * W + q) := by
      simpa only [mul_add, add_mul, mul_assoc, hrpow] using hmul
    have hz : 0 ≤ ρ ^ d * W := by positivity
    have hlast : 2 ^ d * (ρ ^ d * W + q) ≤ K * (1 + ρ ^ d * W) * q := by
      dsimp [K]
      field_simp
      nlinarith [mul_nonneg hq.le hz]
    exact (mul_le_mul_iff_left₀ hq).1 (hbnd.trans hlast)
  have hcard : T.card = ∑ k : Fin n, (T.filter (fun i => col i = k)).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise (s := T) (t := Finset.univ)
      (f := col) (by intro i hi; simp))
  rw [hcard, Nat.cast_sum]
  calc
    _ ≤ ∑ k : Fin n, K * (1 + ρ ^ d * W) := Finset.sum_le_sum (fun k _ => hcolor k)
    _ = _ := by simp [d, mul_comm, mul_left_comm, mul_assoc]

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
open ArithmeticGramSteps

 def aliasTrace (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : F →+ PoissonArch.Space F :=
  (PoissonArch.traceAdapter F).toAddMonoidHom.comp
    ((PoissonArch.infiniteAdeleToSpace F).toAddMonoidHom.comp
      ((RingHom.fst _ _).comp (sLocalDiagonal F S)).toAddMonoidHom)

private theorem aliasTrace_coordinates (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (t : F) :
    mixedEmbedding.euclidean.toMixed F
      ((PoissonArch.traceAdapter F).symm (aliasTrace F S t)) = mixedEmbedding F t := by
  change mixedEmbedding.euclidean.toMixed F
    ((PoissonArch.traceAdapter F).symm ((PoissonArch.traceAdapter F) _)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  change mixedEmbedding.euclidean.toMixed F
    (PoissonArch.infiniteAdeleToSpace F (algebraMap F (InfiniteAdeleRing F) t)) = _
  rw [PoissonArch.infiniteAdeleToSpace_coordinates]
  exact (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F) (x := t)).symm

private theorem place_le_mixed_norm (F : Type) [Field F] [NumberField F]
    (x : mixedEmbedding.mixedSpace F) (v : InfinitePlace F) :
    mixedEmbedding.normAtPlace v x ≤ ‖x‖ := by
  by_cases hv : v.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hv]
    exact (norm_le_pi_norm x.1 ⟨v, hv⟩).trans (norm_fst_le x)
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)]
    exact (norm_le_pi_norm x.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩).trans
      (norm_snd_le x)

theorem same_color_alias_power_separation
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (k : (v : S) → ℤ)
    (C : ℝ) (hC : 0 < C)
    (hfinite : ∀ t : F,
      (∀ (x : PoissonFinite.Space F S), x ∈ PoissonS.finiteBall F S k →
        ∀ v : S, e v (x v * algebraMap F (v.val.adicCompletion F) t) = 1) →
      (∏ v : S, NumberField.FinitePlace.mk v.val t) ≤ C)
    (g : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) → F)
    (hg : ∀ ν, PoissonArch.traceAdapter F
      (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (g ν)).1) =
        (ν : PoissonArch.Space F))
    (hgfinite : ∀ ν (x : PoissonFinite.Space F S),
      x ∈ PoissonS.finiteBall F S k → ∀ v : S,
        e v (x v * algebraMap F (v.val.adicCompletion F) (g ν)) = 1)
    {n : ℕ} (col : F → Fin n)
    (hcolor : ∀ ν μ, col (g ν) = col (g μ) →
      ∃ m : sIntegerRing F S, g ν - g μ = (m : F)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : ℝ), 1 ≤ V →
      ∀ (p : ProbeSeparation.Presentation F S)
        (P : Finset (ProbeSeparation.ReducedPair F S)),
        (∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V) →
      ∀ (r : F → ProbeSeparation.Integers F S),
        (∀ (a : F) (x : PoissonFinite.Space F S),
          x ∈ PoissonS.finiteBall F S k → ∀ v : S,
            e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) = 1) →
      ∀ (β γ : ProbeSeparation.ReducedPair F S)
        (ν μ : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)),
        β ∈ P → γ ∈ P → (β, ν) ≠ (γ, μ) →
        col (g ν) = col (g μ) →
        c ≤ ‖(normalizedFrequency F S r (ProbeSeparation.value F p β) +
                  (ν : PoissonArch.Space F)) -
              (normalizedFrequency F S r (ProbeSeparation.value F p γ) +
                  (μ : PoissonArch.Space F))‖ ^ Module.finrank ℚ F * V ^ 2 := by
  let L := (mixedEmbedding.euclidean.toMixed F).toContinuousLinearMap.comp
    (PoissonArch.traceAdapter F).symm.toContinuousLinearMap
  let M : ℝ := max ‖L‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < M ^ Module.finrank ℚ F * C := mul_pos (pow_pos hM _) hC
  refine ⟨(M ^ Module.finrank ℚ F * C)⁻¹, inv_pos.mpr hD, ?_⟩
  intro V hV p P hP r hr β γ ν μ hβ hγ hne hcol
  let a := ProbeSeparation.value F p β
  let b := ProbeSeparation.value F p γ
  let t := (a + (r a : F) + g ν) - (b + (r b : F) + g μ)
  obtain ⟨m, hm⟩ := hcolor ν μ hcol
  let q : ProbeSeparation.Integers F S := r a - r b + m
  have ht : t = a - b + (q : F) := by
    change (a + (r a : F) + g ν) - (b + (r b : F) + g μ) =
      a - b + ((r a : F) - (r b : F) + (m : F))
    rw [← hm]
    ring
  have htfinite : ∀ x : PoissonFinite.Space F S,
      x ∈ PoissonS.finiteBall F S k → ∀ v : S,
        e v (x v * algebraMap F (v.val.adicCompletion F) t) = 1 := by
    intro x hx v
    dsimp [t]
    rw [map_sub, mul_sub, AddChar.map_sub_eq_div]
    have ha := hr a x hx v
    have hb := hr b x hx v
    rw [map_add, mul_add, AddChar.map_add_eq_mul, ha, hgfinite ν x hx v,
      map_add, mul_add, AddChar.map_add_eq_mul, hb, hgfinite μ x hx v]
    simp
  have hfin := hfinite t htfinite
  have hlow : 1 ≤ ProbeSeparation.productNorm F S t * V ^ 2 := by
    by_cases hbg : β = γ
    · subst γ
      have ht' : t = g ν - g μ := by dsimp [t, a, b]; ring
      have hq : q ≠ 0 := by
        intro hq
        have htzero : t = 0 := by simpa [hq, a, b] using ht
        have hgzero : g ν = g μ := sub_eq_zero.mp (ht'.symm.trans htzero)
        have hv : ν = μ := by
          apply Subtype.ext
          rw [← hg ν, ← hg μ, hgzero]
        exact hne (by rw [hv])
      have hp := probe_sinteger_product_norm_lower_bound F S q hq
      have htq : t = (q : F) := by simpa [a, b] using ht
      rw [← htq] at hp
      have hVs : 1 ≤ V ^ 2 := by nlinarith
      exact le_trans hp (le_mul_of_one_le_right (by linarith) hVs)
    · have hp := probe_reduced_fraction_separation F S p V hV P hP β γ hβ hγ hbg q
      rw [← ht] at hp
      rw [Real.rpow_neg (by linarith : 0 ≤ V), Real.rpow_two] at hp
      exact (inv_le_iff_one_le_mul₀ (by positivity : 0 < V ^ 2)).mp hp
  have harch : (∏ v : InfinitePlace F, v t ^ v.mult) ≤
      M ^ Module.finrank ℚ F * ‖aliasTrace F S t‖ ^ Module.finrank ℚ F := by
    have hplace (v : InfinitePlace F) : v t ≤ M * ‖aliasTrace F S t‖ := by
      calc
        v t = mixedEmbedding.normAtPlace v (mixedEmbedding F t) :=
          (mixedEmbedding.normAtPlace_apply v t).symm
        _ ≤ ‖mixedEmbedding F t‖ := place_le_mixed_norm F _ v
        _ = ‖L (aliasTrace F S t)‖ := by
          congr 1
          exact (aliasTrace_coordinates F S t).symm
        _ ≤ ‖L‖ * ‖aliasTrace F S t‖ := L.le_opNorm _
        _ ≤ M * ‖aliasTrace F S t‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    calc
      (∏ v : InfinitePlace F, v t ^ v.mult) ≤
          ∏ v : InfinitePlace F, (M * ‖aliasTrace F S t‖) ^ v.mult := by
        apply Finset.prod_le_prod₀
        · intro v _; positivity
        · intro v _; exact pow_le_pow_left₀ (apply_nonneg _ _) (hplace v) _
      _ = M ^ Module.finrank ℚ F * ‖aliasTrace F S t‖ ^ Module.finrank ℚ F := by
        rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, mul_pow]
  have hup : ProbeSeparation.productNorm F S t ≤
      (M ^ Module.finrank ℚ F * C) * ‖aliasTrace F S t‖ ^ Module.finrank ℚ F := by
    rw [ProbeSeparation.productNorm]
    have heq : (∏ v ∈ S, FinitePlace.mk v t) = ∏ v : S, FinitePlace.mk v.val t := by
      exact (Finset.prod_coe_sort S (fun v => FinitePlace.mk v t)).symm
    rw [heq]
    calc
      _ ≤ (M ^ Module.finrank ℚ F * ‖aliasTrace F S t‖ ^ Module.finrank ℚ F) * C :=
        mul_le_mul harch hfin (by positivity) (by positivity)
      _ = _ := by ring
  have hfreq : aliasTrace F S t =
      (normalizedFrequency F S r a + (ν : PoissonArch.Space F)) -
        (normalizedFrequency F S r b + (μ : PoissonArch.Space F)) := by
    simp only [t, map_sub]
    rw [map_add (aliasTrace F S) (a + (r a : F)) (g ν),
      map_add (aliasTrace F S) (b + (r b : F)) (g μ)]
    change (normalizedFrequency F S r a +
      PoissonArch.traceAdapter F (PoissonArch.infiniteAdeleToSpace F
        (sLocalDiagonal F S (g ν)).1)) -
      (normalizedFrequency F S r b +
      PoissonArch.traceAdapter F (PoissonArch.infiniteAdeleToSpace F
        (sLocalDiagonal F S (g μ)).1)) = _
    rw [hg ν, hg μ]
  apply (inv_le_iff_one_le_mul₀ hD).mpr
  rw [← hfreq]
  calc
    1 ≤ ProbeSeparation.productNorm F S t * V ^ 2 := hlow
    _ ≤ ((M ^ Module.finrank ℚ F * C) *
        ‖aliasTrace F S t‖ ^ Module.finrank ℚ F) * V ^ 2 :=
      mul_le_mul_of_nonneg_right hup (sq_nonneg V)
    _ = _ := by ring

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

private theorem coordinates (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) :
    ∃ g : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) → F,
      (∀ ν, g ν ∈ (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) * (PoissonS.ballFractionalIdeal F S k)⁻¹) ∧
      (∀ ν, PoissonArch.traceAdapter F (PoissonArch.minkowskiEmbedding F (g ν)) = (ν : PoissonArch.Space F)) := by
  let I : PoissonArch.NonzeroFractionalIdeal F := Units.mk0 (PoissonS.ballFractionalIdeal F S k) (PoissonS.ballFractionalIdeal_ne_zero F S k)
  have h (ν : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)) :
      (PoissonArch.traceAdapter F).symm (ν : PoissonArch.Space F) ∈ PoissonArch.idealTraceDual F I := by
    intro x hx
    have hv : (ν : PoissonArch.Space F) ∈ PoissonArch.dualLattice (PoissonArch.idealLattice F I) := by
      simpa only [I, ← PoissonS.ballArchLattice_eq] using ν.property
    rw [PoissonArch.dualLattice, LinearMap.BilinForm.mem_dualSubmodule] at hv
    have hm := (PoissonArch.mem_idealLattice F I _).mpr ⟨x, hx, rfl⟩
    have hh := hv _ hm
    simp only [innerₗ_apply_apply, Submodule.mem_one] at hh
    change ∃ n : ℤ, (n : ℝ) = _ at hh ⊢
    simpa only [PoissonArch.tracePairing_eq_inner, ContinuousLinearEquiv.apply_symm_apply, real_inner_comm] using hh
  have hex (ν : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)) :
      ∃ t : F, t ∈ (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) * (PoissonS.ballFractionalIdeal F S k)⁻¹ ∧
        PoissonArch.minkowskiEmbedding F t = (PoissonArch.traceAdapter F).symm (ν : PoissonArch.Space F) := by
    have hh := h ν
    rw [PoissonArch.idealTraceDual_eq] at hh
    exact (PoissonArch.mem_idealLattice F _ _).mp hh
  choose g hg heq using hex
  exact ⟨g, hg, fun ν => by rw [heq]; simp⟩
private theorem dual_le (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) (hk : ∀ v, k v ≤ 0) :
    (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) * (PoissonS.ballFractionalIdeal F S k)⁻¹ ≤
      (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) := by
  have h : 1 ≤ PoissonS.ballFractionalIdeal F S k := by
    apply Finset.one_le_prod
    intro v _
    exact one_le_zpow_of_nonpos₀ (bot_lt_iff_ne_bot.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot)) FractionalIdeal.coeIdeal_le_one (hk v)
  have hi : (PoissonS.ballFractionalIdeal F S k)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ h
  simpa using mul_le_mul_of_nonneg_left hi (show 0 ≤ (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) from bot_le)
private theorem finite_bound (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (hne : ∀ v, ∃ y, e v y ≠ 1) (k : S → ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : F,
      (∀ x : PoissonFinite.Space F S, x ∈ PoissonS.finiteBall F S k →
        ∀ v : S, e v (x v * algebraMap F (v.val.adicCompletion F) t) = 1) →
      (∏ v : S, FinitePlace.mk v.val t) ≤ C := by
  choose y hy using hne
  let R : S → ℝ := fun v => (v.val.asIdeal.absNorm : ℝ) ^ (-k v)
  have hR (v : S) : 0 < R v := zpow_pos (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors ⟨v.val.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.val.ne_bot⟩)) _
  let B : S → ℝ := fun v => ‖y v‖ / R v
  have hB (v : S) : 0 < B v := div_pos (norm_pos_iff.mpr (fun hz => hy v (by simp [hz]))) (hR v)
  refine ⟨∏ v, B v, Finset.prod_pos (fun v _ => hB v), ?_⟩
  intro t ht
  apply Finset.prod_le_prod₀
  · intro v _; rw [FinitePlace.mk_apply]; exact norm_nonneg _
  · intro v _
    rw [FinitePlace.mk_apply]
    change ‖algebraMap F (v.val.adicCompletion F) t‖ ≤ B v
    by_contra! hlarge
    let z := algebraMap F (v.val.adicCompletion F) t
    have hz : z ≠ 0 := by
      intro h0
      have : ‖z‖ = 0 := by rw [h0, norm_zero]
      change B v < ‖z‖ at hlarge
      rw [this] at hlarge
      exact (not_lt_of_ge (hB v).le) hlarge
    have hsmall : ‖y v / z‖ ≤ R v := by
      rw [norm_div]
      exact ((div_le_iff₀ (norm_pos_iff.mpr hz)).mpr
        (le_of_lt (by simpa only [mul_comm] using (div_lt_iff₀ (hR v)).mp hlarge)))
    have hx : (Pi.single v (y v / z) : PoissonFinite.Space F S) ∈ PoissonS.finiteBall F S k := by
      intro w
      by_cases hw : w = v
      · subst w; simpa only [Pi.single_eq_same, R] using hsmall
      · rw [Pi.single_eq_of_ne hw, norm_zero]
        exact (hR w).le
    have hh := ht _ hx v
    exact hy v (by simpa [z, hz] using hh)

private theorem arch_product (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (x : InfiniteAdeleRing F) :
    (∏ v : InfinitePlace F, (archTraceCharacter v (x v) : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x v)).re) : ℂ)) := by
  simp only [archTraceCharacter_of_isComplex _ (IsTotallyComplex.isComplex _),
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, Circle.coe_exp]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  ring

private theorem canonical_diagonal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (m : sIntegerRing F S) :
    (∏ v : InfinitePlace F, archTraceCharacter v (algebraMap F v.Completion (m : F))) *
      (∏ v : S, localFiniteCharacter F v.val
        (algebraMap F (v.val.adicCompletion F) (m : F))) = 1 := by
  have hfinite : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (m : F)) = 1 :=
    fun v hv => localFiniteCharacter_eq_one_of_mem_integers F v _
      ((mem_sIntegerRing_iff F S (m : F)).mp m.property v hv)
  have hsub : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (m : F))) ⊆
      (S : Set (HeightOneSpectrum (𝓞 F))) :=
    Function.mulSupport_subset_iff'.mpr hfinite
  have hfin := finprod_eq_prod_of_mulSupport_subset _ hsub
  have hcoe :
      (∏ v : S, localFiniteCharacter F v.val (algebraMap F (v.val.adicCompletion F) (m : F))) =
      ∏ v ∈ S, localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (m : F)) :=
    (Finset.prod_subtype S (fun _ => Iff.rfl)
      (fun w => localFiniteCharacter F w (algebraMap F (w.adicCompletion F) (m : F)))).symm
  rw [hcoe, ← hfin]
  exact traceCharacter_diagonal_product_formula F (m : F)

theorem trace_coordinates_and_finite_annihilator
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ))
    (htrace : ∀ m : sIntegerRing F S, χ (sIntegerDiagonal F S m) = 1)
    (k : (v : S) → ℤ) (hk : ∀ v, k v ≤ 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ t : F,
        (∀ (x : PoissonFinite.Space F S), x ∈ PoissonS.finiteBall F S k →
          ∀ v : S, e v (x v * algebraMap F (v.val.adicCompletion F) t) = 1) →
        (∏ v : S, NumberField.FinitePlace.mk v.val t) ≤ C) ∧
    ∃ g : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) → F,
      (∀ ν, g ν ∈ (PoissonArch.codifferentIdeal F :
          FractionalIdeal (𝓞 F)⁰ F) * (PoissonS.ballFractionalIdeal F S k)⁻¹) ∧
      (∀ ν, g ν ∈ (PoissonArch.codifferentIdeal F :
          FractionalIdeal (𝓞 F)⁰ F)) ∧
      (∀ ν, PoissonArch.traceAdapter F
        (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (g ν)).1) =
          (ν : PoissonArch.Space F)) ∧
      (∀ ν (x : PoissonFinite.Space F S),
        x ∈ PoissonS.finiteBall F S k → ∀ v : S,
          e v (x v * algebraMap F (v.val.adicCompletion F) (g ν)) = 1) := by
  letI : IsTotallyComplex F := primitive12_totallyComplex F ζ12 hζ12
  have heq : ∀ v : S, e v = localFiniteCharacter F v.val := by
    let P : PoissonFinite.Space F S → ℂ := fun x => ∏ v : S, (e v (x v) : ℂ)
    let Q : PoissonFinite.Space F S → ℂ := fun x =>
      ∏ v : S, (localFiniteCharacter F v.val (x v) : ℂ)
    have hP : Continuous P := by
      exact continuous_finset_prod _ (fun v _ => continuous_subtype_val.comp
        ((he v).comp (continuous_apply v)))
    have hQ : Continuous Q := by
      exact continuous_finset_prod _ (fun v _ => continuous_subtype_val.comp
        ((continuous_localFiniteCharacter F v.val).comp (continuous_apply v)))
    have hPQ : P = Q := by
      apply (PoissonSFiniteDensity.diagonal_denseRange F S).equalizer hP hQ
      funext m
      let A := ∏ v : InfinitePlace F, (archTraceCharacter v
        (algebraMap F v.Completion (m : F)) : ℂ)
      have hA : A ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro v _
        exact Circle.coe_ne_zero _
      have hp : A * P (PoissonSFiniteDensity.diagonal F S m) = 1 := by
        have ha := arch_product F (fun v => algebraMap F v.Completion (m : F))
        change A = _ at ha
        rw [ha]
        simpa only [P, PoissonSFiniteDensity.diagonal_apply,
          sIntegerDiagonal_apply, sLocalDiagonal_infinite, sLocalDiagonal_finite] using
          (hχ (sIntegerDiagonal F S m)).symm.trans (htrace m)
      have hq : A * Q (PoissonSFiniteDensity.diagonal F S m) = 1 := by
        have h := congrArg Circle.coeHom (canonical_diagonal F S m)
        simp only [map_mul, map_prod, map_one] at h
        exact h
      exact mul_left_cancel₀ hA (hp.trans hq.symm)
    intro v
    apply AddChar.ext
    intro x
    apply Subtype.ext
    have h := congrFun hPQ (Pi.single v x)
    have hp : P (Pi.single v x) = (e v x : ℂ) := by
      dsimp only [P]
      rw [Finset.prod_eq_single v]
      · simp
      · intro w _ hw
        simp [Pi.single_eq_of_ne hw]
      · simp
    have hq : Q (Pi.single v x) = (localFiniteCharacter F v.val x : ℂ) := by
      dsimp only [Q]
      rw [Finset.prod_eq_single v]
      · simp
      · intro w _ hw
        simp [Pi.single_eq_of_ne hw]
      · simp
    exact hp.symm.trans (h.trans hq)
  obtain ⟨g, hg, hcoord⟩ := coordinates F S k
  have hcodiff (ν : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)) :
      g ν ∈ (PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) :=
    dual_le F S k hk (hg ν)
  have hcoord' (ν : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)) :
      PoissonArch.traceAdapter F
        (PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (g ν)).1) =
          (ν : PoissonArch.Space F) := by
    have hd : PoissonArch.infiniteAdeleToSpace F (sLocalDiagonal F S (g ν)).1 =
        PoissonArch.minkowskiEmbedding F (g ν) := by
      apply (mixedEmbedding.euclidean.toMixed F).injective
      rw [PoissonArch.infiniteAdeleToSpace_coordinates]
      change InfiniteAdeleRing.ringEquiv_mixedSpace F ((sLocalDiagonal F S) (g ν)).1 =
        mixedEmbedding F (g ν)
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      ext v <;> simp [sLocalDiagonal_infinite, mixedEmbedding]
    rw [hd]
    exact hcoord ν
  have hne : ∀ v : S, ∃ y, e v y ≠ 1 := by
    intro v
    by_contra! h
    have hz : (1 : v.val.adicCompletion F) = 0 := by
      apply (localFiniteCharacter_nondegenerate F v.val 1).mp
      intro y
      simpa [← heq v] using h y
    exact one_ne_zero hz
  obtain ⟨C, hC, hbound⟩ := finite_bound F S e hne k
  refine ⟨C, hC, hbound, g, hg, hcodiff, hcoord', ?_⟩
  intro ν x hx v
  have hdual : PoissonFinite.diagonal F S (g ν) ∈
      PoissonS.finiteBallAnnihilator F S k := by
    rw [PoissonS.finiteBallAnnihilator_eq]
    intro w
    apply (PoissonS.ScaleShift.norm_ball_iff_valuation F w.val
      (-PoissonS.differentExponent F w.val - k w) _).mpr
    have hval := (PoissonS.ScaleShift.fractionalIdeal_mem_iff_valuations F _
      (mul_ne_zero (Units.ne_zero (PoissonArch.codifferentIdeal F))
        (inv_ne_zero (PoissonS.ballFractionalIdeal_ne_zero F S k))) (g ν)).mp (hg ν) w.val
    have hc : FractionalIdeal.count F w.val
        ((PoissonArch.codifferentIdeal F : FractionalIdeal (𝓞 F)⁰ F) *
          (PoissonS.ballFractionalIdeal F S k)⁻¹) =
        -PoissonS.differentExponent F w.val - k w := by
      rw [FractionalIdeal.count_mul F w.val
        (Units.ne_zero (PoissonArch.codifferentIdeal F))
        (inv_ne_zero (PoissonS.ballFractionalIdeal_ne_zero F S k)),
        PoissonArch.codifferentIdeal_eq_inv_different, FractionalIdeal.count_inv,
        FractionalIdeal.count_inv, PoissonS.ScaleShift.count_ballFractionalIdeal,
        dif_pos w.property]
      rfl
    rw [hc] at hval
    exact (HeightOneSpectrum.adicCompletion.valued_coe F w.val (g ν)).trans_le hval
  have hs : (Pi.single v (x v) : PoissonFinite.Space F S) ∈
      PoissonS.finiteBall F S k := by
    intro w
    by_cases hw : w = v
    · subst w
      simpa using hx v
    · rw [Pi.single_eq_of_ne hw, norm_zero]
      exact (zpow_pos (by exact_mod_cast
        (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm w.val))) _).le
  have ht := hdual (Pi.single v (x v)) hs
  rw [PoissonS.finiteBallTraceCharacter_apply] at ht
  have hp : (∏ w : S, localFiniteCharacter F w.val
      ((Pi.single v (x v) : PoissonFinite.Space F S) w *
        PoissonFinite.diagonal F S (g ν) w)) =
      localFiniteCharacter F v.val (x v * algebraMap F (v.val.adicCompletion F) (g ν)) := by
    rw [Finset.prod_eq_single v]
    · rw [Pi.single_eq_same]
      rfl
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
  rw [heq v]
  exact hp.symm.trans ht

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramPacking

end

section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical

theorem dual_alias_ball_finite
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : (v : S) → ℤ)
    (c : PoissonArch.Space F) (ρ : ℝ) :
    {z : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) |
       ‖(z : PoissonArch.Space F) - c‖ ≤ ρ}.Finite := by
  rw [PoissonS.ballArchLattice_eq F S k]
  let L := PoissonArch.idealLattice F
      (Units.mk0 (PoissonS.ballFractionalIdeal F S k)
        (PoissonS.ballFractionalIdeal_ne_zero F S k))
  change {z : PoissonArch.dualLattice L | ‖(z : PoissonArch.Space F) - c‖ ≤ ρ}.Finite
  letI : DiscreteTopology L := inferInstance
  letI : IsZLattice ℝ L := inferInstance
  letI : DiscreteTopology (PoissonArch.dualLattice L).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (PoissonArch.dualLattice L))
  letI : DiscreteTopology ↥(PoissonArch.dualLattice L : Set (PoissonArch.Space F)) :=
    inferInstanceAs (DiscreteTopology (PoissonArch.dualLattice L))
  have hclosed : IsClosed (PoissonArch.dualLattice L : Set (PoissonArch.Space F)) :=
    AddSubgroup.isClosed_of_discreteTopology (U := (PoissonArch.dualLattice L).toAddSubgroup)
  have hd : DiscreteTopology ↥(PoissonArch.dualLattice L) := inferInstance
  have hfin : (Metric.closedBall c ρ ∩
      (PoissonArch.dualLattice L : Set (PoissonArch.Space F))).Finite :=
    Metric.finite_isBounded_inter_isClosed
      (DiscreteTopology.isDiscrete (s := (PoissonArch.dualLattice L : Set (PoissonArch.Space F))))
      Metric.isBounded_closedBall hclosed
  have hpre := hfin.preimage (f := fun z : PoissonArch.dualLattice L =>
      (z : PoissonArch.Space F)) Subtype.val_injective.injOn
  apply hpre.subset
  intro z hz
  exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, z.property⟩

theorem dual_alias_family_finite
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (k : (v : S) → ℤ)
    {ι : Type*} [Finite ι] (b : ι → PoissonArch.Space F) (α : ι) (ρ : ℝ) :
    ∃ T : Finset (ι × PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)),
      ∀ z, z ∈ T ↔ ‖(z.2 : PoissonArch.Space F) - (b α - b z.1)‖ ≤ ρ := by
  classical
  let A := fun i : ι => {z : PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) |
      ‖(z : PoissonArch.Space F) - (b α - b i)‖ ≤ ρ}
  have hA : ∀ i, (A i).Finite := fun i => dual_alias_ball_finite F S k (b α - b i) ρ
  have hf : (⋃ i : ι, (fun z => (i, z)) '' A i).Finite :=
    Set.finite_iUnion (fun i => (hA i).image (fun z => (i, z)))
  refine ⟨hf.toFinset, fun z => ?_⟩
  rw [Set.Finite.mem_toFinset]
  simp only [Set.mem_iUnion, Set.mem_image, Prod.mk.injEq, A, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨z.1, z.2, hz, rfl⟩

theorem trace_dual_alias_packing
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ))
    (htrace : ∀ m : sIntegerRing F S, χ (sIntegerDiagonal F S m) = 1)
    (k : (v : S) → ℤ) (hk : ∀ v, k v ≤ 0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (V ρ : ℝ), 1 ≤ V → 0 ≤ ρ →
      ∀ (p : ProbeSeparation.Presentation F S)
        (P : Finset (ProbeSeparation.ReducedPair F S)),
        (∀ α ∈ P, ProbeSeparation.denominatorNorm F α ≤ V) →
        ∀ r : F → ProbeSeparation.Integers F S,
        (∀ (a : F) (x : PoissonFinite.Space F S),
          x ∈ PoissonS.finiteBall F S k → ∀ v : S,
            e v (x v * algebraMap F (v.val.adicCompletion F) (a + (r a : F))) = 1) →
        let b := fun α : ↥P => normalizedFrequency F S r (ProbeSeparation.value F p α.val);
        ∀ α : ↥P, ∃ T : Finset (↥P ×
            PoissonArch.dualLattice (PoissonS.ballArchLattice F S k)),
          (∀ z, z ∈ T ↔ ‖(z.2 : PoissonArch.Space F) - (b α - b z.1)‖ ≤ ρ) ∧
          (T.card : ℝ) ≤ D * (1 + ρ ^ Module.finrank ℚ F * V ^ 2) := by
  classical
  obtain ⟨C, hC, hfinite, g, hgideal, hgcodiff, hg, hgfinite⟩ :=
    ArithmeticGramPacking.trace_coordinates_and_finite_annihilator
      F ζ12 hζ12 S e he χ hχ htrace k hk
  obtain ⟨n, hn, col, hcol⟩ := ArithmeticGramPacking.codifferent_finite_colors F
  have hcolor : ∀ ν μ, col (g ν) = col (g μ) →
      ∃ m : sIntegerRing F S, g ν - g μ = (m : F) := by
    intro ν μ h
    obtain ⟨m, hm⟩ := hcol (g ν) (g μ) (hgcodiff ν) (hgcodiff μ) h
    refine ⟨⟨(m : F), ?_⟩, hm⟩
    exact ((S : Set (HeightOneSpectrum (𝓞 F))).integer F).algebraMap_mem m
  obtain ⟨c, hc, hsep⟩ :=
    ArithmeticGramPacking.same_color_alias_power_separation
      F S e k C hC hfinite g hg hgfinite col hcolor
  have hd : 0 < Module.finrank ℝ (PoissonArch.Space F) := by
    rw [NumberField.mixedEmbedding.euclidean.finrank]
    exact Module.finrank_pos
  obtain ⟨K, hK, hpack⟩ :=
    ArithmeticGramPacking.colored_euclidean_power_packing
      (PoissonArch.Space F) hd c hc
  refine ⟨K * (n : ℝ), mul_nonneg hK (Nat.cast_nonneg n), ?_⟩
  intro V ρ hV hρ p P hP r hr
  dsimp only
  let b : ↥P → PoissonArch.Space F := fun β =>
    normalizedFrequency F S r (ProbeSeparation.value F p β.val)
  intro α
  obtain ⟨T, hT⟩ := dual_alias_family_finite F S k b α ρ
  refine ⟨T, hT, ?_⟩
  let x : ↥P × PoissonArch.dualLattice (PoissonS.ballArchLattice F S k) →
      PoissonArch.Space F := fun z => b z.1 + (z.2 : PoissonArch.Space F)
  have hball : ∀ z ∈ T, ‖x z - b α‖ ≤ ρ := by
    intro z hz
    have hh := (hT z).mp hz
    have heq : x z - b α = (z.2 : PoissonArch.Space F) - (b α - b z.1) := by
      dsimp [x]
      abel
    rwa [heq]
  have hs : ∀ z ∈ T, ∀ w ∈ T, z ≠ w →
      col (g z.2) = col (g w.2) →
      c ≤ ‖x z - x w‖ ^ Module.finrank ℝ (PoissonArch.Space F) * V ^ 2 := by
    intro z hz w hw hne hsame
    rw [NumberField.mixedEmbedding.euclidean.finrank]
    apply hsep V hV p P hP r hr z.1.val w.1.val z.2 w.2
      z.1.property w.1.property ?_ hsame
    intro heq
    apply hne
    have hfst : z.1.val = w.1.val := (Prod.mk.inj heq).1
    have hsnd : z.2 = w.2 := (Prod.mk.inj heq).2
    exact Prod.ext (Subtype.ext hfst) hsnd
  have hW : 0 < V ^ 2 := by nlinarith
  have hb := hpack n x (fun z => col (g z.2)) T (b α) ρ (V ^ 2)
    hρ hW hball hs
  simpa only [NumberField.mixedEmbedding.euclidean.finrank] using hb

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds.ArithmeticGramSteps

end
