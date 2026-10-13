module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Kernel

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ActualRowCount

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem frequency_ext (f g : CorrectionFactors.Frequency D.context) (hu : f.u = g.u)
    (hI : f.ideal = g.ideal) : f = g := by
  obtain ⟨u, I, a, b, c⟩ := f
  obtain ⟨u', I', a', b', c'⟩ := g
  have hu' : u = u' := hu
  have hI' : I = I' := hI
  subst hu'
  subst hI'
  rfl

theorem ideal_eq_of_u_eq {r r' : D.Row} (h : r.u = r'.u) :
    r.toFrequency.ideal = r'.toFrequency.ideal := by
  apply D.recipe.A.exteriorIdealEquiv.injective
  apply Subtype.ext
  rw [D.recipe.A.exteriorIdealEquiv_apply, D.recipe.A.exteriorIdealEquiv_apply,
    ← r.toFrequency.generates.2, ← r'.toFrequency.generates.2]
  exact congrArg (fun x : D.recipe.A.R => Ideal.span {x}) h

theorem row_u_injective : Function.Injective (FixedData.Row.u (D := D)) := by
  intro r r' h
  apply FixedData.Row.ext
  exact frequency_ext D _ _ h (ideal_eq_of_u_eq D h)

theorem q_eq (r : D.Row) : D.q r = D.recipe.A.exteriorNorm r.toFrequency.ideal := by
  unfold FixedData.q
  change (Nat.card (D.recipe.A.R ⧸ Ideal.span {r.toFrequency.u}) : ℝ) = _
  rw [r.toFrequency.generates.2, D.recipe.A.exteriorResidue_card]
  rfl

theorem one_le_q (r : D.Row) : 1 ≤ D.q r := by
  rw [q_eq]
  exact idealNorm_ge_one _ r.toFrequency.ideal.property.1

def principalRow : D.Row :=
  ⟨⟨1, ⟨⊤, top_ne_bot, by simp⟩,
    ⟨one_ne_zero, by
      change Ideal.span {(1 : D.recipe.A.R)} = Ideal.map _ ⊤
      rw [Ideal.map_top, Ideal.span_singleton_one]⟩,
    by
      have h : Units.mk0 (((1 : D.recipe.A.R) : F)) (by simp) = 1 := Units.ext (by simp)
      change D.recipe.A.sClass _ ∈ _
      rw [h, map_one]
      exact one_mem _,
    by
      intro p
      have h : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
        rw [← Ideal.one_eq_top]
        exact UniqueFactorizationMonoid.normalizedFactors_one
      change (UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F))).count _ < 6
      rw [h]
      simp⟩,
    ⟨one_ne_zero, D.recipe.probe.frequencies.containsOne⟩⟩

@[simp] theorem principalRow_u : (principalRow D).u = 1 := rfl

theorem exists_principal_row : ∃ r : D.Row, r.u = 1 := ⟨principalRow D, rfl⟩

theorem principal_row_unique {r r' : D.Row} (h : r.u = 1) (h' : r'.u = 1) : r = r' :=
  row_u_injective D (h.trans h'.symm)

theorem eq_principalRow {r : D.Row} (h : r.u = 1) : r = principalRow D :=
  principal_row_unique D h rfl

theorem u_eq_one_iff {r : D.Row} : r.u = 1 ↔ r = principalRow D :=
  ⟨eq_principalRow D, fun h => by rw [h]; exact principalRow_u D⟩

theorem q_principalRow : D.q (principalRow D) = 1 := by
  rw [q_eq]
  change (Ideal.absNorm (⊤ : Ideal (𝓞 F)) : ℝ) = 1
  simp [Ideal.absNorm_top]

theorem q_eq_one_of_principal {r : D.Row} (h : r.u = 1) : D.q r = 1 := by
  rw [eq_principalRow D h]; exact q_principalRow D

theorem exists_dyad (r : D.Row) : ∃ k : ℕ, r ∈ PoissonKernel.dyadRows D ((2 : ℝ) ^ k) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (one_le_q D r) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨n, h1, ?_⟩
  rw [pow_succ] at h2
  linarith

theorem univ_eq_iUnion_dyadRows :
    (Set.univ : Set D.Row) = ⋃ k : ℕ, PoissonKernel.dyadRows D ((2 : ℝ) ^ k) := by
  ext r
  simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
  exact exists_dyad D r

def toProbeFrequency (r : D.Row) : PrincipalMellinComparison.Frequency D.recipe :=
  ⟨⟨r.u, r.isRep.choose⟩, r.isRep.choose_spec⟩

theorem toProbeFrequency_injective : Function.Injective (toProbeFrequency D) := by
  intro r r' h
  have := congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe =>
    (x.val.val : D.recipe.A.R)) h
  exact row_u_injective D this

theorem frequencyNorm_toProbeFrequency (r : D.Row) :
    PrincipalMellinComparison.frequencyNorm D.recipe (toProbeFrequency D r) = D.q r := rfl

theorem count_nonprincipal_lt : ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
    {r : D.Row | r.u ≠ 1 ∧ D.q r < X}.Finite ∧
    ((Set.ncard {r : D.Row | r.u ≠ 1 ∧ D.q r < X} : ℝ) ≤ K * X) := by
  obtain ⟨K, Dy, hK, hdy, hcov⟩ :=
    PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads.actual_complete_frequency_dyads
      D.recipe
  refine ⟨2 * K, by positivity, fun X hX => ?_⟩
  have hex : ∃ n : ℕ, X ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X (one_lt_two : (1 : ℝ) < 2)
    exact ⟨n, hn.le⟩
  obtain ⟨M, hM, hmin⟩ : ∃ M : ℕ, X ≤ (2 : ℝ) ^ M ∧ ∀ m < M, ¬ X ≤ (2 : ℝ) ^ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hM2 : (2 : ℝ) ^ M < 2 * X := by
    rcases M with _ | m
    · rw [pow_zero]; linarith
    · have h := hmin m (Nat.lt_succ_self m)
      push_neg at h
      rw [pow_succ]; linarith
  have hgeom : ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 : ℝ) ^ j = 2 ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  let T : Finset (PrincipalMellinComparison.Frequency D.recipe) :=
    (Finset.range M).biUnion Dy
  have hTcard : (T.card : ℝ) ≤ K * (2 : ℝ) ^ M := by
    calc (T.card : ℝ) ≤ ∑ j ∈ Finset.range M, ((Dy j).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range M, K * (2 : ℝ) ^ j := by
          apply Finset.sum_le_sum
          intro j _
          obtain ⟨_, h2⟩ := hdy j
          exact h2
      _ = K * ∑ j ∈ Finset.range M, (2 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ K * (2 : ℝ) ^ M := by
          apply mul_le_mul_of_nonneg_left _ hK.le
          rw [hgeom]; linarith
  have hmaps : Set.MapsTo (toProbeFrequency D) {r : D.Row | r.u ≠ 1 ∧ D.q r < X}
      (↑T : Set (PrincipalMellinComparison.Frequency D.recipe)) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hne : toProbeFrequency D r ≠ PrincipalMellinComparison.principalFrequency D.recipe := by
      intro h
      apply hr1
      have := congrArg (fun x : PrincipalMellinComparison.Frequency D.recipe =>
        (x.val.val : D.recipe.A.R)) h
      exact this
    obtain ⟨j, hj⟩ := hcov _ hne
    obtain ⟨h1, _⟩ := hdy j
    obtain ⟨_, h3, _⟩ := h1 _ hj
    have hjM : j < M := by
      by_contra hcon
      push_neg at hcon
      have h4 : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hcon
      have h5 : PrincipalMellinComparison.frequencyNorm D.recipe (toProbeFrequency D r) =
          D.q r := frequencyNorm_toProbeFrequency D r
      linarith
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjM, hj⟩)
  have hinj : Set.InjOn (toProbeFrequency D) {r : D.Row | r.u ≠ 1 ∧ D.q r < X} :=
    (toProbeFrequency_injective D).injOn
  refine ⟨Set.Finite.of_injOn hmaps hinj T.finite_toSet, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn (toProbeFrequency D) hmaps hinj T.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have hle' : (Set.ncard {r : D.Row | r.u ≠ 1 ∧ D.q r < X} : ℝ) ≤ (T.card : ℝ) := by
    exact_mod_cast hle
  have h6 : K * (2 : ℝ) ^ M ≤ K * (2 * X) := mul_le_mul_of_nonneg_left hM2.le hK.le
  linarith

theorem count_lt : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
    {r : D.Row | D.q r < X}.Finite ∧ ((Set.ncard {r : D.Row | D.q r < X} : ℝ) ≤ C * X) := by
  obtain ⟨K, hK, hcount⟩ := count_nonprincipal_lt D
  refine ⟨K + 1, by positivity, fun X hX => ?_⟩
  obtain ⟨hfin, hcard⟩ := hcount X hX
  have hsub : {r : D.Row | D.q r < X} ⊆
      insert (principalRow D) {r : D.Row | r.u ≠ 1 ∧ D.q r < X} := by
    intro r hr
    by_cases h : r.u = 1
    · rw [eq_principalRow D h]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨h, hr⟩
  have hfin' := hfin.insert (principalRow D)
  refine ⟨hfin'.subset hsub, ?_⟩
  have h1 := Set.ncard_le_ncard hsub hfin'
  have h2 := Set.ncard_insert_le (principalRow D) {r : D.Row | r.u ≠ 1 ∧ D.q r < X}
  have h3 : (Set.ncard {r : D.Row | D.q r < X} : ℝ) ≤
      (Set.ncard {r : D.Row | r.u ≠ 1 ∧ D.q r < X} : ℝ) + 1 := by
    exact_mod_cast h1.trans h2
  linarith

theorem dyadRows_finite (U : ℝ) : (PoissonKernel.dyadRows D U).Finite := by
  obtain ⟨C, hC, hcount⟩ := count_lt D
  refine ((hcount (max 1 (2 * U)) (le_max_left _ _)).1).subset ?_
  intro r hr
  exact lt_of_lt_of_le hr.2 (le_max_right _ _)

theorem dyadRows_count : ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
    (PoissonKernel.dyadRows D U).Finite ∧
      ((Set.ncard (PoissonKernel.dyadRows D U) : ℝ) ≤ C * U) := by
  obtain ⟨C, hC, hcount⟩ := count_lt D
  refine ⟨2 * C, by positivity, fun U hU => ⟨dyadRows_finite D U, ?_⟩⟩
  obtain ⟨hfin, hcard⟩ := hcount (2 * U) (by linarith)
  have hsub : PoissonKernel.dyadRows D U ⊆ {r : D.Row | D.q r < 2 * U} := fun r hr => hr.2
  have h1 : (Set.ncard (PoissonKernel.dyadRows D U) : ℝ) ≤
      (Set.ncard {r : D.Row | D.q r < 2 * U} : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  linarith

theorem dyadRows_nonprincipal_count : ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
    (PoissonKernel.dyadRows D U \ PoissonKernel.principalRows D).Finite ∧
      ((Set.ncard (PoissonKernel.dyadRows D U \ PoissonKernel.principalRows D) : ℝ) ≤ C * U) := by
  obtain ⟨C, hC, hcount⟩ := dyadRows_count D
  refine ⟨C, hC, fun U hU => ?_⟩
  obtain ⟨hfin, hcard⟩ := hcount U hU
  refine ⟨hfin.subset Set.diff_subset, ?_⟩
  have h1 : (Set.ncard (PoissonKernel.dyadRows D U \ PoissonKernel.principalRows D) : ℝ) ≤
      (Set.ncard (PoissonKernel.dyadRows D U) : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard Set.diff_subset hfin
  linarith

end

end DedekindZetaZeroFree.Quantitative.ActualRowCount
