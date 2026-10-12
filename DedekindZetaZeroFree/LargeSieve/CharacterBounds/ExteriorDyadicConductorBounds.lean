module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveResidueQuotients
public import DedekindZetaZeroFree.Arithmetic.Ideals.SSupportedDyadicFactorization

@[expose] public section

namespace DedekindZetaZeroFree.Detector

noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain

def HasExteriorDyadicConductorSieve
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (C0 : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ (X U : ℝ), 1 ≤ X → 2 ≤ U →
    ∀ (n : ℕ) (omega : Fin n → PrimitiveFrequencyCharacter F),
      Pairwise (fun i j =>
        ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)) →
      (∀ i : Fin n, HasFixedFullSLocalTuple F A (omega i) sigma) →
      (∀ i : Fin n, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U) →
      ∀ c : A.Exterior →₀ ℂ,
        (∀ a ∈ c.support, a ∈ A.balancedDyadicIdeals X) →
        (∑ i : Fin n, ‖∑ a ∈ c.support, c a * (omega i).character a.val‖ ^ 2) ≤
          K * (X + U ^ 2) * ∑ a ∈ c.support, ‖c a‖ ^ 2

theorem hasExteriorDyadicConductorSieve_of_balancedSection
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (B : Subgroup A.V)
    (K_bal : Set A.G) (hK : IsCompact K_bal)
    (s : A.BalancedIdealSection B K_bal)
    (sigma : FixedSResidue.FullLocalCharacters A)
    (hSigma : FixedSResidue.HasFiniteOrder A sigma)
    (C0 : ℝ) (hC0 : 0 < C0) :
    HasExteriorDyadicConductorSieve F A sigma C0 := by
  obtain ⟨K, hK0, hbound⟩ :=
    detector_exterior_dyadic_conductor_sieve F A B K_bal hK sigma hSigma C0 hC0
  exact ⟨K, hK0, hbound s⟩

private theorem dyadic_arbitrary {F : Type} [Field F] [NumberField F]
    (A : SArithmeticData F) (sigma : FixedSResidue.FullLocalCharacters A) (C0 K : ℝ)
    (hK : ∀ (X U : ℝ), 1 ≤ X → 2 ≤ U →
      ∀ (n : ℕ) (omega : Fin n → PrimitiveFrequencyCharacter F),
      Pairwise (fun i j => ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)) →
      (∀ i, HasFixedFullSLocalTuple F A (omega i) sigma) →
      (∀ i, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U) →
      ∀ c : A.Exterior →₀ ℂ, (∀ a ∈ c.support, a ∈ A.balancedDyadicIdeals X) →
      (∑ i, ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2) ≤
        K * (X + U^2) * ∑ a ∈ c.support, ‖c a‖^2)
    {ι : Type} [Fintype ι] (omega : ι → PrimitiveFrequencyCharacter F)
    (hω : Pairwise (fun i j => ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)))
    (htype : ∀ i, HasFixedFullSLocalTuple F A (omega i) sigma)
    (X U : ℝ) (hX : 1 ≤ X) (hU : 2 ≤ U)
    (hcond : ∀ i, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U)
    (c : A.Exterior →₀ ℂ) (hc : ∀ a ∈ c.support, a ∈ A.balancedDyadicIdeals X) :
    (∑ i, ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2) ≤
      K * (X + U^2) * ∑ a ∈ c.support, ‖c a‖^2 := by
  let e := (Fintype.equivFin ι).symm
  have h := hK X U hX hU (Fintype.card ι) (omega ∘ e)
    (fun i j hij => hω (e.injective.ne hij)) (fun i => htype (e i))
    (fun i => hcond (e i)) c hc
  simpa only [Function.comp_apply,
    e.sum_comp (fun i => ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2)] using h
private theorem finite_cauchy_schwarz {ι : Type} (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖z i‖)^2 := by
      gcongr
      exact norm_sum_le s z
    _ ≤ _ := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖)

private theorem finite_partition_sum {α β M : Type} [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] (T : Finset α) (L : Finset β) (B : β → Finset α)
    (hsub : ∀ l ∈ L, B l ⊆ T)
    (huniq : ∀ a ∈ T, ∃! l : {l // l ∈ L}, a ∈ B l.val)
    (f : α → M) : (∑ l ∈ L, ∑ a ∈ B l, f a) = ∑ a ∈ T, f a := by
  classical
  choose label hlabel hunique using huniq
  let g : α → β := fun a => if ha : a ∈ T then (label a ha).val else Classical.arbitrary β
  have hf : ∀ l ∈ L, B l = T.filter (fun a => g a = l) := by
    intro l hl
    ext a
    simp only [Finset.mem_filter]
    constructor
    · intro ha
      have haT := hsub l hl ha
      refine ⟨haT, ?_⟩
      dsimp [g]
      rw [dif_pos haT]
      exact congrArg Subtype.val (hunique a haT ⟨l, hl⟩ ha).symm
    · rintro ⟨haT, hg⟩
      dsimp [g] at hg
      rw [dif_pos haT] at hg
      simpa only [← hg] using hlabel a haT
  calc
    _ = ∑ l ∈ L, ∑ a ∈ T with g a = l, f a := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hf l hl]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => by
      dsimp [g]
      rw [dif_pos ha]
      exact (label a ha).property) f
private theorem block_coefficients {F : Type} [Field F] [NumberField F]
    (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (h : SSupportedPartition.SupportedIdeal Sf)
    (B : Finset (NonzeroIdeal F))
    (hex : ∀ I ∈ B, ∃ a : SSupportedPartition.Exterior Sf, I.val = h.val.val * a.val)
    (b : NonzeroIdeal F → ℂ) :
    ∃ c : SSupportedPartition.Exterior Sf →₀ ℂ,
      (∀ a ∈ c.support, ∃ I ∈ B, I.val = h.val.val * a.val) ∧
      (∀ ω : PrimitiveFrequencyCharacter F,
        (∑ I ∈ B, b I * ω.character I.val) =
          ω.character h.val.val * (∑ a ∈ c.support, c a * ω.character a.val)) ∧
      (∑ a ∈ c.support, ‖c a‖^2) = ∑ I ∈ B, ‖b I‖^2 := by
  classical
  let f : SSupportedPartition.Exterior Sf → NonzeroIdeal F :=
    fun a => ⟨h.val.val * a.val, mul_ne_zero h.val.property a.property.1⟩
  have hf : Function.Injective f := by
    intro a a' he
    exact SSupportedPartition.mul_exterior_injective Sf h (congrArg Subtype.val he)
  let T := B.preimage f hf.injOn
  let c : SSupportedPartition.Exterior Sf →₀ ℂ := Finsupp.onFinset T
    (fun a => if a ∈ T then b (f a) else 0)
    (fun a ha => by by_contra hh; simp [hh] at ha)
  have hc : c.support ⊆ T := Finsupp.support_onFinset_subset
  have sum_transport {M : Type} [AddCommMonoid M] (g : NonzeroIdeal F → M) :
      (∑ a ∈ T, g (f a)) = ∑ I ∈ B, g I := by
    apply Finset.sum_bij (fun a _ => f a)
    · intro a ha
      exact Finset.mem_preimage.mp ha
    · intro a ha a' ha' he
      exact hf he
    · intro I hI
      obtain ⟨a, ha⟩ := hex I hI
      have he : f a = I := Subtype.ext ha.symm
      exact ⟨a, Finset.mem_preimage.mpr (he ▸ hI), he⟩
    · intro a ha
      rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨f a, Finset.mem_preimage.mp (hc ha), rfl⟩
  · intro ω
    rw [← sum_transport (fun I => b I * ω.character I.val)]
    have hsum : (∑ a ∈ c.support, c a * ω.character a.val) =
        ∑ a ∈ T, b (f a) * ω.character a.val := by
      calc
        _ = ∑ a ∈ T, c a * ω.character a.val := by
          apply Finset.sum_subset hc
          intro a ha hnot
          simp [Finsupp.notMem_support_iff.mp hnot]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [c, ha]
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    change b (f a) * ω.character (h.val.val * a.val) = _
    rw [ω.character.map_mul']
    ring
  · have hsum : (∑ a ∈ c.support, ‖c a‖^2) = ∑ a ∈ T, ‖b (f a)‖^2 := by
      calc
        _ = ∑ a ∈ T, ‖c a‖^2 := by
          apply Finset.sum_subset hc
          intro a ha hnot
          simp [Finsupp.notMem_support_iff.mp hnot]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [c, ha]
    exact hsum.trans (sum_transport (fun I => ‖b I‖^2))

theorem detector_logarithmic_sieve_gluing
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (C0 : ℝ) (hC0 : 0 < C0)
    (L_S : Set (FixedSResidue.FullLocalCharacters A)) (hL : L_S.Finite)
    (hDyadic : ∀ sigma ∈ L_S, HasExteriorDyadicConductorSieve F A sigma C0) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N U : ℝ), 2 ≤ N → 2 ≤ U →
        ∀ (n : ℕ) (omega : Fin n → PrimitiveFrequencyCharacter F),
          Pairwise (fun i j =>
            ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)) →
          (∀ i : Fin n, ∃ sigma ∈ L_S,
            HasFixedFullSLocalTuple F A (omega i) sigma) →
          (∀ i : Fin n, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U) →
          ∀ b : NonzeroIdeal F →₀ ℂ,
            (∀ I ∈ b.support, (Ideal.absNorm I.val : ℝ) ≤ N) →
            (∑ i : Fin n,
              ‖∑ I ∈ b.support, b I * (omega i).character I.val‖ ^ 2) ≤
              D * (1 + Real.log N) ^ (A.Sf.card + 1) * (N + U ^ 2) *
                ∑ I ∈ b.support, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨D0, hD0, hpartition⟩ := SSupportedPartition.finite_dyadic_partition (F := F) A.Sf
  choose K hKpos hKbound using hDyadic
  let Ks : FixedSResidue.FullLocalCharacters A → ℝ := fun sigma =>
    if h : sigma ∈ L_S then K sigma h else 0
  let Ksum : ℝ := ∑ sigma ∈ hL.toFinset, Ks sigma
  have hKs : ∀ sigma, 0 ≤ Ks sigma := by
    intro sigma
    dsimp [Ks]
    split_ifs with h
    · exact hKpos sigma h
    · rfl
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg (fun sigma _ => hKs sigma)
  refine ⟨2 * D0 * (Ksum + 1), by positivity, ?_⟩
  intro N U hN hU n omega hω htype hcond b hb
  obtain ⟨T, L, B, hT, hLbounds, hB, huniq, hcard, henergy⟩ := hpartition N hN
  have hsub : ∀ l ∈ L, B l ⊆ T := fun l hl I hI => ((hB l hl I).mp hI).1
  have hbs : b.support ⊆ T := fun I hI => (hT I).mpr (hb I hI)
  have hsum (f : NonzeroIdeal F → ℂ) :
      (∑ l ∈ L, ∑ I ∈ B l, b I * f I) = ∑ I ∈ b.support, b I * f I := by
    haveI : Nonempty (SSupportedPartition.SupportedIdeal A.Sf × ℕ) := by
      obtain ⟨ha, _, _⟩ := SSupportedPartition.factor_unique A.Sf (⟨1, one_ne_zero⟩ : NonzeroIdeal F)
      exact ⟨(ha.1, 0)⟩
    rw [finite_partition_sum T L B hsub huniq]
    symm
    apply Finset.sum_subset hbs
    intro I hI hn
    simp [Finsupp.notMem_support_iff.mp hn]
  have hE : (∑ l ∈ L, ∑ I ∈ B l, ‖b I‖^2) = ∑ I ∈ b.support, ‖b I‖^2 := by
    rw [henergy b]
    symm
    apply Finset.sum_subset hbs
    intro I hI hn
    simp [Finsupp.notMem_support_iff.mp hn]
  choose tag htag hfixed using htype
  have htagfin : ∀ i, tag i ∈ hL.toFinset := fun i => hL.mem_toFinset.mpr (htag i)
  have hblock : ∀ l ∈ L, ∀ sigma ∈ hL.toFinset,
      (∑ i : Fin n with tag i = sigma,
        ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2) ≤
        Ks sigma * (2 * N + U^2) * ∑ I ∈ B l, ‖b I‖^2 := by
    intro l hl sigma hsigma
    obtain ⟨c, hc, hsplit, hce⟩ := block_coefficients A.Sf l.1 (B l)
      (fun I hI => by
        obtain ⟨a, ha, hband⟩ := ((hB l hl I).mp hI).2
        exact ⟨a, ha⟩) b
    have hcband : ∀ a ∈ c.support, a ∈ A.balancedDyadicIdeals ((2 : ℝ)^l.2) := by
      intro a ha
      obtain ⟨I, hI, he⟩ := hc a ha
      obtain ⟨a', he', hband⟩ := ((hB l hl I).mp hI).2
      have haa : a = a' := SSupportedPartition.mul_exterior_injective A.Sf l.1 (he.symm.trans he')
      rw [← haa] at hband
      change (2 : ℝ)^l.2 / 2 < idealNorm a.val ∧ idealNorm a.val ≤ (2 : ℝ)^l.2
      unfold SSupportedPartition.DyadicBand at hband
      split_ifs at hband with hz
      · simp only [hz, pow_zero] at *
        rw [hband]
        norm_num
      · have hk : l.2 = (l.2-1)+1 := by omega
        rw [hk, pow_succ]
        constructor
        · nlinarith [hband.1]
        · rw [hk, pow_succ] at hband
          exact hband.2
    have hX : 1 ≤ (2 : ℝ)^l.2 := one_le_pow₀ (by norm_num)
    have hσ : sigma ∈ L_S := hL.mem_toFinset.mp hsigma
    have hbnd := dyadic_arbitrary A sigma C0 (K sigma hσ) (hKbound sigma hσ)
      (ι := {i : Fin n // tag i = sigma}) (fun i => omega i.val)
      (fun i j hij => hω (Subtype.val_injective.ne hij))
      (fun i => by simpa only [i.property] using hfixed i.val)
      ((2 : ℝ)^l.2) U hX hU (fun i => hcond i.val) c hcband
    have hnorm (i : Fin n) :
        ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2 ≤
          ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2 := by
      rw [hsplit (omega i), norm_mul]
      have hχ := RayUnitary.ray_character_norm_le_one F (omega i).conductor
        (omega i).conductor_ne_zero (omega i).character l.1.val.val
      have hmul := mul_le_mul_of_nonneg_right hχ
        (norm_nonneg (∑ a ∈ c.support, c a * (omega i).character a.val))
      simp only [one_mul] at hmul
      exact pow_le_pow_left₀ (by positivity) hmul 2
    have hfilter : (∑ i : Fin n with tag i = sigma,
        ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2) =
        ∑ i : {i : Fin n // tag i = sigma},
          ‖∑ a ∈ c.support, c a * (omega i.val).character a.val‖^2 := by
      apply Finset.sum_subtype
      simp
    calc
      _ ≤ ∑ i : Fin n with tag i = sigma,
          ‖∑ a ∈ c.support, c a * (omega i).character a.val‖^2 :=
        Finset.sum_le_sum (fun i _ => hnorm i)
      _ ≤ K sigma hσ * ((2 : ℝ)^l.2 + U^2) * ∑ a ∈ c.support, ‖c a‖^2 := by
        rw [hfilter]
        exact hbnd
      _ ≤ Ks sigma * (2 * N + U^2) * ∑ I ∈ B l, ‖b I‖^2 := by
        rw [hce]
        simp only [Ks, dif_pos hσ]
        gcongr
        · exact hKpos sigma hσ
        · exact (hLbounds l hl).2.2
  have hblockall : ∀ l ∈ L,
      (∑ i : Fin n, ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2) ≤
        Ksum * (2 * N + U^2) * ∑ I ∈ B l, ‖b I‖^2 := by
    intro l hl
    rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => htagfin i)
      (fun i => ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2)]
    calc
      _ ≤ ∑ sigma ∈ hL.toFinset,
          Ks sigma * (2 * N + U^2) * ∑ I ∈ B l, ‖b I‖^2 :=
        Finset.sum_le_sum (fun sigma hs => hblock l hl sigma hs)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hcs : (∑ i : Fin n,
      ‖∑ I ∈ b.support, b I * (omega i).character I.val‖^2) ≤
      (L.card : ℝ) * ∑ l ∈ L, ∑ i : Fin n,
        ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2 := by
    calc
      _ ≤ ∑ i : Fin n, (L.card : ℝ) * ∑ l ∈ L,
          ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← hsum (fun I => (omega i).character I.val)]
        exact finite_cauchy_schwarz L (fun l => ∑ I ∈ B l, b I * (omega i).character I.val)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    _ ≤ (L.card : ℝ) * ∑ l ∈ L, ∑ i : Fin n,
          ‖∑ I ∈ B l, b I * (omega i).character I.val‖^2 := hcs
    _ ≤ (L.card : ℝ) * ∑ l ∈ L,
          Ksum * (2 * N + U^2) * ∑ I ∈ B l, ‖b I‖^2 := by
      gcongr with l hl
      exact hblockall l hl
    _ = (L.card : ℝ) * (Ksum * (2 * N + U^2)) *
          ∑ I ∈ b.support, ‖b I‖^2 := by
      rw [← Finset.mul_sum, hE]
      ring
    _ ≤ (2 * D0 * (Ksum + 1)) * (1 + Real.log N) ^ (A.Sf.card + 1) *
          (N + U ^ 2) * ∑ I ∈ b.support, ‖b I‖ ^ 2 := by
      have hlog0 : 0 ≤ (1 + Real.log N)^(A.Sf.card+1) :=
        pow_nonneg (by linarith [Real.log_nonneg (show 1 ≤ N by linarith)]) _
      have hN0 : 0 ≤ N := by linarith
      have hU0 : 0 ≤ U^2 := sq_nonneg U
      have hfac : Ksum * (2 * N + U^2) ≤ 2 * (Ksum+1) * (N+U^2) := by
        nlinarith
      have hener0 : 0 ≤ ∑ I ∈ b.support, ‖b I‖^2 := by positivity
      calc
        _ ≤ (D0 * (1 + Real.log N)^(A.Sf.card+1)) *
              (Ksum * (2 * N + U^2)) * ∑ I ∈ b.support, ‖b I‖^2 := by
          gcongr
        _ ≤ (D0 * (1 + Real.log N)^(A.Sf.card+1)) *
              (2 * (Ksum+1) * (N+U^2)) * ∑ I ∈ b.support, ‖b I‖^2 := by
          gcongr
        _ = _ := by ring

private theorem logarithmic_power_absorption (m : ℕ) (hm : 0 < m)
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 2 ≤ N →
      (1 + Real.log N)^m ≤ C * N^e := by
  let d := e / (m : ℝ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < d := div_pos he hmR
  refine ⟨(1 + 1 / d)^m, pow_pos (by positivity) _, ?_⟩
  intro N hN
  have hN0 : 0 ≤ N := by linarith
  have hpow : 1 ≤ N^d := Real.one_le_rpow (by linarith) hd.le
  have hlog := Real.log_le_rpow_div hN0 hd
  have hbase : 1 + Real.log N ≤ (1 + 1 / d) * N^d := by
    calc
      1 + Real.log N ≤ N^d + N^d / d := add_le_add hpow hlog
      _ = (1 + 1 / d) * N^d := by ring
  have h := pow_le_pow_left₀
    (by linarith [Real.log_nonneg (show 1 ≤ N by linarith)]) hbase m
  rw [mul_pow] at h
  have hp : (N^d)^m = N^e := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    dsimp [d]
    field_simp
  rwa [hp] at h

theorem detector_logarithmic_sieve_gluing_epsilon
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (C0 : ℝ) (hC0 : 0 < C0)
    (L_S : Set (FixedSResidue.FullLocalCharacters A)) (hL : L_S.Finite)
    (hDyadic : ∀ sigma ∈ L_S, HasExteriorDyadicConductorSieve F A sigma C0)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
      ∀ (N U : ℝ), 2 ≤ N → 2 ≤ U →
        ∀ (n : ℕ) (omega : Fin n → PrimitiveFrequencyCharacter F),
          Pairwise (fun i j =>
            ¬ samePrimitiveFrequencyCharacter F (omega i) (omega j)) →
          (∀ i : Fin n, ∃ sigma ∈ L_S,
            HasFixedFullSLocalTuple F A (omega i) sigma) →
          (∀ i : Fin n, (Ideal.absNorm (omega i).conductor : ℝ) ≤ C0 * U) →
          ∀ b : NonzeroIdeal F →₀ ℂ,
            (∀ I ∈ b.support, (Ideal.absNorm I.val : ℝ) ≤ N) →
            (∑ i : Fin n,
              ‖∑ I ∈ b.support, b I * (omega i).character I.val‖ ^ 2) ≤
              C_epsilon * (N + U ^ 2) * (N * U) ^ epsilon *
                ∑ I ∈ b.support, ‖b I‖ ^ 2 := by
  obtain ⟨D, hD, hbound⟩ :=
    detector_logarithmic_sieve_gluing F A C0 hC0 L_S hL hDyadic
  obtain ⟨C, hC, hlog⟩ :=
    logarithmic_power_absorption (A.Sf.card + 1) (by omega) epsilon hepsilon
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro N U hN hU n omega hω htype hcond b hb
  have hfirst := hbound N U hN hU n omega hω htype hcond b hb
  have hNU : N ≤ N * U := by nlinarith
  have hpow : N ^ epsilon ≤ (N * U) ^ epsilon :=
    Real.rpow_le_rpow (by linarith) hNU hepsilon.le
  have hNUSq : 0 ≤ N + U ^ 2 := by positivity
  have henergy : 0 ≤ ∑ I ∈ b.support, ‖b I‖ ^ 2 := by positivity
  calc
    _ ≤ D * (1 + Real.log N) ^ (A.Sf.card + 1) * (N + U ^ 2) *
          ∑ I ∈ b.support, ‖b I‖ ^ 2 := hfirst
    _ ≤ (D * C) * (N + U ^ 2) * (N * U) ^ epsilon *
          ∑ I ∈ b.support, ‖b I‖ ^ 2 := by
      calc
        _ ≤ D * (C * N ^ epsilon) * (N + U ^ 2) *
              ∑ I ∈ b.support, ‖b I‖ ^ 2 := by gcongr; exact hlog N hN
        _ ≤ D * (C * (N * U) ^ epsilon) * (N + U ^ 2) *
              ∑ I ∈ b.support, ‖b I‖ ^ 2 := by gcongr
        _ = _ := by ring

end
end DedekindZetaZeroFree.Detector
