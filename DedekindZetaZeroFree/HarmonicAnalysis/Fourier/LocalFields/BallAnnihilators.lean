module

public import DedekindZetaZeroFree.Arithmetic.LocalFields.BallQuotients
public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy

@[expose] public section

noncomputable section

open scoped NumberField Classical WithZero Topology
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

theorem localDifferent_ne_bot (v : HeightOneSpectrum (𝓞 F)) :
    localDifferent F v ≠ ⊥ := by
  exact RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable_ne_bot
    (LocalConductor.base F v) (LocalConductor.target F v)

theorem exists_localDifferentExponent (v : HeightOneSpectrum (𝓞 F)) :
    ∃ d : ℕ, localDifferent F v =
      IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d := by
  letI := (LocalConductor.target F v).valuationSubring_isDiscreteValuationRing
  exact exists_maximalIdeal_pow_eq_of_principal _ (inferInstance) _ (localDifferent_ne_bot F v)

def localDifferentExponent (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Classical.choose (exists_localDifferentExponent F v)

theorem localDifferent_eq_maximalIdeal_pow (v : HeightOneSpectrum (𝓞 F)) :
    localDifferent F v =
      IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^
        localDifferentExponent F v := by
  exact Classical.choose_spec (exists_localDifferentExponent F v)

def localDifferentNorm (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Ideal.absNorm v.asIdeal ^ localDifferentExponent F v

 def re (v : HeightOneSpectrum (𝓞 F)) :
    (LocalConductor.target F v).valuationSubring ≃+* Valued.integer (v.adicCompletion F) where
  toFun x := ⟨x, (Set.ext_iff.mp (LocalConductor.target_integerRing_eq F v) x).mp x.property⟩
  invFun x := ⟨x, (Set.ext_iff.mp (LocalConductor.target_integerRing_eq F v) x).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
private theorem inte (v : HeightOneSpectrum (𝓞 F)) :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (LocalConductor.target F v).valuationSubring where
  hom_inj := Subtype.val_injective
  map_le_one x := (re F v x).property
  exists_of_le_one {x} hx := ⟨(re F v).symm ⟨x,hx⟩,rfl⟩
 def pi (v : HeightOneSpectrum (𝓞 F)) : (LocalConductor.target F v).valuationSubring :=
  (re F v).symm ⟨finiteCompletionUniformizer F v, by
    change Valued.v (finiteCompletionUniformizer F v) ≤ 1
    simp [finiteCompletionUniformizer_valuation]⟩
private theorem pi_irr (v : HeightOneSpectrum (𝓞 F)) : Irreducible (pi F v) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (pi F v)
  · exact fun h => finiteCompletionUniformizer_ne_zero F v (congrArg Subtype.val h)
  · ext a
    rw [← SetLike.mem_coe (p := Ideal.span {pi F v}),
      Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap (inte F v)]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (inte F v).isUnit_iff_valuation_eq_one]
    change Valued.v (a : v.adicCompletion F) ≠ 1 ↔ Valued.v (a : v.adicCompletion F) ≤ Valued.v (finiteCompletionUniformizer F v)
    rw [finiteCompletionUniformizer_valuation]
    have ha : Valued.v (a : v.adicCompletion F) ≤ 1 := (inte F v).map_le_one a
    generalize Valued.v (a : v.adicCompletion F) = g at *
    induction g using WithZero.expRecOn with
    | zero => simp
    | exp i =>
      have hi : i ≤ 0 := by simpa using ha
      have hh : WithZero.exp i ≠ 1 ↔ i < 0 := by
        rw [ne_iff_lt_iff_le.mpr ha]
        simp
      rw [hh, WithZero.exp_le_exp]
      omega
private theorem pow_mem (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (a : (LocalConductor.target F v).valuationSubring) :
    a ∈ IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d ↔
    (a : v.adicCompletion F) ∈ finiteCompletionBall F v d := by
  letI := (LocalConductor.target F v).valuationSubring_isDiscreteValuationRing
  rw [← SetLike.mem_coe, (inte F v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow (pi_irr F v)]
  change Valued.v (a : v.adicCompletion F) ≤ Valued.v (finiteCompletionUniformizer F v) ^ d ↔ _
  rw [finiteCompletionUniformizer_valuation, ← WithZero.exp_nsmul]
  simp
private theorem coe_pow (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) :
    (IsLocalization.coeSubmodule (v.adicCompletion F)
      (IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d) : Set (v.adicCompletion F)) =
    (finiteCompletionBall F v d : Set (v.adicCompletion F)) := by
  ext x
  change x ∈ IsLocalization.coeSubmodule (v.adicCompletion F)
    (IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d) ↔
    x ∈ finiteCompletionBall F v d
  rw [IsLocalization.mem_coeSubmodule]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (pow_mem F v d a).mp ha
  · intro hx
    have h0 : x ∈ finiteCompletionBall F v 0 :=
      ((finiteCompletionBall_le_iff F v 0 d).mpr (by omega)) hx
    have ha : x ∈ v.adicCompletionIntegers F := by
      rw [finiteCompletionBall_zero] at h0
      exact h0
    let a := (re F v).symm ⟨x,ha⟩
    exact ⟨a, (pow_mem F v d a).mpr hx, rfl⟩
private theorem inv_pow (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) :
    ((1 / IsLocalization.coeSubmodule (v.adicCompletion F)
      (IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d) :
      Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) : Set (v.adicCompletion F)) =
    (finiteCompletionBall F v (-(d : ℤ)) : Set (v.adicCompletion F)) := by
  have h1 (x : v.adicCompletion F) :
      x ∈ (1 : Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
      x ∈ finiteCompletionBall F v 0 := by
    rw [Submodule.mem_one]
    constructor
    · rintro ⟨a,rfl⟩
      exact (inte F v).map_le_one a
    · intro hx
      exact (inte F v).exists_of_le_one hx
  ext x
  change x ∈ (1 / IsLocalization.coeSubmodule (v.adicCompletion F)
    (IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d) :
    Submodule (LocalConductor.target F v).valuationSubring (v.adicCompletion F)) ↔
    x ∈ finiteCompletionBall F v (-(d : ℤ))
  rw [Submodule.mem_div_iff_forall_mul_mem]
  simp_rw [h1]
  change (∀ y, y ∈ IsLocalization.coeSubmodule (v.adicCompletion F)
    (IsLocalRing.maximalIdeal (LocalConductor.target F v).valuationSubring ^ d) →
    x * y ∈ finiteCompletionBall F v 0) ↔ _
  simp_rw [← SetLike.mem_coe, coe_pow]
  constructor
  · intro h
    have hh := h (finiteCompletionUniformizer F v ^ (d : ℤ))
      (by simpa using finiteCompletionUniformizer_mul_mem_ball F v d 1)
    change Valued.v (x * finiteCompletionUniformizer F v ^ (d : ℤ)) ≤ 1 at hh
    rw [map_mul, map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul] at hh
    simp only [zsmul_eq_mul, mul_neg, mul_one] at hh
    have hh' := (le_inv_mul_iff₀' WithZero.exp_pos).mpr hh
    simpa [← WithZero.exp_neg] using hh'
  · intro hx y hy
    change Valued.v x ≤ WithZero.exp (-(-(d : ℤ))) at hx
    change Valued.v y ≤ WithZero.exp (-(d : ℤ)) at hy
    change Valued.v (x * y) ≤ 1
    rw [map_mul]
    have h := mul_le_mul' hx hy
    simpa [← WithZero.exp_add] using h

theorem localFiniteAnnihilator_finiteCompletionBall
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localFiniteAnnihilator F v (finiteCompletionBall F v n) =
      finiteCompletionBall F v (-n - (localDifferentExponent F v : ℤ)) := by
  have hc : localIntegerAnnihilator F v =
      (finiteCompletionBall F v (-(localDifferentExponent F v : ℤ)) : Set (v.adicCompletion F)) := by
    rw [localIntegerAnnihilator_eq_inverse_different, localDifferent_eq_maximalIdeal_pow, inv_pow]
  ext y
  have hs : y ∈ localFiniteAnnihilator F v (finiteCompletionBall F v n) ↔
      finiteCompletionUniformizer F v ^ n * y ∈ localIntegerAnnihilator F v := by
    rw [mem_localFiniteAnnihilator]
    change (∀ u, u ∈ finiteCompletionBall F v n → localFiniteCharacter F v (u * y) = 1) ↔
      ∀ a, a ∈ v.adicCompletionIntegers F →
        localFiniteCharacter F v ((finiteCompletionUniformizer F v ^ n * y) * a) = 1
    constructor
    · intro h a ha
      have hmem : finiteCompletionUniformizer F v ^ n * a ∈ finiteCompletionBall F v n := by
        rw [← SetLike.mem_coe, finiteCompletionBall_eq_uniformizer_image F v _
          (finiteCompletionUniformizer_valuation F v)]
        exact ⟨a,ha,rfl⟩
      simpa [mul_assoc, mul_comm, mul_left_comm] using h _ hmem
    · intro h u hu
      obtain ⟨a,ha,rfl⟩ := (Set.ext_iff.mp
        (finiteCompletionBall_eq_uniformizer_image F v _
          (finiteCompletionUniformizer_valuation F v) n) u).mp hu
      simpa [mul_assoc, mul_comm, mul_left_comm] using h a ha
  rw [hs, hc]
  change Valued.v (finiteCompletionUniformizer F v ^ n * y) ≤
    WithZero.exp (-(-(localDifferentExponent F v : ℤ))) ↔ _
  rw [map_mul, map_zpow₀, finiteCompletionUniformizer_valuation, ← WithZero.exp_zsmul]
  simp only [zsmul_eq_mul, mul_neg, mul_one]
  rw [← le_inv_mul_iff₀ WithZero.exp_pos, ← WithZero.exp_neg, ← WithZero.exp_add]
  simp [add_comm]

theorem localFiniteAnnihilator_localFiniteAnnihilator_finiteCompletionBall
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    localFiniteAnnihilator F v
        (localFiniteAnnihilator F v (finiteCompletionBall F v n)) =
      finiteCompletionBall F v n := by
  rw [localFiniteAnnihilator_finiteCompletionBall, localFiniteAnnihilator_finiteCompletionBall]
  congr 1
  omega

theorem isLocallyConstant_localFiniteCharacter (v : HeightOneSpectrum (𝓞 F)) :
    IsLocallyConstant (localFiniteCharacter F v : v.adicCompletion F → Circle) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : {y : v.adicCompletion F | y - x ∈ finiteCompletionBall F v 0} ∈ 𝓝 x :=
    (isOpen_finiteCompletionBall_coset F v x 0).mem_nhds (by simp)
  filter_upwards [hn] with y hy
  have hi : y - x ∈ v.adicCompletionIntegers F := by
    rw [finiteCompletionBall_zero] at hy
    exact hy
  have ht := localFiniteCharacter_eq_one_of_mem_integers F v (y - x) hi
  have he := localFiniteCharacter_add F v (y - x) x
  simpa [ht] using he

theorem isLocallyConstant_localFiniteCharacter_neg_mul
    (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletion F) :
    IsLocallyConstant (fun y : v.adicCompletion F =>
      (localFiniteCharacter F v (-b * y) : ℂ)) := by
  exact ((isLocallyConstant_localFiniteCharacter F v).comp_continuous
    (by fun_prop : Continuous (fun y : v.adicCompletion F => -b * y))).comp
    (fun z : Circle => (z : ℂ))

theorem localDifferentExponent_eq_zero_of_not_mem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    localDifferentExponent F v = 0 := by
  have hv' : ¬v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
    intro h
    exact hv (hS h)
  have heq := localDifferent_eq_maximalIdeal_pow F v
  rw [localDifferent_eq_top_of_not_dvd_different F v hv'] at heq
  have h := (Ideal.pow_eq_top_iff.mp heq.symm)
  rcases h with hh | hh
  · exact False.elim ((IsLocalRing.maximalIdeal.isMaximal _).ne_top hh)
  · exact hh

end DedekindZetaZeroFree

end
