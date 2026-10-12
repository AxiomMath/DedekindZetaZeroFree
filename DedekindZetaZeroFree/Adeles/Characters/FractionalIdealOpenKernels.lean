module

public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open scoped nonZeroDivisors Classical

namespace DedekindZetaZeroFree.KPAdelicCharacter

def idealExponent (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (k : T → ℤ) (v : HeightOneSpectrum (RingOfIntegers F)) : ℤ :=
  if h : v ∈ T then k ⟨v, h⟩ else 0

def finiteIdealNeighborhood (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (k : T → ℤ) : Set (KPAdelicTopology.FiniteAdeles F) :=
  {a | ∀ v : HeightOneSpectrum (RingOfIntegers F),
    Valued.v (a v) ≤ WithZero.exp (-idealExponent F T k v)}

def diagonalIdealFiber (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (k : T → ℤ) : Set F :=
  {r | algebraMap F (KPAdelicTopology.FiniteAdeles F) r ∈
    finiteIdealNeighborhood F T k}

set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] IsDedekindDomain.FiniteAdeleRing NumberField.AdeleRing

variable (F : Type) [Field F] [NumberField F]
private lemma ball_open (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-k))
  have hn : (Valued.v.restrict a) ≠ 0 := by
    intro h
    have ha0 : a = 0 := (Valued.v.restrict.map_eq_zero_iff).mp h
    exact WithZero.exp_ne_zero (ha.symm.trans (by simp [ha0]))
  convert Valued.isOpen_closedBall (v.adicCompletion F) hn using 1
  ext x
  simp only [Set.mem_setOf_eq, Valuation.restrict_le_iff, ha]

private lemma exponent_nonneg (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ) (v) :
    0 ≤ idealExponent F T (fun w => k w) v := by
  unfold idealExponent
  split <;> positivity

private lemma bound_le_one (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ) (v) :
    WithZero.exp (-idealExponent F T (fun w => k w) v) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  exact neg_nonpos.mpr (exponent_nonneg F T k v)

lemma finiteIdealNeighborhood_open_nat (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ) :
    IsOpen (finiteIdealNeighborhood F T (fun w => k w)) := by
  let s : Set (KPAdelicTopology.FiniteAdeles F) :=
    {a | ∀ v : T, Valued.v (a v.val) ≤ WithZero.exp (-(k v : ℤ))}
  have hs : IsOpen s := by
    convert isOpen_iInter_of_finite (fun v : T => (ball_open F v.val (k v)).preimage
      (RestrictedProduct.continuous_eval v.val)) using 1
    ext a
    simp [s]
  have he : finiteIdealNeighborhood F T (fun w => k w) =
      s ∩ (KPAdelicTopology.integralAdeles F : Set _) := by
    ext a
    constructor
    · intro ha
      refine ⟨?_, ?_⟩
      · intro v
        simpa [finiteIdealNeighborhood, idealExponent, v.prop] using ha v.val
      · intro v
        exact (ha v).trans (bound_le_one F T k v)
    · rintro ⟨ha, hi⟩ v
      by_cases hv : v ∈ T
      · simpa [idealExponent, hv] using ha ⟨v, hv⟩
      · simpa [idealExponent, hv, HeightOneSpectrum.mem_adicCompletionIntegers] using hi v
  rw [he]
  exact hs.inter (KPAdelicTopology.integralAdeles_isOpen F)

lemma finiteIdealNeighborhood_basis_nat {U : Set (KPAdelicTopology.FiniteAdeles F)}
    (hU : U ∈ 𝓝 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ),
      finiteIdealNeighborhood F T (fun w => k w) ⊆ U := by
  let s := RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set _)) cofinite
  have hm : 𝓝 (0 : KPAdelicTopology.FiniteAdeles F) = map s (𝓝 0) := by
    have hzero : s 0 = 0 := by
      apply RestrictedProduct.ext
      intro i
      rfl
    rw [← hzero]
    exact RestrictedProduct.nhds_zero_eq_map_structureMap _
      (KPAdelicTopology.completionIntegers_isOpen F)
  rw [hm, Filter.mem_map, nhds_pi] at hU
  obtain ⟨T, t, ht, hts⟩ := Filter.mem_pi'.mp hU
  have hh (v : T) : ∃ n : ℕ,
      ∀ x : v.val.adicCompletionIntegers F, Valued.v (x : v.val.adicCompletion F) ≤
        WithZero.exp (-(n : ℤ)) → x ∈ t v.val := by
    have htv := ht v.val
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at htv
    obtain ⟨W, hW, hWt⟩ := htv
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hW
    have hn : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := by
      simpa using γ.ne_zero
    obtain ⟨n, hn'⟩ := WithZero.exists_exp_neg_natCast_lt hn
    refine ⟨n, fun x hx => hWt (hγ ?_)⟩
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hx.trans_lt hn'
  choose k hk using hh
  refine ⟨T, k, ?_⟩
  intro a ha
  have hi : ∀ v, a v ∈ v.adicCompletionIntegers F := by
    intro v
    exact (ha v).trans (bound_le_one F T k v)
  let x : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F := fun v => ⟨a v, hi v⟩
  have hx : x ∈ Set.pi (↑T) t := by
    intro v hv
    apply hk ⟨v, hv⟩
    simpa [x, idealExponent, Finset.mem_coe.mp hv] using ha v
  have hsx : s x = a := by
    apply RestrictedProduct.ext
    intro i
    rfl
  rw [← hsx]
  exact hts hx

 def fiberSubmodule (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ) :
    Submodule (𝓞 F) F where
  carrier := diagonalIdealFiber F T (fun w => k w)
  zero_mem' := by
    intro v
    change Valued.v (0 : v.adicCompletion F) ≤ _
    simp
  add_mem' := by
    intro a b ha hb v
    change Valued.v (algebraMap F (v.adicCompletion F) (a + b)) ≤ _
    rw [map_add]
    exact (Valued.v.map_add _ _).trans (max_le (ha v) (hb v))
  smul_mem' := by
    intro r a ha v
    change Valued.v (algebraMap F (v.adicCompletion F) ((algebraMap (𝓞 F) F r) * a)) ≤ _
    rw [map_mul, Valuation.map_mul]
    apply le_trans (mul_le_of_le_one_left zero_le ?_) (ha v)
    simpa only [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
      HeightOneSpectrum.valuation_of_algebraMap] using v.intValuation_le_one r

lemma diagonalIdealFiber_fractional_nat (T : Finset (HeightOneSpectrum (𝓞 F))) (k : T → ℕ) :
    ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      (I : Set F) = diagonalIdealFiber F T (fun w => k w) := by
  let M := fiberSubmodule F T k
  have hM : M ≤ (1 : Submodule (𝓞 F) F) := by
    intro a ha
    apply Submodule.mem_one.mpr
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one F a
    intro v
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (ha v).trans (bound_le_one F T k v)
  let I : FractionalIdeal (𝓞 F)⁰ F := ⟨M, FractionalIdeal.isFractional_of_le_one M hM⟩
  have hI : I ≠ 0 := by
    let J : Ideal (𝓞 F) := ∏ v : T, v.val.asIdeal ^ k v
    have hJ : J ≠ ⊥ := by
      exact Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ v.val.ne_bot)
    obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff J).mp hJ
    have hIa : algebraMap (𝓞 F) F a ∈ I := by
      intro v
      change Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ≤ _
      rw [← IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
        HeightOneSpectrum.valuation_of_algebraMap]
      by_cases hv : v ∈ T
      · simp only [idealExponent, dif_pos hv]
        apply (v.intValuation_le_pow_iff_mem a (k ⟨v,hv⟩)).mpr
        exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ ⟨v,hv⟩))) ha
      · simpa [idealExponent, hv] using v.intValuation_le_one a
    intro hz
    have hz' : algebraMap (𝓞 F) F a = 0 := by simpa [hz] using hIa
    exact hane ((IsFractionRing.injective (𝓞 F) F).eq_iff.mp (by simpa using hz'))
  exact ⟨Units.mk0 I hI, rfl⟩

end KPAdelicCharacter

theorem kp_adelic_character_open_kernel (F : Type) [Field F] [NumberField F]
    (χ : AddChar (KPAdelicTopology.Adeles F) Circle) (hχ : Continuous χ) :
    ∃ (T : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : T → ℤ)
      (I : (FractionalIdeal (RingOfIntegers F)⁰ F)ˣ),
      IsOpen (KPAdelicCharacter.finiteIdealNeighborhood F T k) ∧
      (∀ a : KPAdelicTopology.FiniteAdeles F,
        a ∈ KPAdelicCharacter.finiteIdealNeighborhood F T k → χ (0, a) = 1) ∧
      (I : FractionalIdeal (RingOfIntegers F)⁰ F) ≠ 0 ∧
      (I : Set F) = KPAdelicCharacter.diagonalIdealFiber F T k ∧
      DiscreteTopology (NumberField.mixedEmbedding.idealLattice F I) ∧
      IsZLattice ℝ (NumberField.mixedEmbedding.idealLattice F I) := by
  have he : ∀ᶠ x : KPAdelicTopology.FiniteAdeles F in 𝓝 0,
      χ (0, x) ∈ Circle.centeredArc (Real.pi / 2) := by
    apply (hχ.comp (continuous_const.prodMk continuous_id)).continuousAt.eventually
    apply (Circle.isOpen_centeredArc _).mem_nhds
    change χ (0, 0) ∈ Circle.centeredArc (Real.pi / 2)
    rw [show χ (0, 0) = 1 by exact χ.map_zero_eq_one,
      Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨T, k, hk⟩ := KPAdelicCharacter.finiteIdealNeighborhood_basis_nat F he
  obtain ⟨I, hI⟩ := KPAdelicCharacter.diagonalIdealFiber_fractional_nat F T k
  refine ⟨T, (fun v => k v), I, KPAdelicCharacter.finiteIdealNeighborhood_open_nat F T k,
    ?_, Units.ne_zero I, hI, inferInstance, inferInstance⟩
  intro a ha
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  have hn : ∀ m : ℕ, m • a ∈ KPAdelicCharacter.finiteIdealNeighborhood F T (fun v => k v) := by
    intro m
    induction m with
    | zero =>
      rw [zero_nsmul]
      intro v
      change Valued.v (0 : v.adicCompletion F) ≤ _
      simp
    | succ m hm =>
      intro v
      rw [succ_nsmul]
      change Valued.v ((m • a) v + a v) ≤ _
      exact (Valued.v.map_add _ _).trans (max_le (hm v) (ha v))
  have he' := hk (hn n)
  have heq : ((0, n • a) : KPAdelicTopology.Adeles F) = n • ((0, a) : KPAdelicTopology.Adeles F) := by
    apply Prod.ext <;> simp
  change χ (0, n • a) ∈ Circle.centeredArc (Real.pi / 2) at he'
  rw [heq] at he'
  exact (χ.map_nsmul_eq_pow n ((0, a) : KPAdelicTopology.Adeles F)) ▸ he'

end DedekindZetaZeroFree

end
