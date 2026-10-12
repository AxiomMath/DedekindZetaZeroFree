module

public import DedekindZetaZeroFree.Metaplectic.Weil.InverseUniformizerQuadraticIntegral
public import DedekindZetaZeroFree.CharacterSums.Gauss.SexticChineseRemainderReciprocity
public import DedekindZetaZeroFree.CharacterSums.Gauss.NormalizedSexticPowerIdentities

@[expose] public section

section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory
open scoped Pointwise WithZero

namespace DedekindZetaZeroFree.ExteriorGauss
noncomputable section
variable {F : Type} [Field F] [NumberField F]

private theorem residue_average
    (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    [Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers F))]
    (f : v.adicCompletion F → ℂ)
    (g : IsLocalRing.ResidueField (v.adicCompletionIntegers F) → ℂ)
    (hfg : ∀ x : v.adicCompletionIntegers F,
      f x = g (IsLocalRing.residue (v.adicCompletionIntegers F) x)) :
    (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), f x ∂μ) =
      (Ideal.absNorm v.asIdeal : ℂ)⁻¹ * ∑ z, g z := by
  let O := v.adicCompletionIntegers F
  let κ := IsLocalRing.ResidueField O
  let r : κ → O := fun z => (IsLocalRing.residue_surjective (R := O) z).choose
  have hr (z : κ) : IsLocalRing.residue O (r z) = z :=
    (IsLocalRing.residue_surjective (R := O) z).choose_spec
  let U : Set (v.adicCompletion F) := {x | ‖x‖ < 1}
  let b : κ → v.adicCompletion F := fun z => r z
  have hU : MeasurableSet U := (isOpen_lt continuous_norm continuous_const).measurableSet
  have hB : (O : Set (v.adicCompletion F)) = {x | ‖x‖ ≤ 1} := by
    ext x
    exact ⟨norm_le_one_of_mem_adicCompletionIntegers v,
      mem_adicCompletionIntegers_of_norm_le_one v⟩
  have hBfin : μ {x : v.adicCompletion F | ‖x‖ ≤ 1} ≠ ⊤ := by
    rw [← hB, hμ]; simp
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top hBfin
    (measure_mono (fun x hx => le_of_lt (show ‖x‖ < 1 from hx)))
  have hmax (x : O) : x ∈ IsLocalRing.maximalIdeal O ↔ ‖(x : v.adicCompletion F)‖ < 1 :=
    (Valuation.mem_maximalIdeal_iff (v.adicCompletion F)
      (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).trans
        Valued.toNormedField.norm_lt_one_iff.symm
  have hcoset (x : v.adicCompletion F) (hx : ‖x‖ ≤ 1) (z : κ) :
      x ∈ b z +ᵥ U ↔ IsLocalRing.residue O
        ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ = z := by
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hn : ‖x - b z‖ < 1 := by
        change ‖y‖ < 1 at hy
        have heq : x - b z = y := by change b z + y = x at hxy; rw [← hxy]; abel
        simpa only [heq] using hy
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O := (hmax _).mpr hn
      have heq := (IsLocalRing.residue_eq_zero_iff _).mpr hm
      rw [map_sub, hr, sub_eq_zero] at heq
      exact heq
    · intro heq
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        rw [map_sub, heq, hr, sub_self]
      have hn := (hmax ((⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z)).mp hm
      refine ⟨x - b z, hn, ?_⟩
      change b z + (x - b z) = x
      abel
  have hsub (z : κ) : b z +ᵥ U ⊆ {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
    change ‖b z + y‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_le_one_of_mem_adicCompletionIntegers v (r z).property) (le_of_lt hy))
  have hcover : {x : v.adicCompletion F | ‖x‖ ≤ 1} = ⋃ z : κ, b z +ᵥ U := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨IsLocalRing.residue O
        ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩, (hcoset x hx _).mpr rfl⟩
    · intro hx
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
      exact hsub z hz
  have hdisj : Pairwise (fun z w : κ => Disjoint (b z +ᵥ U) (b w +ᵥ U)) := by
    intro z w hzw
    apply Set.disjoint_left.mpr
    intro x hxz hxw
    have hx := hsub z hxz
    exact hzw (((hcoset x hx z).mp hxz).symm.trans ((hcoset x hx w).mp hxw))
  have he (z : κ) : Set.EqOn f (fun _ => g z) (b z +ᵥ U) := by
    intro x hx
    have hxB := hsub z hx
    rw [hfg ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hxB⟩,
      (hcoset x hxB z).mp hx]
  have hfin (z : κ) : μ (b z +ᵥ U) ≠ ⊤ := by simpa only [measure_vadd] using hUfin
  have hint (z : κ) : IntegrableOn f (b z +ᵥ U) μ :=
    (integrableOn_const (hfin z) (C := g z)).congr_fun (he z).symm (hU.const_vadd (b z))
  have hcard : Fintype.card κ = Ideal.absNorm v.asIdeal := by
    let e := (finitePlaceIdealResidueEquivCompletion v).trans
      (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr e.toEquiv, Ideal.absNorm_apply]
    rfl
  have hmass : μ.real U = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    have hm : μ.real {x : v.adicCompletion F | ‖x‖ ≤ 1} =
        (Fintype.card κ : ℝ) * μ.real U := by
      rw [hcover, measureReal_iUnion_fintype hdisj (fun z => hU.const_vadd (b z)) hfin]
      simp only [Measure.real, measure_vadd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hB, Measure.real, hμ, ENNReal.toReal_one, hcard] at hm
    have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)))
    apply (mul_left_cancel₀ hq)
    rw [mul_inv_cancel₀ hq]
    exact hm.symm
  rw [hB, hcover, integral_iUnion_fintype (fun z => hU.const_vadd (b z)) hdisj hint]
  simp_rw [setIntegral_congr_fun (hU.const_vadd (b _)) (he _), integral_const]
  simp only [Measure.restrict_apply_univ, Measure.real, measure_vadd]
  change (∑ z, μ.real U • g z) = _
  rw [hmass, ← Finset.smul_sum]
  simp [Complex.real_smul]

theorem integer_quadratic_integral_eq_residue_sum
    (v : HeightOneSpectrum (𝓞 F))
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (a : (v.adicCompletion F)ˣ)
    (ha : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    [Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers F))]
    (θ : AddChar (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) Circle)
    (hθ : ∀ x : v.adicCompletionIntegers F,
      θ (IsLocalRing.residue (v.adicCompletionIntegers F) x) =
        ResidueTrace.localTraceCharacter v ((x : v.adicCompletion F) / (a : v.adicCompletion F))) :
    (Real.sqrt ‖(2 : v.adicCompletion F) * (a⁻¹ : (v.adicCompletion F)ˣ)‖ : ℂ) *
        (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
          (ResidueTrace.localTraceCharacter v
            ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ) ∂μ) =
      (Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℂ)⁻¹ *
        ∑ x : IsLocalRing.ResidueField (v.adicCompletionIntegers F), (θ (x ^ 2) : ℂ) := by
  have hnot : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    have hz : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h
    have hd : (ResidueTrace.rationalPrimeBelow v).val ∣ 2 :=
      (ringChar.spec (𝓞 F ⧸ v.asIdeal) 2).mp hz
    exact hgood (dvd_trans hd (by decide))
  have htwo : ‖(2 : v.adicCompletion F)‖ = 1 := by
    simpa only [map_ofNat] using (FinitePlace.norm_eq_one_iff_notMem F v (2 : 𝓞 F)).mpr hnot
  have hnorm : ‖(a : v.adicCompletion F)‖ =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def, ha,
      WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp),
      NNReal.coe_zpow]
    simp
  have hnormInv : ‖(2 : v.adicCompletion F) * (a⁻¹ : (v.adicCompletion F)ˣ)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [norm_mul, htwo, one_mul, Units.val_inv_eq_inv_val, norm_inv, hnorm, inv_inv]
  have havg := residue_average v μ hμ
    (fun x => (ResidueTrace.localTraceCharacter v
      ((a⁻¹ : (v.adicCompletion F)ˣ) * x ^ 2) : ℂ))
    (fun z => (θ (z ^ 2) : ℂ)) (by
      intro x
      have ht := hθ (x ^ 2)
      rw [map_pow] at ht
      rw [ht]
      congr 2
      simp only [Units.val_inv_eq_inv_val, SubmonoidClass.coe_pow, div_eq_mul_inv]
      rw [mul_comm])
  rw [hnormInv, havg, ← mul_assoc]
  congr 1
  have hq : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v))
  have hs : (Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have hsqr : (Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℂ) *
      (Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq.le
  rw [← hsqr, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

end
end DedekindZetaZeroFree.ExteriorGauss

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SArithmeticData

noncomputable section
set_option autoImplicit false

variable {F : Type} [Field F] [NumberField F]

abbrev exteriorLocalResidue (v : HeightOneSpectrum (𝓞 F)) :=
  IsLocalRing.ResidueField (v.adicCompletionIntegers F)

theorem exterior_sInteger_integral (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (x : A.R) :
    algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
  have hv : v ∉ A.Sf := by
    intro hv
    have hc : A.cS ≤ v.asIdeal := by
      change (∏ w ∈ A.Sf, w.asIdeal) ≤ v.asIdeal
      rw [← Ideal.dvd_iff_le]
      exact Finset.dvd_prod_of_mem (fun w => w.asIdeal) hv
    have ht : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rw [← I.property.2, hIv]
      exact sup_le le_rfl hc
    exact v.isPrime.ne_top (top_le_iff.mp ht)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v ((WithVal.toVal (v.valuation F) (x : F) : WithVal (v.valuation F)) : v.adicCompletion F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact Set.integer_valuation_le_one (A.Sf : Set (HeightOneSpectrum (𝓞 F))) F x
    (by simpa only [Finset.mem_coe] using hv)

def exteriorIntegerMap (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) : A.R →+* v.adicCompletionIntegers F where
  toFun x := ⟨algebraMap F (v.adicCompletion F) (x : F),
    A.exterior_sInteger_integral I v hIv x⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

 def integralResidueEquiv (v : HeightOneSpectrum (𝓞 F)) :
    (𝓞 F ⧸ v.asIdeal) ≃+* exteriorLocalResidue v :=
  (finitePlaceIdealResidueEquivCompletion v).trans
    (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))

private theorem integralResidueEquiv_apply_mk (A : SArithmeticData F) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) (x : 𝓞 F) :
    integralResidueEquiv v (Ideal.Quotient.mk v.asIdeal x) =
    IsLocalRing.residue (v.adicCompletionIntegers F)
      (A.exteriorIntegerMap I v hIv (algebraMap (𝓞 F) A.R x)) := by
  rw [integralResidueEquiv, RingEquiv.trans_apply, finitePlaceIdealResidueEquivCompletion_apply_mk,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  change finitePlaceCompletionRingEquiv v (algebraMap F _ (x : F)) =
    algebraMap F _ ((algebraMap (𝓞 F) A.R x : A.R) : F)
  simp only [finitePlaceCompletionRingEquiv_toCompletion]
  rfl
 def f (A : SArithmeticData F) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :=
  (IsLocalRing.residue (v.adicCompletionIntegers F)).comp (A.exteriorIntegerMap I v hIv)

private theorem f_surj (A : SArithmeticData F) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) : Function.Surjective (f A I v hIv) := by
  intro z
  obtain ⟨z', rfl⟩ := (integralResidueEquiv v).surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z'
  exact ⟨algebraMap (𝓞 F) A.R x, (integralResidueEquiv_apply_mk A I v hIv x).symm⟩

private theorem f_ker (A : SArithmeticData F) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
    RingHom.ker (f A I v hIv) = A.extendIdeal I := by
  have hn (a : 𝓞 F) : f A I v hIv (algebraMap (𝓞 F) A.R a) = 0 ↔ a ∈ v.asIdeal := by
    rw [show f A I v hIv (algebraMap (𝓞 F) A.R a) = integralResidueEquiv v (Ideal.Quotient.mk v.asIdeal a)
      from (integralResidueEquiv_apply_mk A I v hIv a).symm, map_eq_zero_iff _ (integralResidueEquiv v).injective,
      Ideal.Quotient.eq_zero_iff_mem]
  apply le_antisymm
  · intro x hx
    have hvx : v.valuation F (x : F) ≤ 1 := by
      have := A.exterior_sInteger_integral I v hIv x
      change Valued.v ((WithVal.toVal (v.valuation F) (x : F) : WithVal (v.valuation F)) : v.adicCompletion F) ≤ 1 at this
      rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) hvx
    have hndR : x * algebraMap (𝓞 F) A.R d = algebraMap (𝓞 F) A.R n := by
      apply Subtype.ext
      exact hnd
    have hnmem : n ∈ v.asIdeal := by
      apply (hn n).mp
      rw [← hndR, map_mul]
      change f A I v hIv x = 0 at hx
      rw [hx, zero_mul]
    obtain ⟨y, i, hi, hiy⟩ := (inferInstance : v.asIdeal.IsMaximal).exists_inv d.property
    have hsum : x = algebraMap (𝓞 F) A.R y * algebraMap (𝓞 F) A.R n +
        algebraMap (𝓞 F) A.R i * x := by
      rw [← hndR]
      have he := congrArg (algebraMap (𝓞 F) A.R) hiy
      simp only [map_add, map_mul, map_one] at he
      linear_combination -x * he
    rw [hsum]
    apply (A.extendIdeal I).add_mem
    · apply (A.extendIdeal I).mul_mem_left
      apply Ideal.mem_map_of_mem
      rwa [hIv]
    · apply (A.extendIdeal I).mul_mem_right
      apply Ideal.mem_map_of_mem
      rwa [hIv]
  · change Ideal.map (algebraMap (𝓞 F) A.R) I.val ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (hn a).mpr (hIv ▸ ha)

theorem existsUnique_exteriorLocalResidueEquiv (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
    ∃! e : (A.R ⧸ A.extendIdeal I) ≃+* exteriorLocalResidue v,
      ∀ x : A.R, e (Ideal.Quotient.mk (A.extendIdeal I) x) =
        IsLocalRing.residue (v.adicCompletionIntegers F)
          (A.exteriorIntegerMap I v hIv x) := by
  let e' := (Ideal.quotEquivOfEq (f_ker A I v hIv).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f_surj A I v hIv))
  have he' (x : A.R) : e' (Ideal.Quotient.mk (A.extendIdeal I) x) = f A I v hIv x := by
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  refine ⟨e', he', ?_⟩
  intro e'' he''
  apply RingEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (he'' x).trans (he' x).symm

def exteriorLocalResidueEquiv (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
    (A.R ⧸ A.extendIdeal I) ≃+* exteriorLocalResidue v :=
  Classical.choose (A.existsUnique_exteriorLocalResidueEquiv I v hIv)

theorem exteriorLocalResidueEquiv_apply (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (x : A.R) :
    A.exteriorLocalResidueEquiv I v hIv (Ideal.Quotient.mk (A.extendIdeal I) x) =
      IsLocalRing.residue (v.adicCompletionIntegers F)
        (A.exteriorIntegerMap I v hIv x) :=
  (Classical.choose_spec (A.existsUnique_exteriorLocalResidueEquiv I v hIv)).1 x

theorem exteriorLocalResidue_finite (v : HeightOneSpectrum (𝓞 F)) :
    Finite (exteriorLocalResidue v) :=
  Finite.of_equiv (𝓞 F ⧸ v.asIdeal) (integralResidueEquiv v).toEquiv

theorem exteriorLocalResidue_card (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (exteriorLocalResidue v) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (integralResidueEquiv v).toEquiv, Ideal.absNorm_apply]
  rfl

def exteriorTheta (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) : AddChar (exteriorLocalResidue v) Circle :=
  (A.residueTraceCharacter hS I p hp)⁻¹ |>.compAddMonoidHom
    (A.exteriorLocalResidueEquiv I v hIv).symm.toAddMonoidHom

theorem exteriorTheta_global_inverse (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) (x : A.R ⧸ A.extendIdeal I) :
    A.residueTraceCharacter hS I p hp x =
      (A.exteriorTheta hS I v hIv p hp (A.exteriorLocalResidueEquiv I v hIv x))⁻¹ := by
  simp [exteriorTheta, AddChar.compAddMonoidHom_apply, AddChar.map_neg_eq_inv]

private theorem local_div_integral (A : SArithmeticData F) (I : A.Exterior)
 (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
 (p : A.R) (hp : A.Generates I p) (a : Fˣ) (hap : (a : F) = (p : F))
 (d : v.adicCompletionIntegers F)
 (hd : IsLocalRing.residue (v.adicCompletionIntegers F) d = 0) :
 (d : v.adicCompletion F) / algebraMap F (v.adicCompletion F) (a : F) ∈
   v.adicCompletionIntegers F := by
 have hv : v ∉ A.Sf := by
   intro hv
   have hle : A.cS ≤ v.asIdeal :=
     (Ideal.prod_le_inf (s := A.Sf) (f := fun w => w.asIdeal)).trans (Finset.inf_le hv)
   exact v.isPrime.ne_top (by simpa only [hIv, sup_eq_left.mpr hle] using I.prop.2)
 have hval := SIntegerLocalization.generator_completion_valuation
   A.Sf I.val I.prop.1 p hp.1 hp.2 a hap v hv
 have he : idealPrimeExponent v.asIdeal I.val = 1 := by
   rw [hIv, idealPrimeExponent, UniqueFactorizationMonoid.normalizedFactors_irreducible v.prime.irreducible,
     normalize_eq]
   simp
 rw [he] at hval
 have hmem : d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
   Ideal.Quotient.eq_zero_iff_mem.mp hd
 have hnu : ¬ IsUnit d := (IsLocalRing.mem_maximalIdeal d).mp hmem
 have hlt : Valued.v (d : v.adicCompletion F) < 1 :=
   (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hnu
 rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hval]
 apply (div_le_one₀ (by simp)).mpr
 by_cases hz : Valued.v (d : v.adicCompletion F) = 0
 · rw [hz]; exact zero_le
 · rw [← WithZero.exp_log hz, WithZero.exp_le_exp]
   have hl : (Valued.v (d : v.adicCompletion F)).log < 0 := by
     rw [← WithZero.log_one, WithZero.log_lt_log hz one_ne_zero]
     exact hlt
   omega

theorem exteriorTheta_local_apply (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a)
    (x : v.adicCompletionIntegers F) :
    A.exteriorTheta hS I v hIv p hp
        (IsLocalRing.residue (v.adicCompletionIntegers F) x) =
      ResidueTrace.localTraceCharacter v
        ((x : v.adicCompletion F) / algebraMap F (v.adicCompletion F) (a : F)) := by
 obtain ⟨q, hq⟩ := (A.exteriorLocalResidueEquiv I v hIv).surjective
   (IsLocalRing.residue (v.adicCompletionIntegers F) x)
 obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
 have hr : IsLocalRing.residue (v.adicCompletionIntegers F)
     (A.exteriorIntegerMap I v hIv r) = IsLocalRing.residue (v.adicCompletionIntegers F) x := by
   rwa [A.exteriorLocalResidueEquiv_apply] at hq
 have hd : IsLocalRing.residue (v.adicCompletionIntegers F)
     (x - A.exteriorIntegerMap I v hIv r) = 0 := by rw [map_sub, hr, sub_self]
 have hint := local_div_integral A I v hIv p hp a hap _ hd
 have htr := (hzero _).mpr hint (1 : v.adicCompletionIntegers F)
 simp only [OneMemClass.coe_one, mul_one] at htr
 have hsame : ResidueTrace.localTraceCharacter v
     ((x : v.adicCompletion F) / algebraMap F (v.adicCompletion F) (a : F)) =
   ResidueTrace.localTraceCharacter v
     (algebraMap F (v.adicCompletion F) ((r : F) / (p : F))) := by
   change ResidueTrace.localTraceCharacter v
     (((x : v.adicCompletion F) - algebraMap F (v.adicCompletion F) (r : F)) /
       algebraMap F (v.adicCompletion F) (a : F)) = 1 at htr
   rw [sub_div, hap, ← map_div₀] at htr
   rw [AddChar.map_sub_eq_div] at htr
   rw [hap]
   exact div_eq_one.mp htr
 rw [← hq]
 have h := A.exteriorTheta_global_inverse hS I v hIv p hp
   (Ideal.Quotient.mk (A.extendIdeal I) r)
 rw [A.residueTraceCharacter_prime_local hS B I v hIv p hp a hap ha r,
   map_neg, AddChar.map_neg_eq_inv] at h
 exact (inv_injective h).symm.trans hsame.symm

theorem exteriorTheta_ne_one (A : SArithmeticData F)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    A.exteriorTheta hS I v hIv p hp ≠ 1 := by
  intro h
  apply A.residueTraceCharacter_prime_ne_one hS B I (hIv ▸ v.isPrime) p hp a hap ha
  apply AddChar.ext
  intro x
  rw [A.exteriorTheta_global_inverse hS I v hIv p hp x, h]
  simp

def exteriorLocalSexticChar (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
    MulChar (exteriorLocalResidue v) ℂ :=
  MulChar.ofUnitHom <|
    ((A.sexticResiduePowerChar σ I 1).toUnitHom).comp
      (Units.map (A.exteriorLocalResidueEquiv I v hIv).symm.toMonoidHom)

def exteriorThetaComplex (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) : AddChar (exteriorLocalResidue v) ℂ where
  toFun x := (A.exteriorTheta hS I v hIv p hp x : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    change ((A.exteriorTheta hS I v hIv p hp (x + y) : Circle) : ℂ) = _
    rw [AddChar.map_add_eq_mul]
    rfl

def exteriorQuadraticGauss (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) : ℂ :=
  letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
  letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
  (Real.sqrt (A.exteriorNorm I) : ℂ)⁻¹ *
    ∑ x : exteriorLocalResidue v, A.exteriorThetaComplex hS I v hIv p hp (x ^ 2)

private theorem local_order (A : SArithmeticData F) (σ : F →+* ℂ) (I : A.Exterior)
 (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
 orderOf (A.exteriorLocalSexticChar σ I v hIv) = 6 := by
 have hv : v ∉ A.Sf := by
   intro hv
   have hle : A.cS ≤ v.asIdeal :=
     (Ideal.prod_le_inf (s := A.Sf) (f := fun w => w.asIdeal)).trans (Finset.inf_le hv)
   exact v.isPrime.ne_top (by simpa only [hIv, sup_eq_left.mpr hle] using I.prop.2)
 have ho : orderOf (A.sexticResiduePowerChar σ I 1) = 6 := by
   letI : (A.extendIdeal I).IsMaximal := Ideal.Quotient.maximal_of_isField _
     ((A.exteriorLocalResidueEquiv I v hIv).toMulEquiv.isField (Field.toIsField _))
   letI := Ideal.Quotient.field (A.extendIdeal I)
   letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
   have hchi (u : (A.R ⧸ A.extendIdeal I)ˣ) :
       A.sexticResiduePowerChar σ I 1 u = σ (A.sexticResidueFamily I u : F) := by
     simp [ SArithmeticData.sexticResiduePowerChar, SArithmeticData.sexticExponent,
       MulChar.ofUnitHom_coe]
   have h6 : A.sexticResiduePowerChar σ I 1 ^ 6 = 1 := by
     apply MulChar.ext
     intro u
     rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hchi, ← map_pow]
     have h := congrArg Units.val (A.sexticResidueFamily_normalized.1 I u)
     exact (congrArg σ h).trans (map_one σ)
   have hd : 6 ∣ Nat.card (A.R ⧸ A.extendIdeal I) - 1 := by
     rw [A.exteriorResidue_card]
     have hm := A.exterior_norm_mod_twelve v hv
     rw [hIv]
     change 6 ∣ Ideal.absNorm v.asIdeal - 1
     omega
   obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
     (α := (A.R ⧸ A.extendIdeal I)ˣ)
   have hgc : orderOf g = Nat.card (A.R ⧸ A.extendIdeal I) - 1 := by
     rw [hg, Nat.card_units]
   have hk : orderOf (g ^ ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6)) = 6 := by
     rw [← hgc]
     apply orderOf_pow_orderOf_div
     · rw [hgc]
       have hn := Finite.one_lt_card (α := A.R ⧸ A.extendIdeal I)
       omega
     · rwa [hgc]
   have hdiv : 6 ∣ orderOf (A.sexticResiduePowerChar σ I 1) := by
     obtain ⟨j, hj, he, hr⟩ := A.sexticResidueFamily_normalized.2.1
       I v hIv g
     have hv : (A.sexticResidueFamily I g : F) ^
         orderOf (A.sexticResiduePowerChar σ I 1) = 1 := by
       apply σ.injective
       rw [map_pow, map_one, ← hchi, ← MulChar.pow_apply_coe]
       rw [pow_orderOf_eq_one, MulChar.one_apply_coe]
     rw [he] at hv
     have hz : (A.primitive_zeta12.toInteger ^ (2 * j)) ^
         orderOf (A.sexticResiduePowerChar σ I 1) = (1 : 𝓞 F) := by
       apply RingOfIntegers.ext
       change (((A.primitive_zeta12.toInteger : 𝓞 F) : F) ^ (2 * j)) ^
         orderOf (A.sexticResiduePowerChar σ I 1) = 1
       exact (congrArg (fun z : F => (z ^ (2 * j)) ^ orderOf (A.sexticResiduePowerChar σ I 1))
         A.primitive_zeta12.coe_toInteger).trans hv
     have hrpow := congrArg (fun z : A.R ⧸ A.extendIdeal I =>
         z ^ orderOf (A.sexticResiduePowerChar σ I 1)) hr
     rw [← map_pow, ← map_pow, hz, map_one, map_one] at hrpow
     have hp : (g ^ ((Nat.card (A.R ⧸ A.extendIdeal I) - 1) / 6)) ^
         orderOf (A.sexticResiduePowerChar σ I 1) = 1 := by
       apply Units.ext
       exact hrpow.symm
     rw [← hk]
     exact orderOf_dvd_of_pow_eq_one hp
   exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h6) hdiv
 let e := (Units.mapEquiv (A.exteriorLocalResidueEquiv I v hIv).symm.toMulEquiv).monoidHomCongrLeft (N := ℂˣ)
 have he : MulChar.mulEquivToUnitHom (A.exteriorLocalSexticChar σ I v hIv) =
   e.symm (MulChar.mulEquivToUnitHom (A.sexticResiduePowerChar σ I 1)) := by
   apply MonoidHom.ext
   intro u
   apply Units.ext
   change ((MulChar.equivToUnitHom (A.exteriorLocalSexticChar σ I v hIv) u : ℂˣ) : ℂ) = _
   rw [MulChar.coe_equivToUnitHom]
   change MulChar.ofUnitHom _ (u : exteriorLocalResidue v) = _
   rw [MulChar.ofUnitHom_coe]
   rfl
 rw [← MulChar.mulEquivToUnitHom.orderOf_eq, he, e.symm.orderOf_eq,
   MulChar.mulEquivToUnitHom.orderOf_eq]
 exact ho
section
variable {k : Type} [Field k] [Fintype k]
private lemma quad_unique (η θ : MulChar k ℂ) (hη : η ^ 2 = 1) (hθ : θ ^ 2 = 1)
    (hnη : η ≠ 1) (hnθ : θ ≠ 1) : η = θ := by
 obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
 have hv (ξ : MulChar k ℂ) (hs : ξ ^ 2 = 1) (hn : ξ ≠ 1) : ξ g = -1 := by
  have h1 : ξ g ≠ 1 := by
   intro h
   apply hn
   exact (MulChar.eq_iff hg ξ 1).mpr (by simpa using h)
  have h2 : ξ g ^ 2 = 1 := by rw [← MulChar.pow_apply_coe, hs, MulChar.one_apply_coe]
  exact (sq_eq_one_iff.mp h2).resolve_left h1
 exact (MulChar.eq_iff hg η θ).mpr ((hv η hη hnη).trans (hv θ hθ hnθ).symm)
private lemma char_ne_two (hQ : Fintype.card k % 12 = 1) : ringChar k ≠ 2 := by
 intro h
 have H := FiniteField.even_card_of_char_two h
 omega
private lemma square_count (χ : MulChar k ℂ) (hQ : Fintype.card k % 12 = 1) (hχ : orderOf χ = 6) (t : k) [DecidableEq k] :
 ((Finset.univ.filter fun x : k => x ^ 2 = t).card : ℂ) = (χ ^ 3) t + 1 := by
 classical
 have hs : (χ ^ 3) ^ 2 = 1 := by rw [← pow_mul]; norm_num; exact hχ ▸ pow_orderOf_eq_one χ
 let θ := (quadraticChar k).ringHomComp (Int.castRingHom ℂ)
 have hθ : θ ^ 2 = 1 := by
  dsimp [θ]
  rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic k).sq_eq_one, MulChar.ringHomComp_one]
 have hnθ : θ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (by intro a b h; change (a : ℂ) = b at h; exact_mod_cast h)).mpr (quadraticChar_ne_one (char_ne_two hQ))
 have he := quad_unique (χ ^ 3) θ hs hθ (pow_ne_one_of_lt_orderOf (by norm_num) (by omega)) hnθ
 rw [he]
 have H := quadraticChar_card_sqrts (char_ne_two hQ) t
 have H' := congrArg (fun z : ℤ => (z : ℂ)) H
 simpa [θ, MulChar.ringHomComp_apply] using H'

end

theorem exteriorQuadraticGauss_eq_gaussSum (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
    letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
    A.exteriorQuadraticGauss hS I v hIv p hp =
      (Real.sqrt (A.exteriorNorm I) : ℂ)⁻¹ *
        gaussSum (A.exteriorLocalSexticChar σ I v hIv ^ 3)
          (A.exteriorThetaComplex hS I v hIv p hp) := by
 letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
 letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
 have hv : v ∉ A.Sf := by
   intro hv
   have hle : A.cS ≤ v.asIdeal :=
     (Ideal.prod_le_inf (s := A.Sf) (f := fun w => w.asIdeal)).trans (Finset.inf_le hv)
   exact v.isPrime.ne_top (by simpa only [hIv, sup_eq_left.mpr hle] using I.prop.2)
 have hQ : Fintype.card (exteriorLocalResidue v) % 12 = 1 := by
   rw [← Nat.card_eq_fintype_card, exteriorLocalResidue_card]
   exact A.exterior_norm_mod_twelve v hv
 let ψ := A.exteriorThetaComplex hS I v hIv p hp
 let χ := A.exteriorLocalSexticChar σ I v hIv
 have hnψ : ψ ≠ 1 := by
   intro h
   apply A.exteriorTheta_ne_one hS B I v hIv hzero p hp a hap ha
   apply AddChar.ext
   intro x
   apply Subtype.ext
   have hh := congrArg (fun z : AddChar (exteriorLocalResidue v) ℂ => z x) h
   exact hh
 have hsum := AddChar.sum_eq_zero_of_ne_one hnψ
 have H := Finset.sum_fiberwise (Finset.univ : Finset (exteriorLocalResidue v))
   (fun y : exteriorLocalResidue v => y ^ 2) (fun y => ψ (y ^ 2))
 have hf (t : exteriorLocalResidue v) :
   (∑ y ∈ Finset.univ.filter (fun y => y ^ 2 = t), ψ (y ^ 2)) = ((χ ^ 3) t + 1) * ψ t := by
   calc
     _ = ∑ y ∈ Finset.univ.filter (fun y => y ^ 2 = t), ψ t := by
       apply Finset.sum_congr rfl
       intro y hy
       rw [(Finset.mem_filter.mp hy).2]
     _ = _ := by
       rw [Finset.sum_const, nsmul_eq_mul]
       exact congrArg (fun z : ℂ => z * ψ t) (square_count χ hQ (local_order A σ I v hIv) t)
 unfold exteriorQuadraticGauss
 congr 1
 change (∑ y, ψ (y ^ 2)) = gaussSum (χ ^ 3) ψ
 rw [← H]
 simp only [hf, add_mul, one_mul, Finset.sum_add_distrib, hsum, add_zero, gaussSum]

private theorem exteriorLocalSexticChar_cube_neg_one (A : SArithmeticData F) (σ : F →+* ℂ) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal) :
    (A.exteriorLocalSexticChar σ I v hIv ^ 3) (-1) = 1 := by
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0)]
  have hc : A.exteriorLocalSexticChar σ I v hIv (-1) = 1 := by
    change A.exteriorLocalSexticChar σ I v hIv ((-1 : (exteriorLocalResidue v)ˣ) : exteriorLocalResidue v) = 1
    unfold exteriorLocalSexticChar
    rw [MulChar.ofUnitHom_coe]
    change ((A.sexticResiduePowerChar σ I 1).toUnitHom
      (Units.map (A.exteriorLocalResidueEquiv I v hIv).symm.toMonoidHom (-1)) : ℂ) = 1
    have hu : Units.map (A.exteriorLocalResidueEquiv I v hIv).symm.toMonoidHom (-1) = -1 := by
      apply Units.ext
      simp
    rw [hu, MulChar.toUnitHom_eq]
    change (MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I)) ^
      sexticExponent 1) (-1 : A.R ⧸ A.extendIdeal I) = 1
    have he : sexticExponent 1 = 1 := rfl
    rw [he, pow_one]
    change (MulChar.ofUnitHom ((Units.map σ.toMonoidHom).comp (A.sexticResidueFamily I)))
      ((-1 : (A.R ⧸ A.extendIdeal I)ˣ) : A.R ⧸ A.extendIdeal I) = 1
    rw [MulChar.ofUnitHom_coe]
    have hn := congrArg σ (A.sexticResidue_neg_one I)
    unfold sexticResidue residueValue at hn
    have hq : Ideal.Quotient.mk (A.extendIdeal I) (-1 : A.R) =
      ((-1 : (A.R ⧸ A.extendIdeal I)ˣ) : A.R ⧸ A.extendIdeal I) := by
      simp only [map_neg, map_one, Units.val_neg, Units.val_one]
    rw [hq, MulChar.ofUnitHom_coe, map_one] at hn
    exact hn
  rw [hc, one_pow]

theorem exterior_gaussSum_theta_eq_inverse (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (I : A.Exterior)
    (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (p : A.R) (hp : A.Generates I p) :
    letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
    letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
    gaussSum (A.exteriorLocalSexticChar σ I v hIv ^ 3)
        (A.exteriorThetaComplex hS I v hIv p hp) =
      gaussSum (A.exteriorLocalSexticChar σ I v hIv ^ 3)
        (A.exteriorThetaComplex hS I v hIv p hp)⁻¹ := by
  letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
  letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
  have h := mul_gaussSum_inv_eq_gaussSum
    (A.exteriorLocalSexticChar σ I v hIv ^ 3)
    (A.exteriorThetaComplex hS I v hIv p hp)
  rw [exteriorLocalSexticChar_cube_neg_one A σ I v hIv, one_mul] at h
  exact h.symm

private theorem transported_power (A : SArithmeticData F) (σ : F →+* ℂ)
 (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
 (x : A.R ⧸ A.extendIdeal I) :
 (A.exteriorLocalSexticChar σ I v hIv ^ 3) (A.exteriorLocalResidueEquiv I v hIv x) =
 A.sexticResiduePowerChar σ I 3 x := by
 have hc : A.exteriorLocalSexticChar σ I v hIv (A.exteriorLocalResidueEquiv I v hIv x) =
     A.sexticResiduePowerChar σ I 1 x := by
   by_cases hx : IsUnit x
   · obtain ⟨u, rfl⟩ := hx
     change A.exteriorLocalSexticChar σ I v hIv
       ((Units.map (A.exteriorLocalResidueEquiv I v hIv).toMonoidHom u :
         (exteriorLocalResidue v)ˣ) : exteriorLocalResidue v) = _
     rw [exteriorLocalSexticChar, MulChar.ofUnitHom_coe]
     change ((A.sexticResiduePowerChar σ I 1).toUnitHom
       (Units.map (A.exteriorLocalResidueEquiv I v hIv).symm.toMonoidHom
         (Units.map (A.exteriorLocalResidueEquiv I v hIv).toMonoidHom u)) : ℂ) = _
     have hu : Units.map (A.exteriorLocalResidueEquiv I v hIv).symm.toMonoidHom
       (Units.map (A.exteriorLocalResidueEquiv I v hIv).toMonoidHom u) = u := by
       apply Units.ext
       exact (A.exteriorLocalResidueEquiv I v hIv).symm_apply_apply _
     rw [hu, MulChar.toUnitHom_eq]
     exact MulChar.coe_equivToUnitHom _ _
   · have hnu : ¬ IsUnit (A.exteriorLocalResidueEquiv I v hIv x) := by
       intro hu
       apply hx
       have h := hu.map (A.exteriorLocalResidueEquiv I v hIv).symm.toRingHom
       change IsUnit ((A.exteriorLocalResidueEquiv I v hIv).symm
         (A.exteriorLocalResidueEquiv I v hIv x)) at h
       rwa [RingEquiv.symm_apply_apply] at h
     rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hnu]
 rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), hc]
 have hp : (A.sexticResiduePowerChar σ I 1) ^ 3 = A.sexticResiduePowerChar σ I 3 := by
   simp only [sexticResiduePowerChar]
   have h1 : sexticExponent 1 = 1 := rfl
   have h3 : sexticExponent 3 = 3 := rfl
   rw [h1, h3, pow_one]
 rw [← hp, MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0)]

theorem exteriorQuadraticGauss_eq_idealGauss_three (A : SArithmeticData F)
    (σ : F →+* ℂ) (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    A.exteriorQuadraticGauss hS I v hIv p hp = A.idealGauss σ hS I p hp 3 := by
 letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
 letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
 letI : Finite (A.R ⧸ A.extendIdeal I) := A.exteriorResidue_finite I
 letI : Fintype (A.R ⧸ A.extendIdeal I) := Fintype.ofFinite _
 rw [A.exteriorQuadraticGauss_eq_gaussSum σ hS B I v hIv hgood hzero p hp a hap ha,
   A.exterior_gaussSum_theta_eq_inverse σ hS I v hIv hgood p hp]
 unfold idealGauss gaussSum
 congr 1
 rw [← (A.exteriorLocalResidueEquiv I v hIv).toEquiv.sum_comp]
 apply Finset.sum_congr rfl
 intro x hx
 change (A.exteriorLocalSexticChar σ I v hIv ^ 3) (A.exteriorLocalResidueEquiv I v hIv x) *
   (A.exteriorThetaComplex hS I v hIv p hp)⁻¹ (A.exteriorLocalResidueEquiv I v hIv x) = _
 rw [transported_power]
 congr 1
 rw [AddChar.inv_apply]
 change ((A.exteriorTheta hS I v hIv p hp
   (-(A.exteriorLocalResidueEquiv I v hIv x)) : Circle) : ℂ) = _
 rw [AddChar.map_neg_eq_inv, ← A.exteriorTheta_global_inverse]

def exteriorQuadraticCutoff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Set (v.adicCompletion F) :=
  {x | ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ n}

def exteriorRawQuadraticCutoff (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ) (n : ℕ) : ℂ :=
  (Real.sqrt ‖(2 : v.adicCompletion F) * (a : v.adicCompletion F)‖ : ℂ) *
    ∫ x in exteriorQuadraticCutoff v n,
      (ResidueTrace.localTraceCharacter v ((a : v.adicCompletion F) * x ^ 2) : ℂ) ∂μ

theorem exteriorRawQuadraticCutoff_unit_eventually (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (u : (v.adicCompletionIntegers F)ˣ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      exteriorRawQuadraticCutoff v μ
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) n = 1 := by
  exact ExteriorGauss.unit_cutoff_eventually v hgood hzero μ hμ u

theorem exterior_raw_quadratic_ratio_unit_eventually (A : SArithmeticData F)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1)
    (u : (v.adicCompletionIntegers F)ˣ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      exteriorRawQuadraticCutoff v μ
          (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) n /
        exteriorRawQuadraticCutoff v μ 1 n = 1 := by
  have hu := A.exteriorRawQuadraticCutoff_unit_eventually I v hIv hgood hzero μ hμ u
  have h1 := A.exteriorRawQuadraticCutoff_unit_eventually I v hIv hgood hzero μ hμ 1
  filter_upwards [hu, h1] with n hn h1n
  simpa only [map_one] using (show exteriorRawQuadraticCutoff v μ
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) n /
    exteriorRawQuadraticCutoff v μ
      (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom 1) n = 1 by
        rw [hn, h1n, div_self one_ne_zero])

theorem exteriorRawQuadraticCutoff_inv_generator_eventually
    (A : SArithmeticData F) (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      exteriorRawQuadraticCutoff v μ
        ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⁻¹) n =
          A.exteriorQuadraticGauss hS I v hIv p hp := by
  have hv : v ∉ A.Sf := by
    intro hv
    have hle : A.cS ≤ v.asIdeal :=
      (Ideal.prod_le_inf (s := A.Sf) (f := fun w => w.asIdeal)).trans (Finset.inf_le hv)
    exact v.isPrime.ne_top (by simpa only [hIv, sup_eq_left.mpr hle] using I.prop.2)
  have hval := SIntegerLocalization.generator_completion_valuation
    A.Sf I.val I.prop.1 p hp.1 hp.2 a hap v hv
  have he : idealPrimeExponent v.asIdeal I.val = 1 := by
    rw [hIv, idealPrimeExponent,
      UniqueFactorizationMonoid.normalizedFactors_irreducible v.prime.irreducible,
      normalize_eq]
    simp
  rw [he] at hval
  let aLocal : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  have haLocal : Valued.v (aLocal : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hval
  letI : Finite (exteriorLocalResidue v) := exteriorLocalResidue_finite v
  letI : Fintype (exteriorLocalResidue v) := Fintype.ofFinite _
  have hfinite := ExteriorGauss.integer_quadratic_integral_eq_residue_sum
    v hgood μ hμ aLocal haLocal (A.exteriorTheta hS I v hIv p hp)
    (A.exteriorTheta_local_apply hS B I v hIv hzero p hp a hap ha)
  filter_upwards [ExteriorGauss.inverse_uniformizer_cutoff_eventually
    v hgood hzero μ hμ aLocal haLocal] with n hn
  change ExteriorGauss.rawCutoff v μ aLocal⁻¹ n = _
  rw [hn, hfinite]
  change (Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℂ)⁻¹ *
    (∑ x : exteriorLocalResidue v, (A.exteriorTheta hS I v hIv p hp (x ^ 2) : ℂ)) = _
  have hnorm : A.exteriorNorm I = (Ideal.absNorm v.asIdeal : ℝ) := by
    change (Ideal.absNorm I.val : ℝ) = _
    rw [hIv]
  simp only [exteriorQuadraticGauss, hnorm, exteriorThetaComplex]
  rfl

theorem exterior_raw_quadratic_integral_eq_gamma_three
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      exteriorRawQuadraticCutoff v μ
        ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⁻¹) n =
          A.idealGauss σ hS I p hp 3 := by
  filter_upwards [A.exteriorRawQuadraticCutoff_inv_generator_eventually
      hS B I v hIv hgood hzero p hp a hap ha μ hμ] with n hn
  exact hn.trans (A.exteriorQuadraticGauss_eq_idealGauss_three
    σ hS B I v hIv hgood hzero p hp a hap ha)

theorem exterior_raw_quadratic_ratio_eq_gamma_three
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (hgood : ¬ (ResidueTrace.rationalPrimeBelow v).val ∣ 6)
    (hzero : ResidueTrace.IsSelfDual v) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a)
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : MeasureTheory.Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      exteriorRawQuadraticCutoff v μ
          ((Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⁻¹) n /
        exteriorRawQuadraticCutoff v μ 1 n = A.idealGauss σ hS I p hp 3 := by
  have h1 := A.exteriorRawQuadraticCutoff_unit_eventually I v hIv hgood hzero μ hμ 1
  filter_upwards [A.exterior_raw_quadratic_integral_eq_gamma_three
    σ hS B I v hIv hgood hzero p hp a hap ha μ hμ, h1] with n hn h1n
  simp only [map_one] at h1n
  rw [hn, h1n, div_one]

end
end DedekindZetaZeroFree.SArithmeticData

end
