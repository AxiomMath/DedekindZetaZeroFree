module

public import DedekindZetaZeroFree.Metaplectic.Weil.NormalizedLocalIndicesAndProductFormula
public import DedekindZetaZeroFree.Metaplectic.Weil.IsotropicComplementSignCharacter
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.Reciprocity

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection.CorrectedWeilSource
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

private lemma outside_prime_good (A : SArithmeticData F) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ A.Sf) : ¬ (ResidueTrace.rationalPrimeBelow w).val ∣ 6 := by
  intro hd
  apply hw
  apply A.above_six
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have hz := (CharP.cast_eq_zero_iff (𝓞 F ⧸ w.asIdeal)
    (ringChar (𝓞 F ⧸ w.asIdeal)) 6).mpr hd
  simpa only [map_ofNat, Nat.cast_ofNat] using hz
private lemma outside_prime_ideal (A : SArithmeticData F) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ A.Sf) : ∃ J : A.Exterior, J.val = w.asIdeal := by
  refine ⟨⟨w.asIdeal, w.ne_bot, ?_⟩, rfl⟩
  apply (A.exterior_iff ⟨w.asIdeal, w.ne_bot⟩).mpr
  intro v hv
  apply w.isMaximal.coprime_of_ne v.isMaximal
  intro he
  exact hw (HeightOneSpectrum.asIdeal_injective he ▸ hv)
private lemma outside_unit_index (A : SArithmeticData F) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ A.Sf) (hS : A.ContainsTraceBadPlaces)
    (b : (w.adicCompletion F)ˣ) (hb : Valued.v (b : w.adicCompletion F) = 1) :
    A.finiteWeilIndex w b = 1 := by
  obtain ⟨J,hJ⟩ := outside_prime_ideal A w hw
  have hmem := (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr hb
  let u : (w.adicCompletionIntegers F)ˣ :=
    ⟨⟨b, hmem.1⟩, ⟨(b⁻¹ : (w.adicCompletion F)ˣ), hmem.2⟩,
      Subtype.ext b.val_inv, Subtype.ext b.inv_val⟩
  have hu : Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom u = b := by
    apply Units.ext
    rfl
  rw [← hu]
  exact A.finiteWeilIndex_exterior_unit J w hJ (outside_prime_good A w hw) (hS w hw) u

theorem weilSCorrection_diagonal_prime (A : SArithmeticData F)
    (σ : F →+* ℂ) (hS : A.ContainsTraceBadPlaces) (B : Subgroup A.V)
    (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F)) (hIv : I.val = v.asIdeal)
    (p : A.R) (hp : A.Generates I p) (a : Fˣ)
    (hap : (a : F) = (p : F)) (ha : A.IsAllowed B a) :
    A.weilSCorrection A.complexWeilPhase (fun w => A.finiteWeilPhase w.val)
      (A.diagonal a) = A.idealGauss σ hS I p hp 3 := by
  have hvS : v ∉ A.Sf := ArithmeticContext.actual_exterior_prime_outside A I v hIv
  let f : HeightOneSpectrum (𝓞 F) → Circle := fun w =>
    A.finiteWeilIndex w (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom a⁻¹)
  have hout (w : HeightOneSpectrum (𝓞 F)) (hwS : w ∉ A.Sf) (hwv : w ≠ v) : f w = 1 := by
    have hnot : ¬ I.val ≤ w.asIdeal := by
      rw [hIv]
      intro hle
      exact hwv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
    have hval := ArithmeticContext.actual_generator_valuation_unit A I p a hp hap w hwS hnot
    apply outside_unit_index A w hwS hS
    change Valued.v (algebraMap F (w.adicCompletion F) ((a⁻¹ : Fˣ) : F)) = 1
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simp only [Units.val_inv_eq_inv_val, map_inv₀, RingHom.id_apply, hval, inv_one]
  have hsupp : Function.mulSupport f ⊆ (insert v A.Sf : Finset _) := by
    intro w hw
    by_contra hnot
    have hnot' : w ≠ v ∧ w ∉ A.Sf := by
      simpa only [Finset.mem_coe, Finset.mem_insert, not_or] using hnot
    exact hw (hout w hnot'.2 hnot'.1)
  have hglob := A.normalizedWeilIndex_product a⁻¹
  have hinf (w : InfinitePlace F) : A.infiniteWeilIndex w
      (Units.map (algebraMap F w.Completion).toMonoidHom a⁻¹) = 1 := by
    apply Circle.ext
    exact A.complexWeilPhase_eq_one w _
  simp only [hinf, Finset.prod_const_one, one_mul] at hglob
  change (∏ᶠ w, f w) = 1 at hglob
  rw [finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_insert hvS] at hglob
  have hcorr : (∏ w ∈ A.Sf, f w)⁻¹ = f v := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [mul_comm] using hglob
  have heval := A.finiteWeilIndex_exterior_inv_generator σ hS B I v hIv
    (outside_prime_good A v hvS) (hS v hvS) p hp a hap ha
  have hc : A.weilSCorrection A.complexWeilPhase (fun w => A.finiteWeilPhase w.val)
      (A.diagonal a) = ((∏ w ∈ A.Sf, f w)⁻¹ : Circle) := by
    change ((∏ w : InfinitePlace F, A.complexWeilPhase w
      ((Units.map (algebraMap F w.Completion).toMonoidHom a)⁻¹)) *
      ∏ w : A.Sf, A.finiteWeilPhase w.val
        ((Units.map (algebraMap F (w.val.adicCompletion F)).toMonoidHom a)⁻¹))⁻¹ = _
    simp only [A.complexWeilPhase_eq_one, Finset.prod_const_one, one_mul]
    rw [Circle.coe_inv]
    change _ = (Circle.coeHom (∏ w ∈ A.Sf, f w))⁻¹
    rw [map_prod, ← Finset.prod_coe_sort A.Sf (fun w => Circle.coeHom (f w))]
    simp only [f, map_inv]
    rfl
  rw [hc, hcorr]
  change (A.finiteWeilIndex v
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a⁻¹) : ℂ) = _
  rw [map_inv]
  exact heval.1.trans heval.2

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection.CorrectedWeilSource
