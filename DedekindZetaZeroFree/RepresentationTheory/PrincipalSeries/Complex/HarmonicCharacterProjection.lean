module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.SU2HaarCharacterAverages
public import DedekindZetaZeroFree.HarmonicAnalysis.SphericalHarmonics.FischerSpanning

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues MeasureTheory

private lemma entry_continuous (i j : Fin 2) :
    Continuous (fun k : ComplexSU2 => (k : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private lemma compactSphereCoordinate_continuous :
    Continuous (compactSphereCoordinate : ComplexSU2 → Fin 3 → ℂ) := by
  rw [continuous_pi_iff]
  intro i
  have h : Continuous (fun k : ComplexSU2 =>
      (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1)) :=
    (entry_continuous 1 0).mul (entry_continuous 1 1).star
  fin_cases i
  · simp only [compactSphereCoordinate, Matrix.cons_val_zero]
    exact RCLike.continuous_ofReal.comp ((Complex.continuous_re.comp h).const_mul 2)
  · simp only [compactSphereCoordinate, Matrix.cons_val_one, Matrix.head_cons]
    exact RCLike.continuous_ofReal.comp ((Complex.continuous_im.comp h).const_mul 2)
  · simp only [compactSphereCoordinate, Matrix.cons_val_two, Matrix.tail_cons]
    exact RCLike.continuous_ofReal.comp
      (((entry_continuous 1 0).norm.pow 2).sub ((entry_continuous 1 1).norm.pow 2))

private lemma polynomialCompactRestriction_continuous (q : MvPolynomial (Fin 3) ℂ) :
    Continuous (polynomialCompactRestriction q) := by
  simp only [polynomialCompactRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  exact (MvPolynomial.continuous_eval q).comp compactSphereCoordinate_continuous

private lemma su2HarmonicCharacter_continuous' (ℓ : ℕ) :
    Continuous (su2HarmonicCharacter ℓ) := by
  have htrace : ∀ n : ℕ, Continuous (fun k : ComplexSU2 =>
      KPCompactHarmonic.symmetricPowerTrace n
        ⟨(k : Matrix (Fin 2) (Fin 2) ℂ),
          (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1⟩) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simpa [KPCompactHarmonic.symmetricPowerTrace] using
        (continuous_const : Continuous (fun _ : ComplexSU2 => (1 : ℂ)))
    | one => simp only [KPCompactHarmonic.symmetricPowerTrace]; fun_prop
    | more n hn hn1 =>
        simp only [KPCompactHarmonic.symmetricPowerTrace]
        exact ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.trace (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn1).sub
          ((by fun_prop : Continuous (fun k : ComplexSU2 =>
            Matrix.det (k : Matrix (Fin 2) (Fin 2) ℂ))).mul hn)
  unfold su2HarmonicCharacter KPCompactHarmonic.rankOneCharacter
  simp only [(Matrix.mem_specialUnitaryGroup_iff.mp (Subtype.prop _)).2, one_pow, div_one]
  exact htrace (2 * ℓ)

theorem polynomial_character_integrand_integrable (μ : Measure ComplexSU2)
    (hfinite : IsFiniteMeasure μ) (ℓ : ℕ) (q : MvPolynomial (Fin 3) ℂ)
    (k : ComplexSU2) :
    Integrable (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
      polynomialCompactRestriction q (k * t)) μ := by
  letI : IsFiniteMeasure μ := hfinite
  letI : CompactSpace ComplexSU2 := isCompact_iff_compactSpace.mp (by
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm)
  have hcont : Continuous (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
      polynomialCompactRestriction q (k * t)) :=
    ((su2HarmonicCharacter_continuous' ℓ).star).mul
      ((polynomialCompactRestriction_continuous q).comp (by fun_prop))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues MeasureTheory
open _root_.ContRepresentation
open DedekindZetaZeroFree.TauCeti DedekindZetaZeroFree.TauCeti.ContRepresentation

private theorem sym_trace (n : ℕ) (g : ComplexSU2) :
    KPCompactHarmonic.symmetricPowerTrace n
      ⟨g.val, (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1⟩ =
        (TauCeti.SU2.symPower n).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  induction n using Nat.twoStepInduction with
  | zero => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_zero]
  | one => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_one_eq_trace]
  | more n h0 h1 =>
    rw [KPCompactHarmonic.symmetricPowerTrace, h0, h1]
    change Matrix.trace g.val * _ - Matrix.det g.val * _ = _
    rw [hd, one_mul]
    have h := TauCeti.SU2.trace_mul_character_symPower n g
    linear_combination h
private theorem char_eq (n : ℕ) (g : ComplexSU2) :
    su2HarmonicCharacter n g = (TauCeti.SU2.symPower (2*n)).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  unfold su2HarmonicCharacter KPCompactHarmonic.rankOneCharacter
  rw [sym_trace]
  rw [hd, one_pow, div_one]

theorem harmonic_character_projection_diagonal (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ harmonicPolynomials ℓ)
    (k : ComplexSU2) :
    (((2 * ℓ + 1 : ℕ) : ℂ) *
      ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
        polynomialCompactRestriction p (k * t) ∂μ) =
      polynomialCompactRestriction p k := by
  letI := hhaar
  letI := hprob
  rw [TauCeti.eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure ComplexSU2 μ]
  letI := HarmonicVendor.harmonicNormedAddCommGroup ℓ
  letI := HarmonicVendor.harmonicNormedSpace ℓ
  letI : TopologicalSpace (HarmonicVendor.Harmonic ℓ) :=
    (HarmonicVendor.harmonicNormedAddCommGroup ℓ).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let π := HarmonicVendor.harmonicContRepresentation ℓ
  have hπ : Continuous π := HarmonicVendor.harmonicContRepresentation_continuous ℓ
  let e := (Classical.choice (HarmonicVendor.harmonic_equiv_symPower ℓ)).symm
  have hirr : π.toRepresentation.IsIrreducible :=
    Representation.isIrreducible_of_linearEquiv e.toLinearEquiv
      (fun g v => congrArg (fun T => T v) (e.toIntertwiningMap.isIntertwining' g))
      (TauCeti.SU2.isIrreducible_symPower (2*ℓ))
  have hc (g : ComplexSU2) : π.character hπ g = su2HarmonicCharacter ℓ g := by
    rw [char_eq]
    exact HarmonicVendor.harmonic_character ℓ g
  let f : C(ComplexSU2, ℂ) := star (π.character hπ)
  have hf : ∀ g h : ComplexSU2, f (h*g*h⁻¹) = f g := by
    intro g h
    change star (π.character hπ (h*g*h⁻¹)) = star (π.character hπ g)
    rw [ContRepresentation.character_conj]
  have hi : (∫ g : ComplexSU2, f g * π.character hπ g ∂TauCeti.haarProb ComplexSU2) = 1 := by
    have heq : (fun g : ComplexSU2 => f g * π.character hπ g) =
        (fun g : ComplexSU2 => (TauCeti.SU2.symPower (2*ℓ)).character g *
          (starRingEnd ℂ) ((TauCeti.SU2.symPower (2*ℓ)).character g)) := by
      funext g
      change star (π.character hπ g) * π.character hπ g = _
      rw [hc, char_eq]
      exact mul_comm _ _
    rw [heq]
    have h := TauCeti.SU2.integral_character_symPower_mul_conj (2*ℓ) (2*ℓ)
    simp only [ite_true] at h
    exact h
  have hd : Module.finrank ℂ (HarmonicVendor.Harmonic ℓ) = 2*ℓ+1 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact TauCeti.SU2.finrank_symPower (2*ℓ)
  have hop := TauCeti.ContRepresentation.integratedOperator_eq_smul_id π hπ hf hirr
  rw [hi, hd, mul_one] at hop
  let v : HarmonicVendor.Harmonic ℓ := ⟨p, hp⟩
  let E : HarmonicVendor.Harmonic ℓ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.proj k).comp (polynomialCompactRestriction.comp (harmonicPolynomials ℓ).subtype))
  have hint : Integrable (fun g : ComplexSU2 => f g • π g v) (TauCeti.haarProb ComplexSU2) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact f.continuous.smul ((hπ.clm_apply continuous_const))
    · exact HasCompactSupport.of_compactSpace _
  have he := congrArg (fun T : HarmonicVendor.Harmonic ℓ →L[ℂ] HarmonicVendor.Harmonic ℓ => E (T v)) hop
  rw [TauCeti.ContRepresentation.integratedOperator_apply,
    ← E.integral_comp_comm hint] at he
  have hE (g : ComplexSU2) : E (f g • π g v) =
      star (su2HarmonicCharacter ℓ g) * polynomialCompactRestriction p (k*g) := by
    rw [map_smul]
    change f g * polynomialCompactRestriction (HarmonicVendor.harmonicRepresentation ℓ g v) k = _
    have hr := HarmonicVendor.harmonicRepresentation_restriction ℓ g k v
    change polynomialCompactRestriction (HarmonicVendor.harmonicRepresentation ℓ g v) k =
      polynomialCompactRestriction p (k*g) at hr
    rw [hr]
    congr 1
    exact congrArg star (hc g)
  simp_rw [hE] at he
  have he' : (∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
      polynomialCompactRestriction p (k*t) ∂TauCeti.haarProb ComplexSU2) =
      ((2*ℓ+1 : ℕ) : ℂ)⁻¹ * polynomialCompactRestriction p k := by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul,
      smul_eq_mul] at he
    change _ = ((2*ℓ+1 : ℕ) : ℂ)⁻¹ * polynomialCompactRestriction p k at he
    exact he
  rw [he', ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (by omega : 2*ℓ+1 ≠ 0)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues MeasureTheory
open scoped BigOperators

private theorem recurrence_character (d : ℕ) (g : ComplexSU2) :
    KPCompactHarmonic.symmetricPowerTrace d
      ⟨g.val, (Matrix.mem_specialUnitaryGroup_iff.mp g.property).1⟩ =
    (TauCeti.SU2.symPower d).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  induction d using Nat.twoStepInduction with
  | zero => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_zero]
  | one => simp [KPCompactHarmonic.symmetricPowerTrace, TauCeti.SU2.character_symPower_one_eq_trace]
  | more d h0 h1 =>
    simp only [KPCompactHarmonic.symmetricPowerTrace, h0, h1, hd, one_mul]
    have h := TauCeti.SU2.trace_mul_character_symPower d g
    linear_combination h
private theorem actual_character (ℓ : ℕ) (g : ComplexSU2) :
    su2HarmonicCharacter ℓ g = (TauCeti.SU2.symPower (2 * ℓ)).character g := by
  have hd : Matrix.det g.val = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.property).2
  simp only [su2HarmonicCharacter, KPCompactHarmonic.rankOneCharacter, hd, one_pow,
    div_one, recurrence_character]

theorem harmonic_character_projection_off_diagonal (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ n : ℕ) (hne : n ≠ ℓ) (p : MvPolynomial (Fin 3) ℂ)
    (hp : p ∈ harmonicPolynomials n) (k : ComplexSU2) :
    (∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
      polynomialCompactRestriction p (k * t) ∂μ) = 0 := by
  letI : μ.IsHaarMeasure := hhaar
  letI : IsProbabilityMeasure μ := hprob
  rw [TauCeti.eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure ComplexSU2 μ]
  letI : TopologicalSpace (HarmonicVendor.Harmonic n) :=
    (HarmonicVendor.harmonicNormedAddCommGroup n).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let π := HarmonicVendor.harmonicContRepresentation n
  have hπ : Continuous π := HarmonicVendor.harmonicContRepresentation_continuous n
  let f : C(ComplexSU2, ℂ) := star (TauCeti.SU2.symPowerCharacter (2 * ℓ))
  have hf (g h : ComplexSU2) : f (h * g * h⁻¹) = f g := by
    simp only [f, ContinuousMap.star_apply, TauCeti.SU2.symPowerCharacter_apply]
    rw [Representation.char_conj]
  have hchar (g : ComplexSU2) : π.character hπ g =
      (TauCeti.SU2.symPower (2 * n)).character g := by
    change (HarmonicVendor.harmonicRepresentation n).character g = _
    exact HarmonicVendor.harmonic_character n g
  obtain ⟨e⟩ := HarmonicVendor.harmonic_equiv_symPower n
  have hirr : π.toRepresentation.IsIrreducible := by
    apply Representation.isIrreducible_of_linearEquiv e.symm.toLinearEquiv
      (fun g v => ?_) (TauCeti.SU2.isIrreducible_symPower (2 * n))
    exact congrArg (fun L => L v) (e.symm.isIntertwining' g)
  have hz : (∫ g, f g * π.character hπ g ∂TauCeti.haarProb ComplexSU2) = 0 := by
    simp only [f, ContinuousMap.star_apply, TauCeti.SU2.symPowerCharacter_apply, hchar]
    simp_rw [mul_comm (star _) ((TauCeti.SU2.symPower (2 * n)).character _)]
    simpa only [starRingEnd_apply, if_neg (show 2 * n ≠ 2 * ℓ by omega)] using
      TauCeti.SU2.integral_character_symPower_mul_conj (2 * n) (2 * ℓ)
  have hzero := TauCeti.ContRepresentation.integratedOperator_eq_zero π hπ hf hirr hz
  let v : HarmonicVendor.Harmonic n := ⟨p, hp⟩
  let ev : HarmonicVendor.Harmonic n →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.proj k).comp (KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction.comp
      (KPCplxHarmonicIntertwinerSpectrum.harmonicPolynomials n).subtype))
  have hint : Integrable (fun g => f g • π g v) (TauCeti.haarProb ComplexSU2) := by
    exact (f.continuous.smul (hπ.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh := ev.integral_comp_comm hint
  rw [← TauCeti.ContRepresentation.integratedOperator_apply π hπ f v, hzero,
    ContinuousLinearMap.zero_apply, map_zero] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [map_smul]
  change star (su2HarmonicCharacter ℓ t) * polynomialCompactRestriction p (k * t) =
    f t * KPCplxHarmonicIntertwinerSpectrum.polynomialCompactRestriction
      (HarmonicVendor.harmonicRepresentation n t v) k
  rw [HarmonicVendor.harmonicRepresentation_restriction]
  simp only [actual_character, f, ContinuousMap.star_apply, TauCeti.SU2.symPowerCharacter_apply]
  rfl

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end

section

namespace DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

open KPCplxCharacterHaar KPCplxIntertwinerEigenvalues MeasureTheory

theorem compactSphereCoordinate_is_real_unit (k : ComplexSU2) :
    compactSphereCoordinate k = (fun i : Fin 3 => (((compactSphereCoordinate k i).re : ℝ) : ℂ)) ∧
      (∑ i : Fin 3, ((compactSphereCoordinate k i).re) ^ 2) = 1 := by
  constructor
  · funext i
    fin_cases i <;> dsimp [compactSphereCoordinate] <;> rw [Complex.ofReal_re]
  · have hrow := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℂ => (B 1 1).re)
      (Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
      Matrix.one_apply_eq] at hrow
    change (((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 0)) +
      ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * (starRingEnd ℂ) ((k : Matrix (Fin 2) (Fin 2) ℂ) 1 1))).re = 1 at hrow
    simp only [Complex.mul_conj', Complex.add_re, ← Complex.ofReal_pow,
      Complex.ofReal_re] at hrow
    let a := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 0
    let b := (k : Matrix (Fin 2) (Fin 2) ℂ) 1 1
    have hab : (a * star b).re ^ 2 + (a * star b).im ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
      simp only [pow_two, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq, norm_mul,
        norm_star]
      ring
    simp only [Fin.sum_univ_three, compactSphereCoordinate, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.ofReal_re]
    change (2 * (a * star b).re) ^ 2 + (2 * (a * star b).im) ^ 2 +
      (‖a‖ ^ 2 - ‖b‖ ^ 2) ^ 2 = 1
    change ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 at hrow
    nlinarith [sq_nonneg (‖a‖ ^ 2 + ‖b‖ ^ 2 - 1)]

theorem harmonic_character_projection (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (I : Finset ℕ) (h : ℕ → MvPolynomial (Fin 3) ℂ)
    (hh : ∀ ℓ' ∈ I, h ℓ' ∈ harmonicPolynomials ℓ') (k : ComplexSU2) :
    (((2 * ℓ + 1 : ℕ) : ℂ) *
        ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
          (∑ ℓ' ∈ I, polynomialCompactRestriction (h ℓ') (k * t)) ∂μ)
      = if ℓ ∈ I then polynomialCompactRestriction (h ℓ) k else 0 := by
  classical
  letI : IsProbabilityMeasure μ := hprob
  rw [show (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
      (∑ n ∈ I, polynomialCompactRestriction (h n) (k * t))) =
    (fun t : ComplexSU2 => ∑ n ∈ I, star (su2HarmonicCharacter ℓ t) *
      polynomialCompactRestriction (h n) (k * t)) from
    funext fun t => Finset.mul_sum _ _ _]
  rw [integral_finsetSum I (fun n _ =>
    polynomial_character_integrand_integrable μ inferInstance ℓ (h n) k),
    Finset.mul_sum]
  have hterm (n : ℕ) (hn : n ∈ I) :
      (((2 * ℓ + 1 : ℕ) : ℂ) *
        ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
          polynomialCompactRestriction (h n) (k * t) ∂μ) =
        if n = ℓ then polynomialCompactRestriction (h ℓ) k else 0 := by
    by_cases heq : n = ℓ
    · subst n
      simpa using harmonic_character_projection_diagonal μ hhaar hprob ℓ (h ℓ) (hh ℓ hn) k
    · rw [harmonic_character_projection_off_diagonal μ hhaar hprob ℓ n heq
        (h n) (hh n hn) k]
      simp [heq]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem polynomial_character_convolution_realization_zero (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (q : MvPolynomial (Fin 3) ℂ) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p ∈ harmonicPolynomials 0 ∧
      ∀ k : ComplexSU2, polynomialCompactRestriction p k =
        ((2 * 0 + 1 : ℕ) : ℂ) *
          ∫ t : ComplexSU2, star (su2HarmonicCharacter 0 t) *
            polynomialCompactRestriction q (k * t) ∂μ := by
  letI : μ.IsHaarMeasure := hhaar
  refine ⟨MvPolynomial.C (∫ t : ComplexSU2, polynomialCompactRestriction q t ∂μ), ?_, ?_⟩
  · constructor
    · exact MvPolynomial.isHomogeneous_C (σ := Fin 3) _
    · simp [LinearMap.mem_ker, polynomialLaplacian, LinearMap.sum_apply,
        LinearMap.comp_apply]
  · intro k
    simp only [su2HarmonicCharacter, KPCompactHarmonic.rankOneCharacter,
      KPCompactHarmonic.symmetricPowerTrace, mul_zero, pow_zero, div_one, star_one,
      one_mul, Nat.cast_one, zero_add, polynomialCompactRestriction,
      LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.eval_C]
    exact (integral_mul_left_eq_self
      (fun t => MvPolynomial.eval (compactSphereCoordinate t) q) k).symm

theorem polynomial_character_convolution_realization_of_projection
    (μ : Measure ComplexSU2) (ℓ : ℕ) (q : MvPolynomial (Fin 3) ℂ)
    (hprojection : ∀ (I : Finset ℕ) (h : ℕ → MvPolynomial (Fin 3) ℂ),
      (∀ ℓ' ∈ I, h ℓ' ∈ harmonicPolynomials ℓ') → ∀ k : ComplexSU2,
        (((2 * ℓ + 1 : ℕ) : ℂ) *
          ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
            (∑ ℓ' ∈ I, polynomialCompactRestriction (h ℓ') (k * t)) ∂μ) =
          if ℓ ∈ I then polynomialCompactRestriction (h ℓ) k else 0) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p ∈ harmonicPolynomials ℓ ∧
      ∀ k : ComplexSU2,
        polynomialCompactRestriction p k =
          ((2 * ℓ + 1 : ℕ) : ℂ) *
            ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
              polynomialCompactRestriction q (k * t) ∂μ := by
  classical
  obtain ⟨I, h, hh, hspan⟩ :=
    ComplexFractionalInverse.FiniteFischerRaw.unit_radius_spanning q
  refine ⟨if hℓ : ℓ ∈ I then h ℓ else 0, ?_, ?_⟩
  · split
    · exact hh ℓ ‹ℓ ∈ I›
    · exact Submodule.zero_mem _
  · intro k
    have hcoord := compactSphereCoordinate_is_real_unit k
    have hreal (t : ComplexSU2) :
        polynomialCompactRestriction q (k * t) =
          ∑ ℓ' ∈ I, polynomialCompactRestriction (h ℓ') (k * t) := by
      have hu := (compactSphereCoordinate_is_real_unit (k * t)).2
      have hq := hspan (fun i => ((compactSphereCoordinate (k * t) i).re : ℝ)) hu
      have he : (fun i => (((compactSphereCoordinate (k * t) i).re : ℝ) : ℂ)) =
          compactSphereCoordinate (k * t) :=
        ((compactSphereCoordinate_is_real_unit (k * t)).1).symm
      rw [he] at hq
      simpa only [polynomialCompactRestriction, LinearMap.coe_mk, AddHom.coe_mk] using hq
    rw [show (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
          polynomialCompactRestriction q (k * t)) =
        (fun t : ComplexSU2 => star (su2HarmonicCharacter ℓ t) *
          (∑ ℓ' ∈ I, polynomialCompactRestriction (h ℓ') (k * t))) from
      funext fun t => by rw [hreal t]]
    rw [hprojection I h hh k]
    split
    · rfl
    · simp

theorem polynomial_character_convolution_realization (μ : Measure ComplexSU2)
    (hhaar : μ.IsHaarMeasure) (hprob : IsProbabilityMeasure μ)
    (ℓ : ℕ) (q : MvPolynomial (Fin 3) ℂ) :
    ∃ p : MvPolynomial (Fin 3) ℂ, p ∈ harmonicPolynomials ℓ ∧
      ∀ k : ComplexSU2,
        polynomialCompactRestriction p k =
          ((2 * ℓ + 1 : ℕ) : ℂ) *
            ∫ t : ComplexSU2, star (su2HarmonicCharacter ℓ t) *
              polynomialCompactRestriction q (k * t) ∂μ := by
  by_cases hzero : ℓ = 0
  · subst ℓ
    exact polynomial_character_convolution_realization_zero μ hhaar q
  · exact polynomial_character_convolution_realization_of_projection μ ℓ q
      (harmonic_character_projection μ hhaar hprob ℓ)

end DedekindZetaZeroFree.KPCplxHarmonicExtraction.CompactPolynomial

end
