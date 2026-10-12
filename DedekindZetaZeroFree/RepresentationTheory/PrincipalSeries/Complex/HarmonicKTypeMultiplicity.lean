module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.HarmonicHighestWeightCyclicity

@[expose] public section

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

noncomputable def compactDiagonalTorus : Set compactSubgroup :=
  {k | ∃ a d : ℂˣ, ‖(a : ℂ)‖ = 1 ∧ ‖(d : ℂ)‖ = 1 ∧
    Matrix.ProjGenLinGroup.mk (upperTriangular a d 0) = (k : ComplexPGL2)}

theorem compactDiagonalTorus_identity_invariant (s : ℝ)
    (k : compactSubgroup) (hk : k ∈ compactDiagonalTorus)
    (f : PrincipalSeries s) : (pi s k f) 1 = f 1 := by
  obtain ⟨a, d, ha, hd, hk⟩ := hk
  rw [← hk, pi_mk]
  show f (1 * upperTriangular a d 0) = f 1
  rw [one_mul]
  have hcov := f.2.1 a d 0 1
  rw [mul_one] at hcov
  have hw : inductionWeight s a d = 1 := by
    unfold inductionWeight complexAbs
    rw [norm_div, ha, hd]
    norm_num
  rw [hcov, hw]
  norm_num

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

noncomputable def harmonicIdentityEvaluation (s : ℝ) (ℓ : ℕ) :
    harmonicKType s ℓ →ₗ[ℂ] ℂ where
  toFun u := (u : PrincipalSeries s) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem harmonicIdentityEvaluation_nonzero (s : ℝ) (ℓ : ℕ) :
    harmonicIdentityEvaluation s ℓ ≠ 0 := by
  intro hzero

  have hvan : ∀ f : PrincipalSeries s, f ∈ harmonicKType s ℓ → f = 0 := by
    intro f hf
    apply compactRestriction_injective s
    funext h
    change f (complexSU2Embedding h) = 0
    let k : compactSubgroup :=
      ⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding h), ⟨h, rfl⟩⟩
    have hmem : pi s (k : ComplexPGL2) f ∈ harmonicKType s ℓ :=
      (harmonicKType_structure s ℓ).1 k f hf
    have h1 : (pi s (k : ComplexPGL2) f) 1 = 0 := by
      have hc := DFunLike.congr_fun hzero
        (⟨pi s (k : ComplexPGL2) f, hmem⟩ : harmonicKType s ℓ)
      simpa [harmonicIdentityEvaluation] using hc
    have heq : (pi s (k : ComplexPGL2) f) 1 = f (complexSU2Embedding h) := by
      change (pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding h)) f) 1 =
        f (complexSU2Embedding h)
      rw [pi_mk]
      change f (1 * complexSU2Embedding h) = f (complexSU2Embedding h)
      rw [one_mul]
    rw [← heq]
    exact h1
  have hbot : harmonicKType s ℓ = ⊥ := (Submodule.eq_bot_iff (harmonicKType s ℓ)).mpr hvan
  have hfr := (harmonicKType_structure s ℓ).2.1
  rw [hbot, finrank_bot] at hfr
  omega

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

noncomputable def torusInvariantHarmonicDual (s : ℝ) (ℓ : ℕ) :
    Submodule ℂ (harmonicKType s ℓ →ₗ[ℂ] ℂ) where
  carrier := {L | ∀ k ∈ compactDiagonalTorus, ∀ u v : harmonicKType s ℓ,
    (v : PrincipalSeries s) = pi s k u → L v = L u}
  zero_mem' := by
    intro k hk u v hv
    rfl
  add_mem' := by
    intro L M hL hM k hk u v hv
    simp only [LinearMap.add_apply, hL k hk u v hv, hM k hk u v hv]
  smul_mem' := by
    intro c L hL k hk u v hv
    simp only [LinearMap.smul_apply, hL k hk u v hv]

theorem harmonicIdentityEvaluation_mem_torusInvariant (s : ℝ) (ℓ : ℕ) :
    harmonicIdentityEvaluation s ℓ ∈ torusInvariantHarmonicDual s ℓ := by
  intro k hk u v hv
  change (v : PrincipalSeries s) 1 = (u : PrincipalSeries s) 1
  rw [hv]
  exact compactDiagonalTorus_identity_invariant s k hk u

theorem torusInvariantHarmonicDual_finrank_pos (s : ℝ) (ℓ : ℕ) :
    0 < Module.finrank ℂ (torusInvariantHarmonicDual s ℓ) := by
  letI := harmonicKType_finite s ℓ
  letI := Module.Free.of_divisionRing ℂ (harmonicKType s ℓ)
  letI := Module.Finite.linearMap ℂ ℂ (harmonicKType s ℓ) ℂ
  let E : torusInvariantHarmonicDual s ℓ :=
    ⟨harmonicIdentityEvaluation s ℓ, harmonicIdentityEvaluation_mem_torusInvariant s ℓ⟩
  have hE : E ≠ 0 := by
    intro h
    exact harmonicIdentityEvaluation_nonzero s ℓ (congrArg Subtype.val h)
  letI : Nontrivial (torusInvariantHarmonicDual s ℓ) :=
    ⟨⟨E, 0, hE⟩⟩
  exact Module.finrank_pos

private theorem torus_lift_mem (z : Circle) :
    (⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding (TauCeti.SU2.torusHom z)),
      ⟨TauCeti.SU2.torusHom z, rfl⟩⟩ : compactSubgroup) ∈ compactDiagonalTorus := by
  refine ⟨Circle.toUnits z, (Circle.toUnits z)⁻¹, ?_, ?_, ?_⟩
  · simpa using Circle.norm_coe z
  · simp [Units.val_inv_eq_inv_val, norm_inv, Circle.norm_coe]
  · congr 1
    apply Units.ext
    ext i j
    change (!![(Circle.toUnits z : ℂ), 0; 0, ((Circle.toUnits z)⁻¹ : ℂˣ)] :
      Matrix (Fin 2) (Fin 2) ℂ) i j =
      (TauCeti.SU2.torusHom z : Matrix (Fin 2) (Fin 2) ℂ) i j
    fin_cases i <;> fin_cases j <;>
      simp [TauCeti.SU2.coe_torusHom,
        TauCeti.SU2.torusMatrix_apply_zero_zero, TauCeti.SU2.torusMatrix_apply_zero_one,
        TauCeti.SU2.torusMatrix_apply_one_zero, TauCeti.SU2.torusMatrix_apply_one_one,
        Units.val_inv_eq_inv_val]

private theorem generic_powers_injective :
    Function.Injective fun m : ℤ => (Circle.exp 1 : ℂ) ^ m := by
  intro m n hmn
  have h : (Circle.exp 1 ^ m : Circle) = Circle.exp 1 ^ n :=
    Subtype.ext (by simpa only [Circle.coe_zpow] using hmn)
  rw [← Circle.exp_intCast_mul, ← Circle.exp_intCast_mul, mul_one, mul_one] at h
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 h
  rcases eq_or_ne k 0 with rfl | hk0
  · have hmn' : (m : ℝ) = (n : ℝ) := by simpa using hk
    exact_mod_cast hmn'
  · refine absurd ?_ ((irrational_pi.intCast_mul (m := 2 * k) (by omega)).ne_int (m - n))
    push_cast
    linear_combination -hk

theorem torusInvariantHarmonicDual_finrank (s : ℝ) (ℓ : ℕ) :
    Module.finrank ℂ (torusInvariantHarmonicDual s ℓ) = 1 := by
  classical
  letI := harmonicKType_finite s ℓ
  letI := harmonicPolynomials_finiteDimensional ℓ
  letI := polynomialCompactHarmonics_finiteDimensional ℓ
  obtain ⟨e⟩ := HarmonicVendor.harmonic_equiv_symPower ℓ
  let q : harmonicPolynomials ℓ →ₗ[ℂ]
      (harmonicPolynomials ℓ).map polynomialCompactRestriction :=
    (polynomialCompactRestriction.domRestrict (harmonicPolynomials ℓ)).codRestrict _
      (fun p => Submodule.mem_map.mpr ⟨p, p.property, rfl⟩)
  have hqs : Function.Surjective q := by
    intro v
    obtain ⟨p, hp, he⟩ := Submodule.mem_map.mp v.property
    exact ⟨⟨p, hp⟩, Subtype.ext he⟩
  have hdim : Module.finrank ℂ (harmonicPolynomials ℓ) =
      Module.finrank ℂ ((harmonicPolynomials ℓ).map polynomialCompactRestriction) := by
    rw [polynomialCompactHarmonics_finrank]
    exact e.toLinearEquiv.finrank_eq.trans (TauCeti.SU2.finrank_symPower (2 * ℓ))
  let qe := LinearEquiv.ofBijective q
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hqs, hqs⟩
  let r := harmonicKTypeRestrictionEquiv s ℓ (polynomialCompactHarmonics_extend s ℓ)
  let t : harmonicPolynomials ℓ ≃ₗ[ℂ] harmonicKType s ℓ := qe.trans r.symm
  have ht (p : harmonicPolynomials ℓ) :
      compactRestriction s (t p) = polynomialCompactRestriction p := by
    have hh := r.apply_symm_apply (qe p)
    exact congrArg Subtype.val hh
  let b := (TauCeti.SU2.weightBasis (2 * ℓ)).map (e.toLinearEquiv.symm.trans t)
  have hb (z : Circle) (i : Fin (2 * ℓ + 1)) :
      pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding (TauCeti.SU2.torusHom z))) (b i) =
        ((z : ℂ) ^ TauCeti.SU2.weight (2 * ℓ) i) • (b i : PrincipalSeries s) := by
    let p := e.toLinearEquiv.symm (TauCeti.SU2.weightBasis (2 * ℓ) i)
    have hp : HarmonicVendor.harmonicRepresentation ℓ (TauCeti.SU2.torusHom z) p =
        ((z : ℂ) ^ TauCeti.SU2.weight (2 * ℓ) i) • p := by
      apply e.toLinearEquiv.injective
      have hh := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (TauCeti.SU2.torusHom z) p
      change e.toLinearEquiv ((HarmonicVendor.harmonicRepresentation ℓ (TauCeti.SU2.torusHom z)) p) =
        TauCeti.SU2.symPower (2 * ℓ) (TauCeti.SU2.torusHom z) (e.toLinearEquiv p) at hh
      have hep : e.toLinearEquiv p = TauCeti.SU2.weightBasis (2 * ℓ) i :=
        e.toLinearEquiv.apply_symm_apply _
      rw [hep, TauCeti.SU2.symPower_torusHom_weightBasis] at hh
      simpa only [map_smul, hep] using hh
    have hbi : b i = t p := by rfl
    rw [hbi]
    apply compactRestriction_injective s
    ext k
    rw [compactRestriction_pi_su2]
    change compactRestriction s (t p) (k * TauCeti.SU2.torusHom z) = _
    rw [ht]
    rw [← HarmonicVendor.harmonicRepresentation_restriction ℓ (TauCeti.SU2.torusHom z) k p, hp]
    change polynomialCompactRestriction (((z : ℂ) ^ TauCeti.SU2.weight (2 * ℓ) i) • (p : MvPolynomial (Fin 3) ℂ)) k = _
    rw [map_smul]
    change _ = ((z : ℂ) ^ TauCeti.SU2.weight (2 * ℓ) i) * compactRestriction s (t p) k
    rw [ht]
    rfl
  let i₀ : Fin (2 * ℓ + 1) := ⟨ℓ, by omega⟩
  have vanish (L : torusInvariantHarmonicDual s ℓ) (i : Fin (2 * ℓ + 1))
      (hi : i ≠ i₀) : L.val (b i) = 0 := by
    let z := Circle.exp 1
    let c : ℂ := (z : ℂ) ^ TauCeti.SU2.weight (2 * ℓ) i
    have hw : TauCeti.SU2.weight (2 * ℓ) i ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      dsimp [TauCeti.SU2.weight] at h
      dsimp [i₀]
      omega
    have hc : c ≠ 1 := by
      intro h
      apply hw
      apply generic_powers_injective
      simpa [c, z] using h
    have hh := L.property
      (⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding (TauCeti.SU2.torusHom z)),
        ⟨TauCeti.SU2.torusHom z, rfl⟩⟩ : compactSubgroup)
      (torus_lift_mem z) (b i) (c • b i) (hb z i).symm
    rw [map_smul, smul_eq_mul] at hh
    have hh' : (c - 1) * L.val (b i) = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hh').resolve_left (sub_ne_zero.mpr hc)
  let ev : torusInvariantHarmonicDual s ℓ →ₗ[ℂ] ℂ :=
    { toFun L := L.val (b i₀)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hevinj : Function.Injective ev := by
    intro L M h
    apply Subtype.ext
    apply b.ext
    intro i
    by_cases hi : i = i₀
    · subst i
      exact h
    · rw [vanish L i hi, vanish M i hi]
  have hle := LinearMap.finrank_le_finrank_of_injective hevinj
  rw [Module.finrank_self] at hle
  have hpos := torusInvariantHarmonicDual_finrank_pos s ℓ
  omega

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end

section
namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

theorem harmonicKType_zero_fixed (s : ℝ) (f : PrincipalSeries s)
    (hf : f ∈ harmonicKType s 0) (k : compactSubgroup) : pi s k f = f := by
  obtain ⟨l, hl⟩ := k.property
  apply compactRestriction_injective s
  obtain ⟨p, hp, he⟩ := (harmonicKType_mem_iff s 0 f).mp hf
  have hc : p = MvPolynomial.C (p.coeff 0) := by
    rw [← MvPolynomial.homogeneousComponent_zero p]
    exact (MvPolynomial.homogeneousComponent_eq_self hp.1).symm
  ext h
  rw [← hl]
  change compactRestriction s (pi s (Matrix.ProjGenLinGroup.mk (complexSU2Embedding l)) f) h = _
  rw [compactRestriction_pi_su2]
  change f (complexSU2Embedding (h * l)) = f (complexSU2Embedding h)
  rw [he, he, hc]
  simp

theorem harmonicKType_zero_eq_span (s : ℝ) :
    harmonicKType s 0 = ℂ ∙ sphericalSection s := by
  apply le_antisymm
  · intro f hf
    rw [sphericalSection_spans_fixed s f (harmonicKType_zero_fixed s f hf)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · apply Submodule.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    have hdim := (harmonicKType_structure s 0).2.1
    have hn : harmonicKType s 0 ≠ ⊥ := by
      intro hn
      rw [hn, finrank_bot] at hdim
      norm_num at hdim
    obtain ⟨f, hf, hne⟩ := (harmonicKType s 0).ne_bot_iff.mp hn
    have he := sphericalSection_spans_fixed s f (harmonicKType_zero_fixed s f hf)
    have hc : f 1 ≠ 0 := by
      intro hc
      rw [hc, zero_smul] at he
      exact hne he
    have hh := (harmonicKType s 0).smul_mem (f 1)⁻¹ hf
    have hh' : (f 1)⁻¹ • ((f 1) • sphericalSection s) ∈ harmonicKType s 0 := by
      convert hh using 1
      congr 1
      exact he.symm
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hh'
    exact hh'

noncomputable def principalSeriesEvaluation (s : ℝ) (g : ComplexGL2) :
    PrincipalSeries s →ₗ[ℂ] ℂ where
  toFun f := f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem KEquivalent_symm (s : ℝ) (U V : Submodule ℂ (PrincipalSeries s))
    (hU : IsKInvariant s U) (he : KEquivalent s U V) : KEquivalent s V U := by
  obtain ⟨e, he⟩ := he
  refine ⟨e.symm, ?_⟩
  intro k u v hv
  let w : U := ⟨pi s k (e.symm u), hU k (e.symm u) (e.symm u).property⟩
  have hw := he k (e.symm u) w rfl
  have hwv : e w = v := by
    apply Subtype.ext
    simpa only [e.apply_symm_apply] using hw.trans (by simpa only [e.apply_symm_apply] using hv.symm)
  have hw' : w = e.symm v := by
    exact e.injective (hwv.trans (e.apply_symm_apply v).symm)
  exact (congrArg Subtype.val hw').symm

theorem compactEquivariantMap_eq_smul_of_evaluation (s : ℝ) (ℓ : ℕ)
    (r : harmonicKType s ℓ →ₗ[ℂ] PrincipalSeries s)
    (hr : ∀ (k : compactSubgroup) (u v : harmonicKType s ℓ),
      (v : PrincipalSeries s) = pi s k u → r v = pi s k (r u))
    (c : ℂ) (heval : ∀ u : harmonicKType s ℓ, (r u) 1 = c * (u : PrincipalSeries s) 1) :
    ∀ u : harmonicKType s ℓ, r u = c • (u : PrincipalSeries s) := by
  intro u
  apply compactRestriction_injective s
  ext k
  let k' : compactSubgroup :=
    ⟨Matrix.ProjGenLinGroup.mk (complexSU2Embedding k), ⟨k, rfl⟩⟩
  let v : harmonicKType s ℓ :=
    ⟨pi s k' u, (harmonicKType_structure s ℓ).1 k' u u.property⟩
  have hv := hr k' u v rfl
  have hc := heval v
  rw [hv] at hc
  change (r u) (complexSU2Embedding k) = c * (u : PrincipalSeries s) (complexSU2Embedding k)
  change (r u) (1 * complexSU2Embedding k) =
    c * (u : PrincipalSeries s) (1 * complexSU2Embedding k) at hc
  simpa only [one_mul] using hc

theorem harmonicKType_unique_copy_of_invariant_functionals (s : ℝ) (ℓ : ℕ)
    (T : Set compactSubgroup)
    (hT : ∀ k ∈ T, ∀ f : PrincipalSeries s, (pi s k f) 1 = f 1)
    (hfunctional : ∀ L : harmonicKType s ℓ →ₗ[ℂ] ℂ,
      (∀ k ∈ T, ∀ u v : harmonicKType s ℓ,
        (v : PrincipalSeries s) = pi s k u → L v = L u) →
      ∃ c : ℂ, ∀ u : harmonicKType s ℓ, L u = c * (u : PrincipalSeries s) 1)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (he : KEquivalent s U (harmonicKType s ℓ)) : U = harmonicKType s ℓ := by
  classical
  obtain ⟨e, he⟩ := KEquivalent_symm s U (harmonicKType s ℓ) hU he
  let r : harmonicKType s ℓ →ₗ[ℂ] PrincipalSeries s := U.subtype.comp e.toLinearMap
  have hr : ∀ (k : compactSubgroup) (u v : harmonicKType s ℓ),
      (v : PrincipalSeries s) = pi s k u → r v = pi s k (r u) := he
  let L : harmonicKType s ℓ →ₗ[ℂ] ℂ := (principalSeriesEvaluation s 1).comp r
  obtain ⟨c, hc⟩ := hfunctional L (by
    intro k hk u v hv
    change (r v) 1 = (r u) 1
    rw [hr k u v hv]
    exact hT k hk (r u))
  have hscalar := compactEquivariantMap_eq_smul_of_evaluation s ℓ r hr c hc
  have hle : U ≤ harmonicKType s ℓ := by
    intro f hf
    let u : harmonicKType s ℓ := e.symm ⟨f, hf⟩
    have hh := hscalar u
    have hru : r u = f := by
      change (e (e.symm ⟨f, hf⟩) : PrincipalSeries s) = f
      simp
    rw [hru] at hh
    rw [hh]
    exact (harmonicKType s ℓ).smul_mem c u.property
  letI := harmonicKType_finite s ℓ
  letI : Module.Finite ℂ U := Module.Finite.of_surjective e.toLinearMap e.surjective
  exact Submodule.eq_of_le_of_finrank_eq hle e.finrank_eq.symm

theorem harmonicKType_unique_copy (s : ℝ) (ℓ : ℕ)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (he : KEquivalent s U (harmonicKType s ℓ)) :
    U = harmonicKType s ℓ := by
  apply harmonicKType_unique_copy_of_invariant_functionals s ℓ compactDiagonalTorus
    (fun k hk f => compactDiagonalTorus_identity_invariant s k hk f) ?_ U hU he
  intro L hL
  let E : torusInvariantHarmonicDual s ℓ :=
    ⟨harmonicIdentityEvaluation s ℓ, by
      intro k hk u v hv
      change (v : PrincipalSeries s) 1 = (u : PrincipalSeries s) 1
      rw [hv]
      exact compactDiagonalTorus_identity_invariant s k hk u⟩
  have hE : E ≠ 0 := by
    intro h
    exact harmonicIdentityEvaluation_nonzero s ℓ (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    (torusInvariantHarmonicDual_finrank s ℓ) hE
    (⟨L, hL⟩ : torusInvariantHarmonicDual s ℓ)
  refine ⟨c, ?_⟩
  intro u
  have hu := congrArg (fun M : torusInvariantHarmonicDual s ℓ =>
    (M : harmonicKType s ℓ →ₗ[ℂ] ℂ) u) hc
  exact hu.symm

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum

end
