module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailGeometricSum
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompactCoreLaurentIntegral

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

private lemma eval₂_id_eq_smeval (f : LaurentPolynomial ℂ) (u : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) u f = f.smeval u := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, LaurentPolynomial.smeval_add, hp, hq]
  | C_mul_T n a =>
      rw [LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.smeval_C_mul_T_n, smul_eq_mul,
        RingHom.id_apply]

private lemma smeval_eq_finsupp_sum (f : LaurentPolynomial ℂ) (u : ℂˣ) :
    f.smeval u = f.coeff.sum (fun n c => (u : ℂ) ^ n * c) := by
  rw [LaurentPolynomial.smeval_eq_sum]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_eq_mul, Units.val_zpow_eq_zpow_val, mul_comm]

theorem actual_scalar_numerator_coordinate (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∀ (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
      ∃ p : ℤ →₀ ℂ, ∀ s : ℂ, convergenceHalfPlane ε s →
        denominator (LocalField F q) ε s *
          standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
            (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
            (k : ActualCover F ζ hζ q) h =
          p.sum (fun n c => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * c) := by
  intro φ k h
  obtain ⟨M, hM⟩ := actual_tail_geometric_sum F ζ hζ q S P J hJ μ hμ π hπ ε
  obtain ⟨M₂, hM₂⟩ := actual_tail_absolute_convergence F ζ hζ q S P J hJ μ hμ π hπ ε
  set B : Set (LocalField F q) :=
    {x | KPCubicHaar.abs (LocalField F q) x ≤
      (residueCardinality (LocalField F q) : ℝ) ^ ((M : ℤ) - 1)} with hBdef
  set T : Set (LocalField F q) :=
    ⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ) with hTdef
  set B₂ : Set (LocalField F q) :=
    {x | KPCubicHaar.abs (LocalField F q) x ≤
      (residueCardinality (LocalField F q) : ℝ) ^ ((M₂ : ℤ) - 1)} with hB₂def
  set T₂ : Set (LocalField F q) :=
    ⋃ n : ℕ, actualShell F q ((M₂ + n : ℕ) : ℤ) with hT₂def
  obtain ⟨hBc, hBm, hshellc, hdisj, hunion⟩ := actual_shell_compact_partition F q M
  have hshellc' : ∀ m : ℤ, IsCompact (actualShell F q m) ∧ MeasurableSet (actualShell F q m) :=
    hshellc
  have hTm : MeasurableSet T := by
    rw [hTdef]; exact MeasurableSet.iUnion fun n => (hshellc' _).2
  obtain ⟨hB₂c, hB₂m, hshellc₂, hdisj₂, hunion₂⟩ := actual_shell_compact_partition F q M₂

  obtain ⟨p_core, hp_core⟩ := actual_initial_cutoff_laurent F ζ hζ q S P μ ε
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : ActualCover F ζ hζ q) h B hBc hBm
  have hshell : ∀ i : Fin 3, ∃ p : ℤ →₀ ℂ, ∀ s : ℂ,
      (∫ x in actualShell F q ((M + i.val : ℕ) : ℤ),
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
      p.sum (fun n c => (evaluationUnit (LocalField F q) ε s : ℂ) ^ n * c) := by
    intro i
    exact actual_initial_cutoff_laurent F ζ hζ q S P μ ε
      (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
      (k : ActualCover F ζ hζ q) h (actualShell F q ((M + i.val : ℕ) : ℤ))
      (hshellc' _).1 (hshellc' _).2
  choose p_i hp_i using hshell
  let cc : ℂ := if ε = Sign.plus then (residueCardinality (LocalField F q) : ℂ)⁻¹
    else (residueCardinality (LocalField F q) : ℂ)
  let Pcore : LaurentPolynomial ℂ := AddMonoidAlgebra.ofCoeff p_core
  let Pi : Fin 3 → LaurentPolynomial ℂ := fun i => AddMonoidAlgebra.ofCoeff (p_i i)
  let Ppoly : LaurentPolynomial ℂ :=
    (1 - LaurentPolynomial.C cc * LaurentPolynomial.T 6) * Pcore + ∑ i : Fin 3, Pi i
  refine ⟨Ppoly.coeff, ?_⟩
  intro s hs
  let u : ℂˣ := evaluationUnit (LocalField F q) ε s
  have hden : denominator (LocalField F q) ε s = 1 - cc * (u : ℂ) ^ 6 := by
    cases ε with
    | plus =>
        simp only [denominator, if_true, cc, u, evaluationUnit, rUnit, t, r, if_true]
        rw [Units.val_mk0]
    | minus =>
        simp only [denominator, reduceCtorEq, if_false, cc, u, evaluationUnit, rUnit, r,
          if_false, if_true, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow]
  have hstd : standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
        (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
        (k : ActualCover F ζ hζ q) h =
      ∫ x in (Set.univ : Set (LocalField F q)),
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ := by
    rw [MeasureTheory.setIntegral_univ]
    rfl
  have hIntB : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) B μ :=
    standardIntegral_integrableOn_compact (LocalField F q) S.borel P S.iwasawa μ ε s
      (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
      (k : ActualCover F ζ hζ q) h B hBc hBm
  have hIntB₂ : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) B₂ μ :=
    standardIntegral_integrableOn_compact (LocalField F q) S.borel P S.iwasawa μ ε s
      (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
      (k : ActualCover F ζ hζ q) h B₂ hB₂c hB₂m
  have hIntT₂ : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) T₂ μ :=
    hM₂ s hs φ k h
  have hIntU : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h)
      (B₂ ∪ T₂) μ := hIntB₂.union hIntT₂
  have hunion₂' : B₂ ∪ T₂ = Set.univ := by rw [hB₂def, hT₂def]; exact hunion₂
  rw [hunion₂'] at hIntU
  have hIntT : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h) T μ :=
    hIntU.mono_set (Set.subset_univ T)
  have hsplit : (∫ x in (Set.univ : Set (LocalField F q)),
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
      (∫ x in B, actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) +
      (∫ x in T, actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) := by
    rw [← hunion]
    exact setIntegral_union hdisj hTm hIntB hIntT
  have hpc : (∫ x in B, actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
      p_core.sum (fun n c => (u : ℂ) ^ n * c) := by
    simpa only [actualStandardIntegrand, u] using hp_core s
  have hgeom' : denominator (LocalField F q) ε s *
        (∫ x in T, actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
      ∑ i : Fin 3, (p_i i).sum (fun n c => (u : ℂ) ^ n * c) := by
    rw [hM s hs φ k h]
    exact Finset.sum_congr rfl fun i _ => hp_i i s
  have hLHS : denominator (LocalField F q) ε s *
        standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
          (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
          (k : ActualCover F ζ hζ q) h =
      (1 - cc * (u : ℂ) ^ 6) * p_core.sum (fun n c => (u : ℂ) ^ n * c) +
        ∑ i : Fin 3, (p_i i).sum (fun n c => (u : ℂ) ^ n * c) := by
    rw [hstd, hsplit, mul_add, hgeom', hden, hpc]
  have hPeval : Ppoly.smeval u =
      (1 - cc * (u : ℂ) ^ 6) * p_core.sum (fun n c => (u : ℂ) ^ n * c) +
        ∑ i : Fin 3, (p_i i).sum (fun n c => (u : ℂ) ^ n * c) := by
    rw [show Ppoly.smeval u = LaurentPolynomial.eval₂ (RingHom.id ℂ) u Ppoly from
      (eval₂_id_eq_smeval Ppoly u).symm]
    have hC : LaurentPolynomial.eval₂ (RingHom.id ℂ) u
        (1 - LaurentPolynomial.C cc * LaurentPolynomial.T 6) = 1 - cc * (u : ℂ) ^ 6 := by
      rw [map_sub, map_one, LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply]
      simp
    have hcore : LaurentPolynomial.eval₂ (RingHom.id ℂ) u Pcore =
        p_core.sum (fun n c => (u : ℂ) ^ n * c) := by
      rw [eval₂_id_eq_smeval]
      exact smeval_eq_finsupp_sum Pcore u
    have hsum : LaurentPolynomial.eval₂ (RingHom.id ℂ) u (∑ i : Fin 3, Pi i) =
        ∑ i : Fin 3, (p_i i).sum (fun n c => (u : ℂ) ^ n * c) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [show Pi i = AddMonoidAlgebra.ofCoeff (p_i i) from rfl, eval₂_id_eq_smeval]
        exact smeval_eq_finsupp_sum (AddMonoidAlgebra.ofCoeff (p_i i)) u
    simp only [Ppoly, map_add, map_mul]
    rw [hC, hcore, hsum]
  rw [← smeval_eq_finsupp_sum Ppoly u]
  rw [hPeval]
  exact hLHS

end DedekindZetaZeroFree.KPRankOneShellRepair

end
