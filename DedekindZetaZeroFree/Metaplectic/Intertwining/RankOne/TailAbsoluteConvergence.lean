module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.AbsoluteShellMassRecurrence
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFields.CompactCoreShellPartition

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

private theorem summable_three (A : ℕ → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hA : ∀ n, 0 ≤ A n) (hrec : ∀ n, A (n + 3) = c * A n) : Summable A := by
  have hsub : ∀ i : Fin 3, Summable (fun n : ℕ => A (n * 3 + i.val)) := by
    intro i
    have he : ∀ n : ℕ, A (n * 3 + i.val) = c ^ n * A i.val := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hi : (n + 1) * 3 + i.val = (n * 3 + i.val) + 3 := by omega
        rw [hi, hrec, ih, pow_succ]
        ring
    simp_rw [he]
    exact (summable_geometric_of_lt_one hc0 hc1).mul_right _
  let e : ℕ ≃ Fin 3 × ℕ := (Nat.divModEquiv 3).trans (Equiv.prodComm ℕ (Fin 3))
  apply (e.symm.summable_iff).mp
  apply (summable_prod_of_nonneg (f := fun p : Fin 3 × ℕ => A (e.symm p))
    (fun p => hA _)).mpr
  constructor
  · intro i
    exact hsub i
  · exact summable_of_finite_support (Set.toFinite _)

theorem actual_tail_absolute_convergence (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∃ M : ℕ, ∀ (s : ℂ), convergenceHalfPlane ε s →
      ∀ (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
        (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
      IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h)
        (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)) μ := by
  obtain ⟨M, hM⟩ := actual_tail_shell_norm_step F ζ hζ q S P J hJ μ hμ π hπ ε
  refine ⟨M, ?_⟩
  intro s hs φ k h
  have hratio : ‖actualShellRatio F q ε s‖ < 1 := by
    have H := (convergence_iff_geometric (LocalField F q) ε s).mp hs
    cases ε with
    | plus => simpa [actualShellRatio] using H
    | minus => simpa [actualShellRatio, t, mul_inv_rev, inv_pow, mul_comm] using H
  have hc := (actual_shell_compact_partition F q M).2.2.1
  have hInt : ∀ n : ℕ, IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h)
      (actualShell F q ((M + n : ℕ) : ℤ)) μ := by
    intro n
    exact standardIntegral_integrableOn_compact (LocalField F q) S.borel P S.iwasawa μ ε s
      φ.val k h _ (hc _).1 (hc _).2
  apply integrableOn_iUnion_of_summable_integral_norm hInt
  let A : ℕ → ℝ := fun n => ∫ x in actualShell F q ((M + n : ℕ) : ℤ),
    ‖actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x‖ ∂μ
  change Summable A
  apply summable_three A ‖actualShellRatio F q ε s‖ (norm_nonneg _) hratio
  · intro n
    exact integral_nonneg (fun x => norm_nonneg _)
  · intro n
    have H := hM (M + n) (Nat.le_add_right M n) s φ k h
    have hi : ((M + (n + 3) : ℕ) : ℤ) = ((M + n : ℕ) : ℤ) + 3 := by
      push_cast
      ring
    dsimp only [A]
    rw [hi]
    exact H

end DedekindZetaZeroFree.KPRankOneShellRepair

end
