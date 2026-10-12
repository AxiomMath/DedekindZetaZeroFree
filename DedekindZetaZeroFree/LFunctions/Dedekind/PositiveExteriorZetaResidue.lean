module

public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

namespace DedekindZetaZeroFree.PositiveZetaResidue

noncomputable section
open scoped NumberField Topology
open Filter IsDedekindDomain

def exteriorEulerFactor (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ p ∈ S, (1 - (Ideal.absNorm p.asIdeal : ℂ) ^ (-s))

def exteriorResidue (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ :=
  NumberField.dedekindZeta_residue F *
    ∏ p ∈ S, (1 - (Ideal.absNorm p.asIdeal : ℝ)⁻¹)

def exteriorRegularization (F : Type) [Field F] [NumberField F]
    {η : RayClassCharacter F (⊤ : Ideal (𝓞 F))}
    (P : PrincipalRayHeckeData F ⊤ η)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  P.R s * exteriorEulerFactor F S s

theorem principal_continuation_eq_dedekindZeta
    (F : Type) [Field F] [NumberField F]
    (η : RayClassCharacter F (⊤ : Ideal (𝓞 F))) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F ⊤ η) (s : ℂ) (hs : 1 < s.re) :
    P.L s = NumberField.dedekindZeta F s := by
  have hsum := (P.series s hs).summable
  have hgroup := hsum.hasSum.tsum_fiberwise (fun I : Ideal (𝓞 F) => Ideal.absNorm I)
  have hfiber (n : ℕ) :
      (∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
        η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) =
      LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      have hz (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = 0}) :
          η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) = 0 := by
        have hI : I.val = ⊥ := Ideal.absNorm_eq_zero_iff.mp I.property
        rw [hI, (η.eq_zero_iff' ⊥).mpr (Or.inl rfl), zero_mul]
      simp [hz, LSeries.term]
    · have hterm (I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}) :
          η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := by
        have hI : I.val ≠ ⊥ := by
          intro h
          exact hn (by simpa [h] using I.property.symm)
        rw [hη I.val hI (by simp), one_mul, I.property]
      simp_rw [hterm]
      rw [tsum_const, nsmul_eq_mul, LSeries.term_of_ne_zero hn]
      simp [Complex.cpow_neg, div_eq_mul_inv]
  have heq : (fun n => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
      η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) =
      LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s :=
    funext hfiber
  change HasSum (fun n => ∑' I : {I : Ideal (𝓞 F) // Ideal.absNorm I = n},
    η I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) _ at hgroup
  rw [heq] at hgroup
  exact (P.series s hs).tsum_eq.symm.trans hgroup.tsum_eq.symm

theorem principal_regularization_at_one
    (F : Type) [Field F] [NumberField F]
    (η : RayClassCharacter F (⊤ : Ideal (𝓞 F))) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F ⊤ η) :
    P.R 1 = (NumberField.dedekindZeta_residue F : ℂ) := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : ContinuousAt P.R 1 :=
    (P.R_holo.differentiableAt (hopen.mem_nhds (by norm_num))).continuousAt
  have hlim : Tendsto (fun x : ℝ => P.R (x : ℂ)) (𝓝[>] 1) (𝓝 (P.R 1)) :=
    hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  apply tendsto_nhds_unique hlim
  apply (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  rw [P.regularized _ (zero_lt_one.trans hx') (by intro h; rw [h] at hx'; norm_num at hx'),
    principal_continuation_eq_dedekindZeta F η hη P _ hx']

theorem exterior_residue_pos
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    0 < exteriorResidue F S := by
  classical
  apply mul_pos (NumberField.dedekindZeta_residue_pos F)
  apply Finset.prod_pos
  intro p hp
  have hn : (1 : ℝ) < Ideal.absNorm p.asIdeal := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm p
  exact sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans hn)).mpr hn)

theorem exterior_regularization_at_one
    (F : Type) [Field F] [NumberField F]
    (η : RayClassCharacter F (⊤ : Ideal (𝓞 F))) (hη : η.IsPrincipal)
    (P : PrincipalRayHeckeData F ⊤ η)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    exteriorRegularization F P S 1 = (exteriorResidue F S : ℂ) := by
  simp [exteriorRegularization, exteriorEulerFactor, exteriorResidue,
    principal_regularization_at_one F η hη P, Complex.cpow_neg,
    Complex.cpow_one, Complex.ofReal_prod]

end
end DedekindZetaZeroFree.PositiveZetaResidue
