module

public import DedekindZetaZeroFree.Theta.RayClasses.ZeroModeCancellation
public import DedekindZetaZeroFree.LFunctions.Hecke.Completion.ConductorGammaPrefactor
public import DedekindZetaZeroFree.LFunctions.Hecke.Completion.PrefactorNormalization
public import DedekindZetaZeroFree.Theta.Unfolding.NarrowRayParityProjection

@[expose] public section

noncomputable section

open scoped NumberField Classical
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]
variable {m : Ideal (𝓞 F)} {hm : m ≠ ⊥}
variable {η : DedekindZetaZeroFree.RayClassCharacter F m}

private theorem partial_hasSum (hF : NumberField.IsTotallyComplex F)
    (E : RayCoset.Data F) (hEm : E.m = m) (c : RayIdealClass F m hm)
    (hc : rayIdealClass F m hm E.a = some c⁻¹) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 F) =>
      if rayIdealClass F m hm I = some c then (Ideal.absNorm I : ℂ) ^ (-s) else 0)
      (RayCoset.Zδ E ∅ s) := by
  letI : NumberField.IsTotallyComplex F := hF
  letI : IsEmpty (RayCoset.RealPlaces F) :=
    ⟨fun v => NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (NumberField.IsTotallyComplex.isComplex v.1) v.2⟩
  have hr : NumberField.InfinitePlace.nrRealPlaces F = 0 := Fintype.card_eq_zero
  subst m
  simpa [hr, Finset.univ_eq_empty] using
    DedekindZetaZeroFree.rayParityProjection E c hc s hs

private theorem sum_hasMellin {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (M : ι → ℂ) (s : ℂ)
    (h : ∀ i ∈ S, HasMellin (f i) s (M i)) :
    HasMellin (fun t => ∑ i ∈ S, f i t) s (∑ i ∈ S, M i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [HasMellin, MellinConvergent, mellin]
  | @insert a S ha ih =>
    have hS := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a S)
    simpa only [Finset.sum_insert ha, ha'.2, hS.2] using hasMellin_add ha'.1 hS.1

private theorem scale_hasMellin {f : ℝ → ℂ} {s M : ℂ} {a : ℝ}
    (ha : 0 < a) (h : HasMellin f s M) :
    HasMellin (fun t => f (t / a)) s ((a : ℂ) ^ s * M) := by
  have he : ((a⁻¹ : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ s := by
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg ha.le, Complex.cpow_neg, inv_inv]
  constructor
  · simpa only [div_eq_mul_inv, mul_comm] using
      (MellinConvergent.comp_mul_left (inv_pos.mpr ha)).mpr h.1
  · simpa only [div_eq_mul_inv, mul_comm, smul_eq_mul, he, h.2] using
      mellin_comp_mul_left f s (inv_pos.mpr ha)

private theorem scale_cpow (hm : m ≠ ⊥) (s : ℂ) :
    (conductorScale F m : ℂ) ^ s =
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) := by
  have ha := conductorScale_pos (F := F) hm
  have hpow := Complex.cpow_ofNat_mul' (x := (conductorScale F m : ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg ha.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg ha.le, Real.pi_pos.le]) (s / 2)
  have hsq : (conductorScale F m : ℂ) ^ (2 : ℕ) =
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) := by
    rw [← Complex.ofReal_pow, conductorScale_sq hm]
    simp only [conductorNorm, ← Int.cast_abs, Complex.ofReal_mul,
      Complex.ofReal_intCast, Complex.ofReal_natCast]
  rw [hsq] at hpow
  convert hpow using 1 <;> ring

private theorem aggregate_calibration
    (hF : NumberField.IsTotallyComplex F) (D : RayThetaRepresentatives F m hm)
    (w : RayIdealClass F m hm → ℂ) (v : Ideal (𝓞 F) → ℂ)
    (hdescent : ∀ I, v I = match rayIdealClass F m hm I with
      | none => 0 | some c => w c)
    (f : ℝ → ℂ)
    (hf : ∀ t, 0 < t → f t = (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F *
      ∑ c : RayIdealClass F m hm, w c *
        (RayTheta.fδ (D.coset c) ∅ (t / conductorScale F m) - RayTheta.f0δ (D.coset c) ∅))
    (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent f s ∧ HasSum (fun I : Ideal (𝓞 F) =>
      normalizedHeckePrefactor F m s * (v I * (Ideal.absNorm I : ℂ) ^ (-s)))
      (mellin f s) := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  let Z := fun c => RayCoset.Zδ (D.coset c) ∅ s
  let g := fun t => ∑ c : RayIdealClass F m hm,
    w c * (RayTheta.fδ (D.coset c) ∅ t - RayTheta.f0δ (D.coset c) ∅)
  have hg : HasMellin g s (RayParity.κδ F ∅ s * ∑ c, w c * Z c) := by
    have h := sum_hasMellin Finset.univ
      (fun c t => w c * (RayTheta.fδ (D.coset c) ∅ t - RayTheta.f0δ (D.coset c) ∅))
      (fun c => w c * (RayParity.κδ F ∅ s * Z c)) s (by
        intro c _
        have h := RayParity.ThetaMellinIntegral.hasMellin (D.coset c) ∅ s hs
        have h' := hasMellin_const_smul h.1 (w c)
        simpa only [smul_eq_mul, h.2] using h')
    convert h using 1
    simp only [Finset.mul_sum, Z]
    congr 1
    ext c
    ring
  have hscaled := scale_hasMellin (conductorScale_pos hm) hg
  have htotal := hasMellin_const_smul hscaled.1
    ((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F)
  have hM : HasMellin
      (fun t => (4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F * g (t / conductorScale F m))
      s (normalizedHeckePrefactor F m s * ∑ c, w c * Z c) := by
    convert htotal using 1
    rw [hscaled.2, scale_cpow hm, normalizedHeckePrefactor,
      completed_prefactor_eq_kappa F hF m s]
    simp only [smul_eq_mul]
    ring
  have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun t => (t : ℂ) ^ (s - 1) •
        ((4 : ℂ) ^ NumberField.InfinitePlace.nrComplexPlaces F * g (t / conductorScale F m))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hf t ht]
  have hconv : MellinConvergent f s := hM.1.congr heq.symm
  have hmel : mellin f s = normalizedHeckePrefactor F m s * ∑ c, w c * Z c := by
    rw [mellin, MeasureTheory.integral_congr_ae heq]
    exact hM.2
  have hseries : HasSum (fun I => v I * (Ideal.absNorm I : ℂ) ^ (-s))
      (∑ c, w c * Z c) := by
    have h := hasSum_sum (s := Finset.univ) (fun c _ =>
      (partial_hasSum hF (D.coset c) (D.modulus_eq c) c (D.inverse_class c) s hs).mul_left (w c))
    apply h.congr_fun
    intro I
    rw [hdescent I]
    cases hI : rayIdealClass F m hm I with
    | none => simp [hI]
    | some c => simp [hI, eq_comm]
  refine ⟨hconv, ?_⟩
  rw [hmel]
  exact hseries.mul_left _

theorem normalizedRayTheta_mellin_calibration
    (hF : NumberField.IsTotallyComplex F)
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent (normalizedRayTheta D χ.ψ) s ∧
      HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          (η I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (mellin (normalizedRayTheta D χ.ψ) s) := by
  exact aggregate_calibration hF D χ.ψ η χ.descent
    (normalizedRayTheta D χ.ψ)
    (normalizedRayTheta_eq_sub_zero_modes D χ hη) s hs

theorem normalizedRayConjugateTheta_mellin_calibration
    (hF : NumberField.IsTotallyComplex F)
    (D : RayThetaRepresentatives F m hm) (χ : RayCharacterData F m hm η)
    (hη : ¬ η.IsPrincipal) (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent (normalizedRayConjugateTheta D χ.ψ) s ∧
      HasSum (fun I : Ideal (𝓞 F) =>
        (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
          Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
          ((starRingEnd ℂ) (η I) * (Ideal.absNorm I : ℂ) ^ (-s)))
        (mellin (normalizedRayConjugateTheta D χ.ψ) s) := by
  apply aggregate_calibration hF D (fun c => (starRingEnd ℂ) (χ.ψ c))
    (fun I => (starRingEnd ℂ) (η I)) ?_
    (normalizedRayConjugateTheta D χ.ψ)
    (normalizedRayConjugateTheta_eq_sub_zero_modes D χ hη) s hs
  intro I
  rw [χ.descent I]
  cases rayIdealClass F m hm I <;> simp

end DedekindZetaZeroFree.Hecke.Theta

end
