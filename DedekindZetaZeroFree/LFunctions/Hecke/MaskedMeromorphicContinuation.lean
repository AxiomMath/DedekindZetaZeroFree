module

public import DedekindZetaZeroFree.Arithmetic.Kummer.SexticFrequencyCharacters
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalRayContinuation
public import DedekindZetaZeroFree.LFunctions.Hecke.PrincipalRayContinuation

@[expose] public section

open scoped NumberField Classical
open IsDedekindDomain

noncomputable section
namespace DedekindZetaZeroFree.MaskedHeckeMeromorphic
set_option autoImplicit false

open LocalFiniteSums CorrectionFactors FrequencyCharacterMasks

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}

inductive Row where
  | principal
  | plus
  | minus
  deriving DecidableEq

def primitive (U : Frequency C) (P : PrimitiveInducers U) :
    Row → Detector.PrimitiveFrequencyCharacter F
  | .principal => Detector.FrequencyPrincipal.principalPrimitive (F := F)
  | .plus => P.plus
  | .minus => P.minus

def deletionSet (U : Frequency C) : Row → Set (HeightOneSpectrum (𝓞 F))
  | .principal => (A.Sf : Set (HeightOneSpectrum (𝓞 F)))
  | .plus => frequencyMask U
  | .minus => frequencyMask U

def coefficient (U : Frequency C) : Row → Ideal (𝓞 F) → ℂ
  | .principal => principalCoefficient A
  | .plus => plusCoefficient U
  | .minus => minusCoefficient U

def incompleteL (U : Frequency C) (i : Row) (s : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s)

def poleIndicator (ν : Detector.PrimitiveFrequencyCharacter F) : ℕ :=
  if ν.character.IsPrincipal then 1 else 0

def deletionProduct (U : Frequency C) (P : PrimitiveInducers U)
    (i : Row) (s : ℂ) : ℂ :=
  Detector.finiteEulerDeletionMask F (deletionSet U i)
    (fun p => (primitive U P i).character p.asIdeal) s

def quotientRepresentative (U : Frequency C) (P : PrimitiveInducers U)
    (i : Row) (J : ℂ → ℂ) (s : ℂ) : ℂ :=
  J s * deletionProduct U P i s / (s - 1) ^ poleIndicator (primitive U P i)

structure RowContinuation (U : Frequency C) (P : PrimitiveInducers U) (i : Row) where
  J : ℂ → ℂ
  J_holomorphic : AnalyticOnNhd ℂ J {s : ℂ | 0 < s.re}
  J_not_identically_zero : ∃ s : ℂ, 0 < s.re ∧ J s ≠ 0
  deletion_finite : (deletionSet U i).Finite
  B_holomorphic : AnalyticOnNhd ℂ (deletionProduct U P i) {s : ℂ | 0 < s.re}
  B_nowhere_zero : ∀ s : ℂ, 0 < s.re → deletionProduct U P i s ≠ 0
  series : ∀ s : ℂ, 1 < s.re →
    HasSum (fun I : Ideal (𝓞 F) =>
      coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s))
      (quotientRepresentative U P i J s)
  regular_equality : ∀ s : ℂ, 1 < s.re →
    incompleteL U i s = quotientRepresentative U P i J s
  meromorphic_germs : MeromorphicOn (quotientRepresentative U P i J)
    {s : ℂ | 0 < s.re}

theorem principal_indicator (U : Frequency C) (P : PrimitiveInducers U) :
    poleIndicator (primitive U P .principal) = 1 := by
  change (if (Detector.FrequencyPrincipal.principalPrimitive (F := F)).character.IsPrincipal
    then 1 else 0) = 1
  exact if_pos (Detector.FrequencyPrincipal.principalPrimitive_principal (F := F))

private lemma positive_open : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private lemma primitive_series_ne_zero (ν : Detector.PrimitiveFrequencyCharacter F)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' I : Ideal (𝓞 F), ν.character I * (Ideal.absNorm I : ℂ) ^ (-s)) ≠ 0 := by
  have hcoeff := ExteriorIdealEuler.zeroMaskedRay_isCoefficient
    (cS := (⊤ : Ideal (𝓞 F))) ν.conductor ν.conductor_ne_zero ν.character ⊤
  have hn := (ExteriorIdealEuler.exterior_ideal_euler _ hcoeff s hs).2.2.1
  have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
      ν.character I * (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
      {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ ⊤ = ⊤} := by
    intro I hI
    refine ⟨?_, by simp⟩
    intro hzero
    have hz : ν.character I = 0 := (ν.character.eq_zero_iff' I).mpr (Or.inl hzero)
    exact hI (by simp [hz])
  have he := tsum_subtype_eq_of_support_subset hsupp
  rw [← he]
  change (∑' I : ExteriorIdeal (⊤ : Ideal (𝓞 F)),
    ν.character I.val * (Ideal.absNorm I.val : ℂ) ^ (-s)) ≠ 0
  simpa only [ExteriorIdealEuler.summand, ExteriorIdealEuler.zeroMaskedRayCoefficient,
    sup_top_eq, if_true] using hn

private lemma primitive_regularizer
    (hF : NumberField.IsTotallyComplex F) (ν : Detector.PrimitiveFrequencyCharacter F) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J {s : ℂ | 0 < s.re} ∧
      (∃ s : ℂ, 0 < s.re ∧ J s ≠ 0) ∧
      ∀ s : ℂ, 1 < s.re → HasSum
        (fun I : Ideal (𝓞 F) => ν.character I * (Ideal.absNorm I : ℂ) ^ (-s))
        (J s / (s - 1) ^ poleIndicator ν) := by
  by_cases hp : ν.character.IsPrincipal
  · let H := principalRayHeckeData F hF ν.conductor ν.conductor_ne_zero
      ν.character ν.primitive hp
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    have hne : (2 : ℂ) ≠ 1 := by norm_num
    have hR : H.R 2 ≠ 0 := by
      rw [H.regularized 2 (by norm_num) hne]
      exact mul_ne_zero (sub_ne_zero.mpr hne)
        (by rw [← (H.series 2 h2).tsum_eq]; exact primitive_series_ne_zero ν 2 h2)
    refine ⟨H.R, H.R_holo.analyticOnNhd positive_open, ⟨2, by norm_num, hR⟩, ?_⟩
    intro s hs
    have hs0 : 0 < s.re := lt_trans (by norm_num) hs
    have hs1 : s ≠ 1 := by intro he; subst s; norm_num at hs
    have he : H.R s / (s - 1) ^ poleIndicator ν = H.L s := by
      rw [poleIndicator, if_pos hp, pow_one, H.regularized s hs0 hs1]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)
    rw [he]
    exact H.series s hs
  · let H := nonprincipalRayHeckeData F hF ν.conductor ν.conductor_ne_zero
      ν.character ν.primitive hp
    refine ⟨H.L, H.L_holo.analyticOnNhd positive_open, ⟨2, by norm_num, ?_⟩, ?_⟩
    · rw [← (H.series 2 (by norm_num)).tsum_eq]
      exact primitive_series_ne_zero ν 2 (by norm_num)
    · intro s hs
      simpa [poleIndicator, hp] using H.series s hs

private lemma row_deletion_finite (U : Frequency C) (i : Row) :
    (deletionSet U i).Finite := by
  have hf : (frequencyMask U).Finite := by
    rw [frequencyMask_eq_principal_support]
    exact A.Sf.finite_toSet.union
      (Detector.exterior_frequency_support_finite_norm_pos F _ A.Sf.finite_toSet
        U.u U.generates.1).1
  cases i
  · exact A.Sf.finite_toSet
  · exact hf
  · exact hf

private lemma row_coefficient_eq (U : Frequency C) (P : PrimitiveInducers U) (i : Row) :
    coefficient U i = Detector.deletedPrimitiveIdealCoefficient F
      (primitive U P i) (deletionSet U i) := by
  funext I
  cases i
  · exact (principal_mask_exactly_S A).2.1 I
  · exact P.plus_mask I
  · exact P.minus_mask I

theorem masked_hecke_meromorphic
     (U : Frequency C) :
    ∃ P : PrimitiveInducers U, ∀ i : Row, Nonempty (RowContinuation U P i) := by
  obtain ⟨P⟩ := primitiveInducers_exists U
  refine ⟨P, fun i => ?_⟩
  let ν := primitive U P i
  have hD := row_deletion_finite U i
  obtain ⟨J, hJ, hJne, hseries⟩ := primitive_regularizer
    (primitive12_totallyComplex F A.zeta12 A.primitive_zeta12) ν
  have hm : MeromorphicOn (fun s : ℂ => J s / (s - 1) ^ poleIndicator ν)
      {s : ℂ | 0 < s.re} := by
    exact hJ.meromorphicOn.div
      ((analyticOnNhd_id.sub analyticOnNhd_const).pow (poleIndicator ν)).meromorphicOn
  obtain ⟨hBdiff, hBmero, hBs⟩ := Detector.deleted_primitive_L_continuation F ν
    (deletionSet U i) hD {s : ℂ | 0 < s.re}
    (fun s : ℂ => J s / (s - 1) ^ poleIndicator ν) hm hseries
  have hB : AnalyticOnNhd ℂ (deletionProduct U P i) {s : ℂ | 0 < s.re} :=
    hBdiff.differentiableOn.analyticOnNhd positive_open
  have hregular : ∀ s : ℂ, 1 < s.re → HasSum
      (fun I : Ideal (𝓞 F) => coefficient U i I * (Ideal.absNorm I : ℂ) ^ (-s))
      (quotientRepresentative U P i J s) := by
    intro s hs
    rw [row_coefficient_eq U P i]
    simpa only [quotientRepresentative, deletionProduct, ν, div_mul_eq_mul_div]
      using hBs s hs
  refine ⟨{
    J := J
    J_holomorphic := hJ
    J_not_identically_zero := hJne
    deletion_finite := hD
    B_holomorphic := hB
    B_nowhere_zero := ?_
    series := hregular
    regular_equality := fun s hs => (hregular s hs).tsum_eq
    meromorphic_germs := ?_
  }⟩
  · intro s hs
    letI := hD.fintype
    change Detector.finiteEulerDeletionMask F (deletionSet U i)
      (fun p => ν.character p.asIdeal) s ≠ 0
    rw [Detector.finiteEulerDeletionMask, finprod_eq_prod_of_fintype]
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact (Detector.finite_euler_local_factor_nonzero F s.re hs p.val
      (ν.character p.val.asIdeal) s
      (RayUnitary.ray_character_norm_le_one F ν.conductor ν.conductor_ne_zero
        ν.character p.val.asIdeal) le_rfl).2.2
  · exact (hJ.meromorphicOn.mul hB.meromorphicOn).div
      ((analyticOnNhd_id.sub analyticOnNhd_const).pow (poleIndicator ν)).meromorphicOn

end DedekindZetaZeroFree.MaskedHeckeMeromorphic

end
