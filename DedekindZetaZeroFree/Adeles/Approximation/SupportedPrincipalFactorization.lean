module

public import ClassFieldTheory.All
public import DedekindZetaZeroFree.Arithmetic.Ideals.SClassPrincipalization

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped NumberField WithZero nonZeroDivisors

set_option maxHeartbeats 800000
noncomputable section

namespace DedekindZetaZeroFree.SUnitFactorProof
variable (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
 abbrev extHom : FractionalIdeal (𝓞 F)⁰ F →+* FractionalIdeal A.R⁰ F :=
  FractionalIdeal.extendedHom (K := F) F A.R
private lemma map_id : IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 F) A.R) = RingHom.id F := by
  apply IsLocalization.ringHom_ext (𝓞 F)⁰
  ext a
  simp [IsFractionRing.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply]
private lemma ext_coe (I : FractionalIdeal (𝓞 F)⁰ F) :
    (extHom F A I : Submodule A.R F) = Submodule.span A.R (I : Set F) := by
  simp only [extHom, FractionalIdeal.extendedHom, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span]
  change Submodule.span A.R ((IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 F) A.R)) '' (I : Set F)) = _
  rw [map_id]
  simp
private lemma member_bound (J : FractionalIdealGroup F) (v : HeightOneSpectrum (𝓞 F))
    (y : F) (hy : y ∈ (J : FractionalIdeal (𝓞 F)⁰ F)) :
    v.valuation F y ≤ WithZero.exp (-FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F)) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  let x : Fˣ := Units.mk0 y hy0
  have hc := FractionalIdeal.count_mono F v
    (I := FractionalIdeal.spanSingleton (𝓞 F)⁰ y)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)
  have hp := IdeleGroup.count_toPrincipalIdeal x v
  simp only [coe_toPrincipalIdeal, x, Units.val_mk0] at hp
  rw [hp] at hc
  have hv0 : v.valuation F y ≠ 0 := (v.valuation F).ne_zero_iff.mpr hy0
  rw [← WithZero.exp_log hv0, WithZero.exp_le_exp]
  omega
private lemma extended_bound (J : FractionalIdealGroup F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) (y : F) (hy : y ∈ extHom F A (J : FractionalIdeal (𝓞 F)⁰ F)) :
    v.valuation F y ≤ WithZero.exp (-FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F)) := by
  change y ∈ (extHom F A (J : FractionalIdeal (𝓞 F)⁰ F) : Submodule A.R F) at hy
  rw [ext_coe] at hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact member_bound F J v y hy
  | zero => simp
  | add y z _ _ hy hz => exact ((v.valuation F).map_add y z).trans (max_le hy hz)
  | smul r y _ hy =>
    change v.valuation F ((r : F) * y) ≤ _
    rw [map_mul]
    have hr : v.valuation F (r : F) ≤ 1 :=
      Set.integer_valuation_le_one (R := 𝓞 F) (A.Sf : Set (HeightOneSpectrum (𝓞 F))) F r (v := v) hv
    have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ v.valuation F y from zero_le)
    exact hm.trans (by simpa using hy)
private lemma count_le_extended (J : FractionalIdealGroup F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) (x : Fˣ) (hx : (x : F) ∈ extHom F A (J : FractionalIdeal (𝓞 F)⁰ F)) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) ≤
      FractionalIdeal.count F v (toPrincipalIdeal (𝓞 F) F x : FractionalIdeal (𝓞 F)⁰ F) := by
  have h := extended_bound F A J v hv x hx
  rw [IdeleGroup.count_toPrincipalIdeal]
  have hv0 : v.valuation F (x : F) ≠ 0 := (v.valuation F).ne_zero_iff.mpr x.ne_zero
  rw [← WithZero.exp_log hv0, WithZero.exp_le_exp] at h
  omega
private lemma exists_generator (hCl : Subsingleton (ClassGroup A.R)) (J : FractionalIdealGroup F) :
    ∃ x : Fˣ, extHom F A (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton A.R⁰ (x : F) := by
  letI := hCl
  have hu : IsUnit (extHom F A (J : FractionalIdeal (𝓞 F)⁰ F)) :=
    J.isUnit.map (extHom F A).toMonoidHom
  exact exists_unit_of_isPrincipal _
    (ClassGroup.isPrincipal_coeSubmodule_of_isUnit _ hu) hu.ne_zero
private lemma count_eq (J : FractionalIdealGroup F) (x : Fˣ)
    (hx : extHom F A (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton A.R⁰ (x : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.count F v (toPrincipalIdeal (𝓞 F) F x : FractionalIdeal (𝓞 F)⁰ F) := by
  apply le_antisymm
  · apply count_le_extended F A J v hv x
    rw [hx]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  · have hxi : extHom F A (J⁻¹ : FractionalIdealGroup F) = FractionalIdeal.spanSingleton A.R⁰ ((x⁻¹ : Fˣ) : F) := by
      have hui : IsUnit (FractionalIdeal.spanSingleton A.R⁰ (x : F)) := by
        rw [← hx]
        exact J.isUnit.map (extHom F A).toMonoidHom
      apply hui.mul_left_cancel
      rw [← hx, ← map_mul]
      simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      rw [hx, FractionalIdeal.spanSingleton_mul_spanSingleton]
      simp
    have h := count_le_extended F A J⁻¹ v hv x⁻¹ (by rw [hxi]; exact FractionalIdeal.mem_spanSingleton_self _ _)
    simp only [Units.val_inv_eq_inv_val, map_inv, FractionalIdeal.count_inv] at h
    omega
private lemma exists_factor (hCl : Subsingleton (ClassGroup A.R)) (a : IdeleGroup F) :
    ∃ (u : IdeleGroup F) (x : Fˣ),
      u ∈ IdeleGroup.supportedAt (K := F) (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∧
      a = u * IdeleGroup.principalIdele F x := by
  let J := IdeleGroup.fractionalIdeal a
  obtain ⟨x, hx⟩ := exists_generator F A hCl J
  refine ⟨a * (IdeleGroup.principalIdele F x)⁻¹, x, ?_, by simp⟩
  rw [IdeleGroup.mem_supportedAt_iff]
  intro v hv
  apply (FiniteIdeleGroup.localOrder_eq_zero_iff v _).mp
  have hc := count_eq F A J x hx v hv
  have hp := congrArg (fun I : FractionalIdealGroup F => FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F)) (IdeleGroup.fractionalIdeal_principalIdele x)
  rw [← hp] at hc
  change FractionalIdeal.count F v (((FractionalIdealGroup.factorization (K := F)) (FiniteIdeleGroup.valuationVector a.2)) : FractionalIdeal (𝓞 F)⁰ F) =
    FractionalIdeal.count F v (((FractionalIdealGroup.factorization (K := F)) (FiniteIdeleGroup.valuationVector (IdeleGroup.principalIdele F x).2)) : FractionalIdeal (𝓞 F)⁰ F) at hc
  rw [FractionalIdealGroup.count_factorization, FractionalIdealGroup.count_factorization,
    FiniteIdeleGroup.valuationVector_apply, FiniteIdeleGroup.valuationVector_apply] at hc
  change (FiniteIdeleGroup.localOrder v (a.2 v * ((IdeleGroup.principalIdele F x).2 v)⁻¹)).toAdd = 0
  rw [map_mul, map_inv]
  change (FiniteIdeleGroup.localOrder v (a.2 v)).toAdd -
    (FiniteIdeleGroup.localOrder v ((IdeleGroup.principalIdele F x).2 v)).toAdd = 0
  exact sub_eq_zero.mpr hc
end DedekindZetaZeroFree.SUnitFactorProof

namespace DedekindZetaZeroFree

theorem supportedAt_sup_principalSubgroup_eq_top_of_classGroup_subsingleton
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) :
    IdeleGroup.supportedAt (K := F) (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ⊔
      IdeleGroup.principalSubgroup F = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨u, x, hu, hux⟩ := SUnitFactorProof.exists_factor F A hCl a
  rw [hux]
  exact Subgroup.mul_mem_sup hu ⟨x, rfl⟩

theorem exists_supportedAt_mul_principalIdele_of_classGroup_subsingleton
    (F : Type) [Field F] [NumberField F] (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (a : IdeleGroup F) :
    ∃ (u : IdeleGroup F) (x : Fˣ),
      u ∈ IdeleGroup.supportedAt (K := F) (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ∧
      a = u * IdeleGroup.principalIdele F x := by
  exact SUnitFactorProof.exists_factor F A hCl a

end DedekindZetaZeroFree

end
