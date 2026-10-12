module

public import DedekindZetaZeroFree.Metaplectic.Torus.ProductPolarizationCharacter

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FrozenTorus
open KPGlobalCubicIdelePairing
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

open _root_.DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw renaming char_mem → char_mem

theorem outside_good (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ A.Sf) :
    ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
  intro hb
  have hs : (6 : 𝓞 F) ∈ q.asIdeal := by
    rcases hb with hb | hb
    · exact q.asIdeal.mem_of_dvd (⟨3, by norm_num⟩ : (2 : 𝓞 F) ∣ 6) (char_mem F q 2 hb)
    · exact q.asIdeal.mem_of_dvd (⟨2, by norm_num⟩ : (3 : 𝓞 F) ∣ 6) (char_mem F q 3 hb)
  exact hq (A.above_six q hs)

private theorem localPairing_one_left (v : KPHilbert.Place F) (a : LocalD F v) :
    localPairing F A.zeta12 A.primitive_zeta12 v 1 a = 1 := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    change KPHilbert.B3 F A.zeta12 A.primitive_zeta12 v 1 a = 1
    simpa using ((KPHilbert.B3_laws F A.zeta12 A.primitive_zeta12 v).2.2.2.2.1 1 a).1

theorem supported_class_mem_unit (u : _root_.IdeleGroup F)
    (hu : u ∈ _root_.IdeleGroup.supportedAt (K := F) (A.Sf : Set _))
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ A.Sf) :
    classComparison F (QuotientGroup.mk' _ (_root_.IdeleGroup.equivAdeleRingUnits u))
      (Sum.inr q) ∈ U F (Sum.inr q) := by
  have hunit := (_root_.IdeleGroup.mem_supportedAt_iff
    (K := F) (A.Sf : Set _) u).mp hu q hq
  letI : ValuativeRel (q.adicCompletion F) :=
    ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have mem (z : q.adicCompletion F) (hz : z ∈ q.adicCompletionIntegers F) :
      z ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
    rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
    exact (Valuation.vle_one_iff
      (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr hz
  let z := u.2 q
  let b : KPHilbert.LocalIntegerUnits F q :=
    ⟨⟨z.val, mem _ hunit.1⟩, ⟨z.inv, mem _ hunit.2⟩,
      by apply Subtype.ext; exact z.val_inv,
      by apply Subtype.ext; exact z.inv_val⟩
  exact ⟨_, ⟨b, rfl⟩, rfl⟩

theorem principal_eq_one_of_frozen_coordinates
    (hCl : Subsingleton (ClassGroup A.R)) (d : D F)
    (hd : d ∈ KPGlobalPrincipalCubicLagrangian.A F)
    (hS : ∀ q ∈ A.Sf, classComparison F d (Sum.inr q) = 1)
    (hU : ∀ q ∉ A.Sf, classComparison F d (Sum.inr q) ∈ U F (Sum.inr q)) :
    d = 1 := by
  apply (beta3_radical_zero F A.zeta12 A.primitive_zeta12 d).mp
  intro y
  induction y using QuotientGroup.induction_on with
  | H y =>
    let e := _root_.IdeleGroup.equivAdeleRingUnits (K := F)
    obtain ⟨u, a, hu, hy⟩ :=
      exists_supportedAt_mul_principalIdele_of_classGroup_subsingleton
        F A hCl (e.symm y)
    have hy' : y = e u * IdeleGroup.unitEmbedding (𝓞 F) F a := by
      have h := congrArg e hy
      simpa only [e, MulEquiv.apply_symm_apply, map_mul,
        _root_.IdeleGroup.equivAdeleRingUnits_principalIdele] using h
    change beta3 F A.zeta12 A.primitive_zeta12 d (QuotientGroup.mk' _ y) = 1
    rw [hy', map_mul, (beta3_bilinear F A.zeta12 A.primitive_zeta12).2.1]
    have hp : beta3 F A.zeta12 A.primitive_zeta12 d
        (KPGlobalPrincipalCubicLagrangian.principalClass F a) = 1 := by
      have hm : d ∈ KPGlobalPrincipalCubicLagrangian.annihilator
          F A.zeta12 A.primitive_zeta12 (KPGlobalPrincipalCubicLagrangian.A F) := by
        rw [KPGlobalPrincipalCubicLagrangian.principal_self_annihilating]
        exact hd
      exact hm _ ⟨a, rfl⟩
    have hu' : beta3 F A.zeta12 A.primitive_zeta12 d (QuotientGroup.mk' _ (e u)) = 1 := by
      unfold beta3 restrictedBeta
      apply finprod_eq_one_of_forall_eq_one
      intro v
      cases v with
      | inl w =>
        letI := local_complex_trivial F w
        rw [show classComparison F d (Sum.inl w) = 1 from Subsingleton.elim _ _]
        exact localPairing_one_left A _ _
      | inr q =>
        by_cases hq : q ∈ A.Sf
        · rw [hS q hq]
          exact localPairing_one_left A _ _
        · exact tame_unit_isotropic F A.zeta12 A.primitive_zeta12 q
            (outside_good A q hq) _ _ (hU q hq) (supported_class_mem_unit A u hu q hq)
    change beta3 F A.zeta12 A.primitive_zeta12 d (QuotientGroup.mk' _ (e u)) *
      beta3 F A.zeta12 A.primitive_zeta12 d
        (KPGlobalPrincipalCubicLagrangian.principalClass F a) = 1
    rw [hu', hp, mul_one]

end DedekindZetaZeroFree.EisensteinReferenceSections.FrozenTorus

end
