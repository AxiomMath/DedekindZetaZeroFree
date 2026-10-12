module

public import DedekindZetaZeroFree.Metaplectic.Torus.CompatibleCharacterAdjustment
public import DedekindZetaZeroFree.Eisenstein.Induction.LocalSphericalSections

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FrozenFibers
open KPGlobalTorusFiniteStages KPGlobalTorusTensorFibers KPLocalStoneVonNeumann
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

theorem exists_fibers (P : CompatibleModelData F ζ hζ)
    (hS : P.adjustment.S = A.Sf)
    (hP : ∀ q ∉ A.Sf, KPGlobalProductPolarizationCharacter.IsUnramified F ζ hζ q
      (P.localData.localData (Sum.inr q))) :
    ∃ C : LocalFiberData F ζ hζ P, C.exceptional = A.Sf := by
  choose M hM using KPGlobalTorusFiniteStagesLocalSteps.canonical_good_compact_model_exists F ζ hζ
  choose psi hpsi using fun q : HeightOneSpectrum (𝓞 F) =>
    KPGlobalTorusFiniteStagesLocalSteps.adjusted_local_character_exists F ζ hζ
      (Sum.inr q) (P.localData.localData (Sum.inr q)) (P.adjustment.chi (Sum.inr q))
  have hpsi_center : ∀ q
      (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
        (P.localData.localData (Sum.inr q)).L)
      (z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ (Sum.inr q)),
      b.val = z.val → psi q b =
        KPGlobalProductPolarizationCharacter.localOmega F ζ hζ (Sum.inr q) z := by
    intro q b z hbz
    rw [hpsi q b]
    exact adjustedLocalValue_preserves_center F ζ hζ P.localData P.adjustment (Sum.inr q) b z hbz
  choose B hB hCB chi hchi hsub hchar using fun q =>
    KPGlobalTorusFiniteStagesLocalSteps.transport_local_polarization_character F ζ hζ
      q (M q) (P.localData.localData (Sum.inr q)) (psi q) (hpsi_center q)
  choose Q hQ hQchar using fun q =>
    polarization_matching_maximal_abelian (M q).heisenberg (B q)
      (hB q) (hCB q) (chi q) (hchi q)
  have hmatched : ∀ q,
      ((Q q).L.comap (M q).heisenberg.π).map
        (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype =
      (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
        (P.localData.localData (Sum.inr q)).L).map
        (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype := by
    intro q
    rw [hQ q]
    exact hsub q
  have hcharacters : ∀ q
      (a : (Q q).L.comap (M q).heisenberg.π)
      (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
        (P.localData.localData (Sum.inr q)).L),
      a.val.val = b.val.val → (Q q).ωL a = psi q b := by
    intro q a b hab
    let a' : B q := ⟨a.val, (le_of_eq (hQ q)) a.property⟩
    exact (hQchar q a a' rfl).trans (hchar q a' b hab)
  have htrivial : ∀ q ∉ A.Sf, ∀ b : KPGlobalProductPolarizationCharacter.localPreimage
      F ζ hζ (Sum.inr q) (P.localData.localData (Sum.inr q)).L,
      b.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) →
        psi q b = 1 := by
    intro q hq b hb
    rw [hpsi q b]
    change KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ
      P.localData P.adjustment (Sum.inr q) b = 1
    rw [KPGlobalProductPolarizationCharacter.adjustedLocalValue_outside F ζ hζ
      P.localData P.adjustment q (by simpa [hS] using hq)]
    exact (hP q hq).2.2 b hb
  refine ⟨{
    canonical := M
    polarization := Q
    subgroup_matches := hmatched
    character_matches := ?_
    exceptional := A.Sf
    unramified := ?_
    actual_compact := ?_ }, rfl⟩
  · intro q a b hab
    exact (hcharacters q a b hab).trans (hpsi q b)
  · intro q hq
    obtain ⟨ht, hc, hr⟩ := hM q (hP q hq).1
    apply KPGlobalTorusFiniteStagesLocalSteps.unramified_of_local_matching F ζ hζ
      q (M q) (Q q) (P.localData.localData (Sum.inr q)) (psi q)
      (hP q hq).1 (hP q hq).2.1 ⟨ht, hc⟩ hr (hmatched q) (hcharacters q)
    exact htrivial q hq
  · intro q hq
    obtain ⟨ht, hc, _⟩ := hM q (hP q hq).1
    exact ⟨ht, hc⟩

theorem exists_model_fibers (hCl : Subsingleton (ClassGroup A.R)) :
    ∃ (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P),
      P.adjustment.S = A.Sf ∧ C.exceptional = A.Sf := by
  obtain ⟨P, hS, hP⟩ := FrozenAdjustment.exists_model A hCl
  obtain ⟨C, hC⟩ := exists_fibers A P hS hP
  exact ⟨P, C, hS, hC⟩

end DedekindZetaZeroFree.EisensteinReferenceSections.FrozenFibers

end
