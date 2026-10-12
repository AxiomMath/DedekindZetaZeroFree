module

public import DedekindZetaZeroFree.Adeles.Lattices.SupportedPrincipalIntersection

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

def normOneClassQuotient (_A : SArithmeticData F) :
    IdeleGroup.normOneSubgroup (K := F) →*
      IdeleClassGroup.normOneSubgroup (K := F) :=
  ((QuotientGroup.mk' (IdeleGroup.principalSubgroup F)).comp
    (IdeleGroup.normOneSubgroup (K := F)).subtype).codRestrict _ fun a =>
      (IdeleClassGroup.mk_mem_normOneSubgroup_iff a.val).2 a.prop

def supportedClassMap : A.H →* IdeleClassGroup.normOneSubgroup (K := F) :=
  A.normOneClassQuotient.comp A.H.subtype

def J : Subgroup (IdeleClassGroup.normOneSubgroup (K := F)) :=
  A.supportedClassMap.range

def supportedClassRestriction : A.H →* A.J :=
  A.supportedClassMap.rangeRestrict

private theorem continuous_normOneClassQuotient : Continuous A.normOneClassQuotient := by
  exact (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _

private theorem isOpenMap_normOneClassQuotient : IsOpenMap A.normOneClassQuotient := by
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
  let T : Set (IdeleClassGroup F) := IdeleClassGroup.normOneSubgroup (K := F)
  have h : (IdeleGroup.normOneSubgroup (K := F) : Set (IdeleGroup F)) = q ⁻¹' T := by
    ext a
    exact (IdeleClassGroup.mk_mem_normOneSubgroup_iff a).symm
  exact ((QuotientGroup.isOpenMap_coe (N := IdeleGroup.principalSubgroup F)).restrictPreimage T).comp
    (Homeomorph.setCongr h).isOpenMap

private theorem isOpenMap_supportedClassMap : IsOpenMap A.supportedClassMap := by
  exact (isOpenMap_normOneClassQuotient A).domRestrict A.isOpen_H

theorem isOpen_J :
    IsOpen (A.J : Set (IdeleClassGroup.normOneSubgroup (K := F))) := by
  change IsOpen (Set.range A.supportedClassMap)
  simpa only [Set.image_univ] using isOpenMap_supportedClassMap A Set.univ isOpen_univ

theorem isClosed_J :
    IsClosed (A.J : Set (IdeleClassGroup.normOneSubgroup (K := F))) := by
  exact A.J.isClosed_of_isOpen A.isOpen_J

theorem continuous_supportedClassRestriction :
    Continuous A.supportedClassRestriction := by
  exact ((continuous_normOneClassQuotient A).comp continuous_subtype_val).subtype_mk _

theorem isOpenMap_supportedClassRestriction :
    IsOpenMap A.supportedClassRestriction := by
  exact (isOpenMap_supportedClassMap A).codRestrict _

theorem surjective_supportedClassRestriction :
    Function.Surjective A.supportedClassRestriction := by
  exact A.supportedClassMap.rangeRestrict_surjective

theorem ker_supportedClassRestriction :
    A.supportedClassRestriction.ker = A.principalIntersection := by
  ext h
  change A.supportedClassRestriction h = 1 ↔ h.1.1 ∈ IdeleGroup.principalSubgroup F
  rw [← Subtype.val_inj]
  change A.supportedClassMap h = 1 ↔ _
  rw [← Subtype.val_inj]
  exact QuotientGroup.eq_one_iff h.1.1

theorem exists_supportedClassQuotientHomeomorph :
    ∃ e : (A.H ⧸ A.principalIntersection) ≃ₜ* A.J,
      ∀ h : A.H, e (QuotientGroup.mk' A.principalIntersection h) =
        A.supportedClassRestriction h := by
  let e : (A.H ⧸ A.principalIntersection) ≃* A.J :=
    (QuotientGroup.quotientMulEquivOfEq A.ker_supportedClassRestriction.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective A.supportedClassRestriction
        A.surjective_supportedClassRestriction)
  have he (h : A.H) : e (QuotientGroup.mk' A.principalIntersection h) =
      A.supportedClassRestriction h := rfl
  have hc : Continuous e := by
    apply (QuotientGroup.isOpenQuotientMap_mk (N := A.principalIntersection)).continuous_comp_iff.mp
    exact A.continuous_supportedClassRestriction
  have ho : IsOpenMap e := by
    apply IsOpenMap.of_comp QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective A.principalIntersection)
    exact A.isOpenMap_supportedClassRestriction
  exact ⟨{ e with
    continuous_toFun := hc
    continuous_invFun := (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).continuous_invFun }, he⟩

theorem sCoordinatesRaw_H_norm (h : A.H) :
    A.norm (A.sCoordinatesRaw h.1.1) = 1 := by
  rw [A.sCoordinatesRaw_norm h.1.1 h.2]
  have hn : IdeleGroup.absoluteNorm h.1.1 = 1 := h.1.2
  simp [hn]

def sCoordinates : A.H →* A.G1 where
  toFun h := ⟨A.sCoordinatesRaw h.1.1, A.sCoordinatesRaw_H_norm h⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · funext w
      exact congrFun (map_one ContinuousMulEquiv.piUnits) w
    · rfl
  map_mul' h k := by
    apply Subtype.ext
    apply Prod.ext
    · funext w
      exact congrFun (map_mul ContinuousMulEquiv.piUnits h.1.1.1 k.1.1.1) w
    · rfl

theorem exists_supportedUnitQuotientProjection :
    ∃ p : (A.H ⧸ A.principalIntersection) →* (A.G1 ⧸ A.L),
      Continuous p ∧ Function.Surjective p ∧
        ∀ h : A.H, p (QuotientGroup.mk' A.principalIntersection h) =
          QuotientGroup.mk' A.L (A.sCoordinates h) := by
  obtain ⟨e, he⟩ := A.exists_supportedChart
  have hs (h : A.H) : A.sCoordinates h = (e h).1 := by
    apply Subtype.ext
    exact (he h).1.symm
  have hc : Continuous A.sCoordinates := by
    convert continuous_fst.comp e.continuous using 1
    funext h
    exact hs h
  have hsur : Function.Surjective A.sCoordinates := by
    intro g
    refine ⟨e.symm (g, 1), ?_⟩
    rw [hs, e.apply_symm_apply]
  have hsub : A.principalIntersection ≤ A.L.comap A.sCoordinates := by
    rw [A.principalIntersection_eq_range]
    rintro h ⟨u, rfl⟩
    change A.sCoordinates (A.principalSupported u) ∈ A.diagonalS.range
    refine ⟨u, ?_⟩
    apply Subtype.ext
    rfl
  let p := QuotientGroup.map A.principalIntersection A.L A.sCoordinates hsub
  refine ⟨p, ?_, ?_, fun h => rfl⟩
  · apply (QuotientGroup.isOpenQuotientMap_mk (N := A.principalIntersection)).continuous_comp_iff.mp
    exact QuotientGroup.continuous_mk.comp hc
  · exact QuotientGroup.map_surjective_of_surjective A.principalIntersection A.L
      A.sCoordinates ((QuotientGroup.mk'_surjective A.L).comp hsur) hsub

instance compactSpace_J : CompactSpace A.J := by
  exact isCompact_iff_compactSpace.mp A.isClosed_J.isCompact

instance compactSpace_supportedPrincipalQuotient :
    CompactSpace (A.H ⧸ A.principalIntersection) := by
  obtain ⟨e, he⟩ := A.exists_supportedClassQuotientHomeomorph
  exact e.toHomeomorph.symm.compactSpace

instance compactSpace_LQuotient : CompactSpace (A.G1 ⧸ A.L) := by
  obtain ⟨p, hc, hs, hp⟩ := A.exists_supportedUnitQuotientProjection
  exact hs.compactSpace hc

end
end SArithmeticData
end DedekindZetaZeroFree
