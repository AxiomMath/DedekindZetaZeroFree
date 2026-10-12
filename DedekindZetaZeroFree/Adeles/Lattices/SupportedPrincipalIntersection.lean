module

public import DedekindZetaZeroFree.Adeles.Quotients.SupportedNormOneCoordinates

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

def principalNormOne (_A : SArithmeticData F) : Fˣ →* IdeleGroup.normOneSubgroup (K := F) :=
  (IdeleGroup.principalIdele F).codRestrict _ fun x =>
    IdeleGroup.absoluteNorm_principalIdele x

theorem principal_mem_supported_iff (x : Fˣ) :
    IdeleGroup.principalIdele F x ∈ IdeleGroup.supportedAt (K := F)
      (A.Sf : Set (HeightOneSpectrum (𝓞 F))) ↔ x ∈ A.U := by
  rw [IdeleGroup.mem_supportedAt_iff]
  change (∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → _) ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ A.Sf → v.valuation F (x : F) = 1
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1 ↔ _
  rw [v.algebraMap_adicCompletion (K := F), Function.comp_apply,
    Algebra.algebraMap_self_apply, v.valuedAdicCompletion_eq_valuation']

theorem principal_mem_H_iff (x : Fˣ) :
    A.principalNormOne x ∈ A.H ↔ x ∈ A.U := by
  exact A.principal_mem_supported_iff x

def principalSupported : A.U →* A.H :=
  (A.principalNormOne.comp A.U.subtype).codRestrict _ fun u =>
    (A.principal_mem_H_iff u.val).2 u.prop

theorem diagonal_norm_one (u : A.U) : A.norm (A.diagonal u.val) = 1 := by
  have h := A.sCoordinatesRaw_norm (IdeleGroup.principalIdele F u.val)
    ((A.principal_mem_supported_iff u.val).2 u.prop)
  change A.norm (A.diagonal u.val) = _ at h
  rw [IdeleGroup.absoluteNorm_principalIdele] at h
  simpa only [Units.val_one, NNReal.coe_one, inv_one] using h

def diagonalS : A.U →* A.G1 :=
  (A.diagonal.comp A.U.subtype).codRestrict _ fun u => A.diagonal_norm_one u

def exteriorDiagonal : A.U →* A.C where
  toFun u := A.exteriorCoordinates (A.principalSupported u)
  map_one' := by
    ext v
    simp [exteriorCoordinates]
  map_mul' u v := by
    ext w
    simp [exteriorCoordinates]

def unitGraph : A.U →* (A.G1 × A.C) := A.diagonalS.prod A.exteriorDiagonal

def Lambda : Subgroup (A.G1 × A.C) := A.unitGraph.range

def L : Subgroup A.G1 := A.diagonalS.range

theorem Gamma1_eq_sixthPower_image :
    A.Gamma1 = A.unitSixthPowers.map A.diagonalS := by
  ext g
  change g.val ∈ (A.U.map (powMonoidHom 6)).map A.diagonal ↔
    g ∈ A.unitSixthPowers.map A.diagonalS
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨u, hu, hux⟩, hxg⟩
    let u' : A.U := ⟨u, hu⟩
    refine ⟨u' ^ 6, ?_, ?_⟩
    · exact ⟨u', rfl⟩
    · apply Subtype.ext
      change A.diagonal (u ^ 6) = g.val
      exact (congrArg A.diagonal hux).trans hxg
  · rintro ⟨u, ⟨v, hv⟩, hug⟩
    refine ⟨u.val, ⟨v.val, v.prop, ?_⟩, ?_⟩
    · exact congrArg Subtype.val hv
    · exact congrArg Subtype.val hug

theorem Gamma1_le_L : A.Gamma1 ≤ A.L := by
  rw [A.Gamma1_eq_sixthPower_image]
  exact Subgroup.map_le_range _ _

def principalIntersection : Subgroup A.H :=
  (IdeleGroup.principalSubgroup F).comap
    ((IdeleGroup.normOneSubgroup (K := F)).subtype.comp A.H.subtype)

theorem principalIntersection_eq_range :
    A.principalIntersection = A.principalSupported.range := by
  ext a
  change a.val.val ∈ (IdeleGroup.principalIdele F).range ↔
    a ∈ A.principalSupported.range
  constructor
  · rintro ⟨x, hx⟩
    have hxH : A.principalNormOne x ∈ A.H := by
      change IdeleGroup.principalIdele F x ∈ IdeleGroup.supportedAt (K := F) _
      rw [hx]
      exact a.prop
    refine ⟨⟨x, (A.principal_mem_H_iff x).1 hxH⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hx
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩

theorem supportedChart_principal
    (e : A.H ≃ₜ* (A.G1 × A.C))
    (he : ∀ a : A.H, (e a).1.val = A.sCoordinatesRaw a.1.1 ∧
      (e a).2 = A.exteriorCoordinates a) (u : A.U) :
    e (A.principalSupported u) = A.unitGraph u := by
  apply Prod.ext
  · apply Subtype.ext
    exact (he (A.principalSupported u)).1
  · exact (he (A.principalSupported u)).2

theorem principalIntersection_map_supportedChart
    (e : A.H ≃ₜ* (A.G1 × A.C))
    (he : ∀ a : A.H, (e a).1.val = A.sCoordinatesRaw a.1.1 ∧
      (e a).2 = A.exteriorCoordinates a) :
    A.principalIntersection.map e.toMonoidHom = A.Lambda := by
  rw [A.principalIntersection_eq_range]
  change A.principalSupported.range.map e.toMonoidHom = A.unitGraph.range
  rw [MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro u
  exact A.supportedChart_principal e he u

end
end SArithmeticData
end DedekindZetaZeroFree
