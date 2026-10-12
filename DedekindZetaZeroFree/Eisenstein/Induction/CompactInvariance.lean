module

public import DedekindZetaZeroFree.Eisenstein.Induction.CompactOpenLevels
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactness
public import DedekindZetaZeroFree.Adeles.Quotients.PrincipalTorusCoordinateInjectivity

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.CompactSource
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

theorem arch_fixed (w : InfinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w))
    (hk : k ∈ ThetaExpansion.complexSU2Compact R w)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    LocalCovariance.arch F ζ hζ w (g * k) = LocalCovariance.arch F ζ hζ w g := by
  let J : Subgroup (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) := {
    carrier := {k | ∀ g, LocalCovariance.arch F ζ hζ w (g * k) = LocalCovariance.arch F ζ hζ w g}
    one_mem' := by intro g; rw [mul_one]
    mul_mem' := by intro k l hk hl g; rw [← mul_assoc, hl, hk]
    inv_mem' := by
      intro k hk g
      have h := hk (g * k⁻¹)
      simpa using h.symm }
  have hJ : ThetaExpansion.complexSU2Compact R w ≤ J := by
    apply (Subgroup.closure_le J).2
    rintro k ⟨a, rfl⟩ g
    exact LocalCovariance.arch_right_su2 F ζ hζ w a g
  exact hJ hk g

theorem value_right_arch (g u : RestrictedCover F ζ hζ)
    (hu : ∀ q, u (Sum.inr q) = 1)
    (hk : ∀ w, u (Sum.inl w) ∈ ThetaExpansion.complexSU2Compact R w) :
    RawSource.value F ζ hζ P C (g * u) = RawSource.value F ζ hζ P C g := by
  have ht : SourceTensor.evaluatedTensor F ζ hζ P C (g * u) =
      SourceTensor.evaluatedTensor F ζ hζ P C g := by
    apply SourceTensor.evaluatedTensor_congr
    intro q
    change (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q) * u (Sum.inr q))) = _
    rw [hu, mul_one]
  rw [RawSource.value, RawSource.value, ht]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  exact arch_fixed R w _ (hk w) _

theorem scalar_spherical (hC : C.exceptional = R.A.Sf)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ R.A.Sf)
    (k : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hk : k ∈ compact F ζ hζ (Sum.inr q)) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    RawSource.scalarValue F ζ hζ P C (g * scalarQuotient F ζ hζ (localInjection F ζ hζ (Sum.inr q) k)) =
      RawSource.scalarValue F ζ hζ P C g := by
  apply RawSource.scalarValue_right_spherical F ζ hζ P C q (by simpa [hC] using hq) k hk
  exact FrozenTorus.outside_good R.A q hq

theorem sourceLevel_le :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (SourceLevels.level F ζ hζ P C) ≤
      ThetaExpansion.fullProductCompact R := by
  rw [SourceLevels.globalLevel_eq]
  exact SourceLevels.refined_compact_le R P C

end DedekindZetaZeroFree.EisensteinReferenceSections.CompactSource

end
