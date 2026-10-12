module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPActualReflectionData.CanonicalPlusReferences
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalGoodSphericalImage
variable {K : Type*} [Field K] [CharZero K] [ValuativeRel K]
 [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
private theorem value_one_fixed (B : LocalBorelData (K := K) (G := G) T)
 (P : Polarization T) (I : IwasawaData B)
 (f : sectionSpace B P .plus 0)
 (hf : f ∈ fixedSubmodule (IPlus B P) I.compact.toOpenSubgroup) :
 f.val 1 ∈ fixedSubmodule (tau P) (compactTorus B I) := by
 intro j
 have hj : (B.torus j.val : G) ∈ I.compact.toOpenSubgroup := j.property
 have hfix := congrArg (fun u : sectionSpace B P .plus 0 => u.val 1)
   (hf ⟨B.torus j.val, hj⟩)
 have hcov := f.property.1 (B.torus j.val) 1
 have hs : inducingScalar B 0 (B.torus j.val) = 1 := by
   simp [inducingScalar, deltaHalf, normPower, I.intersection_norm _ hj]
 change f.val (1 * B.torus j.val) = f.val 1 at hfix
 rw [mul_one] at hcov
 rw [one_mul] at hfix
 change f.val (B.torus j.val) =
   inducingScalar B 0 (B.torus j.val) • tau P (B.retract (B.torus j.val)) (f.val 1) at hcov
 rw [hs, one_smul] at hcov
 rw [B.retract_torus] at hcov
 exact hcov.symm.trans hfix

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12

theorem normalized_canonical_section (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
 (hq : q ∉ C.exceptional) :
 ∃ f : sectionSpace (C.canonical q).borel (C.polarization q) .plus 0,
   f ∈ fixedSubmodule (IPlus (C.canonical q).borel (C.polarization q))
     (C.canonical q).iwasawa.compact.toOpenSubgroup ∧
   f.val 1 = KPGlobalTorusFiniteStages.localReference F ζ hζ P C q := by
 obtain ⟨f, hf, _⟩ := normalized_plus_spherical_vector (C.canonical q).borel
   (C.polarization q) (C.canonical q).iwasawa (C.unramified q hq)
 refine ⟨f, hf.1, ?_⟩
 exact (KPGlobalTorusFiniteStages.referenceGoodSpherical F ζ hζ P C q hq).2.2
   (f.val 1) (value_one_fixed _ _ _ f hf.1) hf.2

def sectionCongr (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
 (S T : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
 (h : S = T) :
 sectionSpace S.borel S.polarization .plus 0 ≃ₗ[ℂ]
 sectionSpace T.borel T.polarization .plus 0 := by
 cases h
 exact LinearEquiv.refl ℂ _

end DedekindZetaZeroFree.KPActualReflectionData.CanonicalPlusReferences

end
