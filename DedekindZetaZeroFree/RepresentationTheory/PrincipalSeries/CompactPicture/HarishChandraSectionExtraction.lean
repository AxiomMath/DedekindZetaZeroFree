module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScatteringChamberAndSmoothTorusFibers
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarishChandraCompactOrbits

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCExtraction
open KPLiteralRaw KPLiteralTensor KPLiteralScalarHCCompactOrbit
open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar → scalar
open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar_injective → scalar_injective
open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar_borelP_kFinite_iff → scalar_borelP_kFinite_iff
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance (P : KPGlobalTorusBorelTwistCompatibility.Polarization F ζ hζ) :
    TopologicalSpace (KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P) :=
  KPGlobalTorusBorelTwistCompatibility.inducedTopology F ζ hζ P
variable (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
local notation "D" => KPLiteralChamber.literalIwasawa F ζ hζ K hK
local notation "R0" => KPGlobalTorusBorelTwistCompatibility.twist F ζ hζ
  (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) 0

def zeroHCSection (f : Flat F ζ hζ K) :
    KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ R0 :=
  (KPLiteralChamber.literal_zero_induced_lift F ζ hζ K hK f).choose

theorem zeroHCSection_fiber (f : Flat F ζ hζ K) (g : G F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ((zeroHCSection F ζ hζ K hK f).val.val g).val.val t =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f.val 0 (t.val * g) :=
  (KPLiteralChamber.literal_zero_induced_lift F ζ hζ K hK f).choose_spec g t

theorem zeroHCSection_scalar (f : Flat F ζ hζ K) :
    scalar F ζ hζ R0 (zeroHCSection F ζ hζ K hK f) = f.val 0 := by
  funext g
  rw [scalar, LinearMap.comp_apply]
  change ((zeroHCSection F ζ hζ K hK f).val.val g).val.val 1 = _
  rw [zeroHCSection_fiber]
  simp [KPGlobalTorusFunctionData.deltaHalf]

def productHCSection
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K) :
    KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.twist F ζ hζ
        (KPGlobalTorusBorelTwistCompatibility.productModel F ζ hζ C) 0) :=
  KPGlobalTorusBorelTwistCompatibility.borelQ F ζ hζ C 0 (zeroHCSection F ζ hζ K hK f)

theorem productHCSection_recovers
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K) :
    KPGlobalTorusBorelTwistCompatibility.borelP F ζ hζ C 0
      (productHCSection F ζ hζ K hK C f) = zeroHCSection F ζ hζ K hK f :=
  KPGlobalTorusBorelTwistCompatibility.borelP_borelQ F ζ hζ C 0 _

def productHCScalar (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ)
    (f : Flat F ζ hζ K) : Functions F ζ hζ :=
  scalar F ζ hζ _ (productHCSection F ζ hζ K hK C f)

theorem productHCScalar_kFinite
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K) :
    KFinite F ζ hζ K (productHCScalar F ζ hζ K hK C f) := by
  apply (scalar_borelP_kFinite_iff F ζ hζ C 0 K (productHCSection F ζ hζ K hK C f)).mpr
  rw [productHCSection_recovers, zeroHCSection_scalar]
  exact f.property.2.2

theorem productHCScalar_family_orbit_finite {Y : Type*}
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)
    (anchor : Y → G F ζ hζ) :
    Module.Finite ℂ (Submodule.span ℂ (Set.range (fun k =>
      scalarFamilyTranslate F k (archRestriction F ζ hζ anchor
        (productHCScalar F ζ hζ K hK C f))))) :=
  archRestriction_orbit_finite F ζ hζ K hK _
    (productHCScalar_kFinite F ζ hζ K hK C f) anchor
set_option maxHeartbeats 8000000 in

theorem productHCSection_right_level
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g a, a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        (productHCSection F ζ hζ K hK C f).val.val (g * a) =
          (productHCSection F ζ hζ K hK C f).val.val g := by
  obtain ⟨J, hJ⟩ := (f.property.1 0).1.2.2
  refine ⟨J, ?_⟩
  intro g a ha
  have hz : (zeroHCSection F ζ hζ K hK f).val.val (g * a) =
      (zeroHCSection F ζ hζ K hK f).val.val g := by
    apply Subtype.ext
    apply Subtype.ext
    funext t
    rw [zeroHCSection_fiber, zeroHCSection_fiber, ← mul_assoc, hJ _ a ha]
  change (KPGlobalTorusBorelTwistCompatibility.borelQ F ζ hζ C 0
    (zeroHCSection F ζ hζ K hK f)).val.val (g * a) =
    (KPGlobalTorusBorelTwistCompatibility.borelQ F ζ hζ C 0
      (zeroHCSection F ζ hζ K hK f)).val.val g
  rw [KPGlobalTorusBorelTwistCompatibility.borelQ_fiberwise,
    KPGlobalTorusBorelTwistCompatibility.borelQ_fiberwise, hz]

theorem productHCScalar_right_level
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g a, a ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        productHCScalar F ζ hζ K hK C f (g * a) = productHCScalar F ζ hζ K hK C f g := by
  obtain ⟨J, hJ⟩ := productHCSection_right_level F ζ hζ K hK C f
  exact ⟨J, fun g a ha => congrArg (fun u => u.val.val 1) (hJ g a ha)⟩

open _root_.DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility renaming induced_smooth → induced_smooth

theorem productHCScalar_left_chart
    (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)
    (g : G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => productHCScalar F ζ hζ K hK C f
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :=
  induced_smooth F ζ hζ _ (productHCSection F ζ hζ K hK C f) g
end DedekindZetaZeroFree.KPLiteralScalarHCExtraction

end
