module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev P0 := KPMsRationalCompactCrossPairing.targetPolarization F ζ hζ 0

def inBorel : Subgroup (borel F ζ hζ) :=
  (P0 F ζ hζ).H.comap (ActualBorelRetraction.retraction F ζ hζ)

def actualC : Subgroup (G F ζ hζ) :=
  (inBorel F ζ hζ).map (borel F ζ hζ).subtype

 theorem c_mem_borel (c : actualC F ζ hζ) : c.val ∈ borel F ζ hζ := by
  obtain ⟨b, _, hb⟩ := c.property
  exact hb ▸ b.property

def cToBorel : actualC F ζ hζ →* borel F ζ hζ :=
  (actualC F ζ hζ).subtype.codRestrict _ (c_mem_borel F ζ hζ)

 theorem c_retraction_mem (c : actualC F ζ hζ) :
    ActualBorelRetraction.retraction F ζ hζ (cToBorel F ζ hζ c) ∈ (P0 F ζ hζ).H := by
  obtain ⟨b, hb, he⟩ := c.property
  have hh : cToBorel F ζ hζ c = b := Subtype.ext he.symm
  rw [hh]
  exact hb

def actualHCoordinate : actualC F ζ hζ →* (P0 F ζ hζ).H :=
  ((ActualBorelRetraction.retraction F ζ hζ).comp (cToBorel F ζ hζ)).codRestrict _
    (c_retraction_mem F ζ hζ)

theorem mem_actualC_iff (g : G F ζ hζ) :
    g ∈ actualC F ζ hζ ↔ ∃ (h : (P0 F ζ hζ).H) (x : Adeles F),
      g = h.val.val * N F ζ hζ x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨t, x, hx⟩ := KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ b
    have he : b = ActualBorelRetraction.torusInBorel F ζ hζ t *
        ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x) := Subtype.ext hx
    have ht : ActualBorelRetraction.retraction F ζ hζ b = t := by
      rw [he, map_mul, ActualBorelRetraction.retraction_torus,
        ActualBorelRetraction.retraction_root, mul_one]
    exact ⟨⟨t, ht ▸ hb⟩, x, hx⟩
  · rintro ⟨h, x, rfl⟩
    let b := ActualBorelRetraction.torusInBorel F ζ hζ h.val *
      ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x)
    refine ⟨b, ?_, rfl⟩
    change ActualBorelRetraction.retraction F ζ hζ b ∈ (P0 F ζ hζ).H
    simp only [b, map_mul, ActualBorelRetraction.retraction_torus,
      ActualBorelRetraction.retraction_root, mul_one]
    exact h.property

 theorem half_one : deltaHalf F ζ hζ 1 = 1 := by
  simp [deltaHalf]

 theorem half_mul (t u : E F ζ hζ) :
    deltaHalf F ζ hζ (t * u) = deltaHalf F ζ hζ t * deltaHalf F ζ hζ u := by
  simp only [deltaHalf, map_mul, Units.val_mul, NNReal.coe_mul]
  rw [Real.sqrt_mul (NNReal.coe_nonneg _), Complex.ofReal_mul]

end DedekindZetaZeroFree.KPSpatialSmoothing

end

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem half_ne_zero (t : E F ζ hζ) : deltaHalf F ζ hζ t ≠ 0 := by
  have hp : 0 < (((delta F ζ hζ t : ℝ≥0) : ℝ)) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  unfold deltaHalf
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hp))

def actualChi : actualC F ζ hζ →* ℂˣ where
  toFun c := Units.mk0
    (deltaHalf F ζ hζ (actualHCoordinate F ζ hζ c).val *
      ((P0 F ζ hζ).character (actualHCoordinate F ζ hζ c) : ℂ))
    (mul_ne_zero (half_ne_zero F ζ hζ _) (Units.ne_zero _))
  map_one' := by
    apply Units.ext
    simp only [Units.val_mk0, map_one, Subgroup.coe_one, half_one,
      Units.val_one, one_mul]
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mk0, map_mul, Subgroup.coe_mul, half_mul, Units.val_mul]
    ring

end DedekindZetaZeroFree.KPSpatialSmoothing

end
end
