module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffineGaussianRegularity
public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.AffinePrincipalCovariance
public import DedekindZetaZeroFree.Theta.Periods.RayUnits.LogHaarInvariance

@[expose] public section

noncomputable section

set_option maxHeartbeats 1000000
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

def affineResidueUnitMul
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : (𝓞 F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} :=
  ⟨((γ : 𝓞 F) : F) * x.val,
    (I : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule.smul_mem (γ : 𝓞 F) x.property⟩

private theorem averaging_span_unit (γ : (𝓞 F)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰
      ((Units.map (algebraMap (𝓞 F) F) γ : Fˣ) : F) = 1 := by
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨γ⁻¹, ?_⟩
  change algebraMap (𝓞 F) F (↑γ⁻¹ : 𝓞 F) * algebraMap (𝓞 F) F (γ : 𝓞 F) = 1
  rw [← map_mul, Units.inv_mul, map_one]

private theorem averaging_ray_shift (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (γ : Additive (RayCoset.U F m)) :
    principalNormalizedLogShift hF (Units.map (algebraMap (𝓞 F) F) γ.toMul.val) =
      RayCoset.rayUnitLogEmbedding F m γ := by
  apply Subtype.ext
  funext v
  change Real.log (v ((γ.toMul.val : 𝓞 F) : F)) -
    Real.log |(Algebra.norm ℚ ((γ.toMul.val : 𝓞 F) : F) : ℝ)| /
      (Module.finrank ℚ F : ℝ) = _
  rw [RayCoset.abs_norm_unit, Real.log_one, zero_div, sub_zero]
  rfl

private theorem averaging_ray_lift (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : RayCoset.U F m)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    (affineResidueUnitMul I γ.val x).val - x.val ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) := by
  have hy : algebraMap (𝓞 F) F ((γ.val : 𝓞 F) - 1) ∈
      (rayIdealFractionalIdeal F m hm : FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ γ.property.1
  have hz := FractionalIdeal.mul_mem_mul x.property hy
  convert hz using 1
  change algebraMap (𝓞 F) F (γ.val : 𝓞 F) * x.val - x.val = _
  rw [map_sub, map_one]
  ring

section Affine
variable (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (hu : 0 < u)
include hF hu

theorem affineResidueTheta_unit_mul
    (γ : (𝓞 F)ˣ) (h : RayCoset.logHyperplane F) :
    affineResidueTheta m hm I (affineResidueUnitMul I γ x) u h =
      affineResidueTheta m hm I x u
        (h + principalNormalizedLogShift hF
          (Units.map (algebraMap (𝓞 F) F) γ)) := by
  simpa [affineResidueUnitMul, Units.coe_map] using
    affineResidueTheta_principal_mul hF m hm I I
      (Units.map (algebraMap (𝓞 F) F) γ)
      (by rw [averaging_span_unit, one_mul]) x u hu h

theorem affineResidueDualTheta_unit_mul
    (γ : (𝓞 F)ˣ) (h : RayCoset.logHyperplane F) :
    affineResidueDualTheta m hm I (affineResidueUnitMul I γ x) u h =
      affineResidueDualTheta m hm I x u
        (h + principalNormalizedLogShift hF
          (Units.map (algebraMap (𝓞 F) F) γ)) := by
  simpa [affineResidueUnitMul, Units.coe_map] using
    affineResidueDualTheta_principal_mul hF m hm I I
      (Units.map (algebraMap (𝓞 F) F) γ)
      (by rw [averaging_span_unit, one_mul]) x u hu h

theorem affineResidueTheta_rayUnit_periodic
    (v : RayCoset.rayUnitLogLattice F m) (h : RayCoset.logHyperplane F) :
    affineResidueTheta m hm I x u (h + (v : RayCoset.logHyperplane F)) =
      affineResidueTheta m hm I x u h := by
  obtain ⟨γ, hγ⟩ := v.property
  rw [← hγ, ← averaging_ray_shift hF m γ,
    ← affineResidueTheta_unit_mul hF m hm I x u hu γ.toMul.val h]
  exact affineResidueTheta_congr m hm I
    (affineResidueUnitMul I γ.toMul.val x) u hu x
    (averaging_ray_lift m hm I γ.toMul x) h

theorem affineResidueDualTheta_rayUnit_periodic
    (v : RayCoset.rayUnitLogLattice F m) (h : RayCoset.logHyperplane F) :
    affineResidueDualTheta m hm I x u (h + (v : RayCoset.logHyperplane F)) =
      affineResidueDualTheta m hm I x u h := by
  obtain ⟨γ, hγ⟩ := v.property
  rw [← hγ, ← averaging_ray_shift hF m γ,
    ← affineResidueDualTheta_unit_mul hF m hm I x u hu γ.toMul.val h]
  exact affineResidueDualTheta_congr m hm I
    (affineResidueUnitMul I γ.toMul.val x) u hu x
    (averaging_ray_lift m hm I γ.toMul x) h

end Affine

private theorem averaging_quotient_lifts
    (I J : FractionalIdeal (𝓞 F)⁰ F) (x y : I.coeToSubmodule)
    (hxy : fractionalIdealQuotientMk I J x = fractionalIdealQuotientMk I J y) :
    x.val - y.val ∈ J := by
  have hz : fractionalIdealQuotientMk I J (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact (fractionalIdealQuotientMk_eq_zero_iff I J (x - y)).mp hz

section Coprime
variable (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (u : ℝ) (hu : 0 < u)
local notation "I" => rayIdealFractionalIdeal F a ha
local notation "M" => rayIdealFractionalIdeal F m hm
local notation "R" => coprimeIdealResidue F m a hm ha
local notation "X" => {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}

def coprimeIdealResidueAverage
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (u : ℝ) (hu : 0 < u) :
    coprimeIdealResidue F m a hm ha → ℂ :=
  fun q => affineResidueAverage m hm (rayIdealFractionalIdeal F a ha)
    (Classical.choose (fractionalIdealQuotientMk_surjective
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) q)) u

def coprimeIdealResidueDualAverage
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (u : ℝ) (hu : 0 < u) :
    coprimeIdealResidue F m a hm ha → ℂ :=
  fun q => affineResidueDualAverage m hm (rayIdealFractionalIdeal F a ha)
    (Classical.choose (fractionalIdealQuotientMk_surjective
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
      ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) q)) u

theorem coprimeIdealResidueAverage_mk (x : X) :
    coprimeIdealResidueAverage hF m a hm ha hcop u hu
      (fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
        ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x) =
      affineResidueAverage m hm I x u := by
  unfold coprimeIdealResidueAverage
  apply affineResidueAverage_congr m hm I _ u hu x
  apply averaging_quotient_lifts
  exact Classical.choose_spec (fractionalIdealQuotientMk_surjective
    (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F)
    (fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x))

theorem coprimeIdealResidueDualAverage_mk (x : X) :
    coprimeIdealResidueDualAverage hF m a hm ha hcop u hu
      (fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
        ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x) =
      affineResidueDualAverage m hm I x u := by
  unfold coprimeIdealResidueDualAverage
  apply affineResidueDualAverage_congr m hm I _ u hu x
  apply averaging_quotient_lifts
  exact Classical.choose_spec (fractionalIdealQuotientMk_surjective
    (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F)
    (fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x))

theorem coprimeIdealResidueAverage_eq_lifts (lift : R → X)
    (hlift : ∀ q, fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) (lift q) = q) :
    coprimeIdealResidueAverage hF m a hm ha hcop u hu =
      fun q => affineResidueAverage m hm I (lift q) u := by
  funext q
  conv_lhs => rw [← hlift q]
  exact coprimeIdealResidueAverage_mk hF m a hm ha hcop u hu (lift q)

end Coprime

end DedekindZetaZeroFree.Hecke.Theta

end
