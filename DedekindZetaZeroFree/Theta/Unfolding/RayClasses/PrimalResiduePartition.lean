module

public import DedekindZetaZeroFree.Theta.RayClasses.ResidueUnitAverages

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

 def residueLiftEquiv
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hJI : J ≤ I)
    (lift : fractionalIdealQuotient I J → I.coeToSubmodule)
    (hlift : ∀ q, fractionalIdealQuotientMk I J (lift q) = q) :
    (fractionalIdealQuotient I J × J.coeToSubmodule) ≃ I.coeToSubmodule := by
  let f : fractionalIdealQuotient I J × J.coeToSubmodule → I.coeToSubmodule :=
    fun z => ⟨(lift z.1).val + z.2.val, I.coeToSubmodule.add_mem (lift z.1).property (hJI z.2.property)⟩
  have hf : ∀ z, fractionalIdealQuotientMk I J (f z) = z.1 := by
    intro z
    let l : I.coeToSubmodule := ⟨z.2.val, hJI z.2.property⟩
    change fractionalIdealQuotientMk I J (lift z.1 + l) = z.1
    rw [map_add, hlift, (fractionalIdealQuotientMk_eq_zero_iff I J l).mpr z.2.property,
      add_zero]
  exact Equiv.ofBijective f ⟨by
    intro z w h
    have hq : z.1 = w.1 := (hf z).symm.trans ((congrArg (fractionalIdealQuotientMk I J) h).trans (hf w))
    apply Prod.ext hq
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    change (lift z.1).val + z.2.val = (lift w.1).val + w.2.val at hv
    rw [hq] at hv
    exact add_left_cancel hv,
    by
    intro x
    let q := fractionalIdealQuotientMk I J x
    have hd : x.val - (lift q).val ∈ J := by
      have hh : fractionalIdealQuotientMk I J (x - lift q) = 0 := by
        rw [map_sub, hlift, sub_self]
      exact (fractionalIdealQuotientMk_eq_zero_iff I J (x - lift q)).mp hh
    refine ⟨(q, ⟨x.val - (lift q).val, hd⟩), ?_⟩
    apply Subtype.ext
    change (lift q).val + (x.val - (lift q).val) = x.val
    abel⟩

private theorem residueLiftEquiv_mk
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hJI : J ≤ I)
    (lift : fractionalIdealQuotient I J → I.coeToSubmodule)
    (hlift : ∀ q, fractionalIdealQuotientMk I J (lift q) = q)
    (z : fractionalIdealQuotient I J × J.coeToSubmodule) :
    fractionalIdealQuotientMk I J (residueLiftEquiv I J hJI lift hlift z) = z.1 := by
  let l : I.coeToSubmodule := ⟨z.2.val, hJI z.2.property⟩
  change fractionalIdealQuotientMk I J (lift z.1 + l) = z.1
  rw [map_add, hlift, (fractionalIdealQuotientMk_eq_zero_iff I J l).mpr z.2.property,
    add_zero]

private theorem tsum_residue_partition
    (I J : FractionalIdeal (𝓞 F)⁰ F) (hJI : J ≤ I)
    [Fintype (fractionalIdealQuotient I J)]
    (lift : fractionalIdealQuotient I J → I.coeToSubmodule)
    (hlift : ∀ q, fractionalIdealQuotientMk I J (lift q) = q)
    (κ : fractionalIdealQuotient I J → ℂ) (g : F → ℂ)
    (hs : Summable (fun x : I.coeToSubmodule =>
      κ (fractionalIdealQuotientMk I J x) * g x.val)) :
    (∑' x : I.coeToSubmodule, κ (fractionalIdealQuotientMk I J x) * g x.val) =
    ∑ q : fractionalIdealQuotient I J, κ q *
      ∑' l : J.coeToSubmodule, g ((lift q).val + l.val) := by
  let e := residueLiftEquiv I J hJI lift hlift
  have he : (fun z : fractionalIdealQuotient I J × J.coeToSubmodule =>
      κ (fractionalIdealQuotientMk I J (e z)) * g (e z).val) =
      (fun z => κ z.1 * g ((lift z.1).val + z.2.val)) := by
    funext z
    rw [residueLiftEquiv_mk]
    rfl
  have hp := e.summable_iff.mpr hs
  change Summable (fun z => κ (fractionalIdealQuotientMk I J (e z)) * g (e z).val) at hp
  rw [he] at hp
  calc
    _ = ∑' z : fractionalIdealQuotient I J × J.coeToSubmodule,
        κ (fractionalIdealQuotientMk I J (e z)) * g (e z).val :=
      (e.tsum_eq _).symm
    _ = ∑' z : fractionalIdealQuotient I J × J.coeToSubmodule,
        κ z.1 * g ((lift z.1).val + z.2.val) := by
      apply tsum_congr
      intro z
      rw [residueLiftEquiv_mk]
      rfl
    _ = ∑' q : fractionalIdealQuotient I J, ∑' l : J.coeToSubmodule,
        κ q * g ((lift q).val + l.val) := hp.tsum_prod
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro q hq
      exact tsum_mul_left

section Coprime
variable (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η) (u : ℝ) (hu : 0 < u)
local notation "I" => rayIdealFractionalIdeal F a ha
local notation "M" => rayIdealFractionalIdeal F m hm
local notation "R" => coprimeIdealResidue F m a hm ha
local notation "X" => {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}
include hu

set_option maxHeartbeats 1000000 in

theorem weightedIdealTheta_eq_sum_residue_lifts
    (lift : R → X)
    (hlift : ∀ q, fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) (lift q) = q)
    (h : RayCoset.logHyperplane F) :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    (∑' x : X, η (integralElementIdeal I x) *
      RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
        (affineResidueScale I • Theta.traceEmbedding F x.val))) =
      ∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
        affineResidueTheta m hm I (lift q) u h := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  have hJI : ((I * M) : FractionalIdeal (𝓞 F)⁰ F) ≤
      (I : FractionalIdeal (𝓞 F)⁰ F) := by
    change (a : FractionalIdeal (𝓞 F)⁰ F) * (m : FractionalIdeal (𝓞 F)⁰ F) ≤ _
    rw [← FractionalIdeal.coeIdeal_mul]
    exact (FractionalIdeal.coeIdeal_le_coeIdeal F).mpr Ideal.mul_le_left
  let κ := coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E
  let g := fun x : F => RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
    (affineResidueScale I • Theta.traceEmbedding F x))
  have hc (x : X) : κ (fractionalIdealQuotientMk
      (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x) =
      η (integralElementIdeal I x) :=
    coprimeIdealResidueCoefficient_mk hF m a hm ha hcop hmt η E x
  have hs : Summable (fun x : (I : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule =>
      κ (fractionalIdealQuotientMk _ _ x) * g x.val) := by
    have hw := (weightedIdealBlock_summable_norm hF m hm hmt η I u hu h).of_norm
    convert hw using 1
    funext x
    rw [hc]
    simp only [g, affineResidueScale, neg_div, one_div]
  calc
    _ = ∑' x : X, κ (fractionalIdealQuotientMk
        (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F) x) * g x.val := by
      apply tsum_congr
      intro x
      rw [hc]
    _ = _ := tsum_residue_partition _ _ hJI lift hlift κ g hs

theorem weightedIdealBlock_eq_sum_residue_averages :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    weightedIdealBlock hF hm hmt η I u =
      ((residueUnitImageCard F m * RayCoset.rayUnitTorsionCard F m : ℕ) : ℂ)⁻¹ *
        ∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
          coprimeIdealResidueAverage hF m a hm ha hcop u hu q := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  let lift : R → X := fun q => (fractionalIdealQuotientMk_surjective
    (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F) q).choose
  have hlift : ∀ q, fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) (lift q) = q := by
    intro q
    exact (fractionalIdealQuotientMk_surjective _ _ q).choose_spec
  rw [weightedIdealBlock, if_pos hu]
  apply congrArg (fun z : ℂ =>
    ((residueUnitImageCard F m * RayCoset.rayUnitTorsionCard F m : ℕ) : ℂ)⁻¹ * z)
  have ht := weightedIdealTheta_eq_sum_residue_lifts hF m a hm ha hcop hmt η E u hu lift hlift
  have hav := coprimeIdealResidueAverage_eq_lifts hF m a hm ha hcop u hu lift hlift
  calc
    _ = ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        ∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
          affineResidueTheta m hm I (lift q) u h ∂Theta.normalizedLogHaar F := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with h
      simpa only [affineResidueScale, neg_div, one_div] using ht h
    _ = ∑ q : R, ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
          affineResidueTheta m hm I (lift q) u h ∂Theta.normalizedLogHaar F := by
      apply MeasureTheory.integral_finset_sum
      intro q hq
      exact (affineResidueTheta_integrableOn m hm I (lift q) u hu).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [MeasureTheory.integral_const_mul, hav]
      rfl

end Coprime

end DedekindZetaZeroFree.Hecke.Theta

end
