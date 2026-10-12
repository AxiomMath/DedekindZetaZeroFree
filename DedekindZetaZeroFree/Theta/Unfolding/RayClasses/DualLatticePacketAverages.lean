module

public import DedekindZetaZeroFree.Theta.RayClasses.ResidueUnitAverages

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

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
local notation "J" => {β : F // β ∈
  (Theta.traceDualIdealUnit F (I * M) : FractionalIdeal (𝓞 F)⁰ F)}
include hu

theorem coprimeIdealResidue_dual_common_packet
    (lift : R → X)
    (hlift : ∀ q, fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) (lift q) = q)
    (h : RayCoset.logHyperplane F) :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
      affineResidueDualTheta m hm I (lift q) u h) =
      ∑' β : J, coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β *
        RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
          ((affineResidueScale I)⁻¹ •
            Theta.traceConjugation F (Theta.traceEmbedding F β.val))) := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  unfold affineResidueDualTheta
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun q _ =>
    (affineResidueDualTheta_summable_norm m hm I (lift q) u hu h).of_norm.mul_left
      (coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q))]
  apply tsum_congr
  intro β
  rw [coprimeIdealResiduePacket, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← hlift q, coprimeIdealResiduePhase_mk, hlift q]
  simp only [mul_assoc]

theorem coprimeIdealResidue_dual_common_averages :
    letI := coprimeIdealResidue_finite m a hm ha hcop
    letI := Fintype.ofFinite R
    (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
      coprimeIdealResidueDualAverage hF m a hm ha hcop u hu q) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        ∑' β : J, coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β *
          RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
            ((affineResidueScale I)⁻¹ •
              Theta.traceConjugation F (Theta.traceEmbedding F β.val)))
        ∂Theta.normalizedLogHaar F := by
  classical
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite R
  let lift : R → X := fun q => Classical.choose
    (fractionalIdealQuotientMk_surjective (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) q)
  have hlift : ∀ q, fractionalIdealQuotientMk (I : FractionalIdeal (𝓞 F)⁰ F)
      ((I * M) : FractionalIdeal (𝓞 F)⁰ F) (lift q) = q := fun q =>
    Classical.choose_spec (fractionalIdealQuotientMk_surjective
      (I : FractionalIdeal (𝓞 F)⁰ F) ((I * M) : FractionalIdeal (𝓞 F)⁰ F) q)
  change (∑ q : R, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
    affineResidueDualAverage m hm I (lift q) u) = _
  unfold affineResidueDualAverage
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum Finset.univ (fun q _ =>
    (affineResidueDualTheta_integrableOn m hm I (lift q) u hu).const_mul
      (coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h =>
    coprimeIdealResidue_dual_common_packet hF m a hm ha hcop hmt η E u hu lift hlift h)

end Coprime

end DedekindZetaZeroFree.Hecke.Theta

end
