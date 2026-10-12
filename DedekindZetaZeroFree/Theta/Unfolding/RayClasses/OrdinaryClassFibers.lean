module

public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.ResidueFiberAveraging
public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.PrimalResiduePartition
public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.DualLatticePacketAverages

@[expose] public section

noncomputable section

open Classical
open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

def coprimeIdealDualKernel (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (u : ℝ) (h : RayCoset.logHyperplane F)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F)}) : ℂ :=
  RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
    (((Ideal.absNorm a : ℝ) ^ (-(Module.finrank ℚ F : ℝ)⁻¹))⁻¹ •
      Theta.traceConjugation F (Theta.traceEmbedding F β.val)))

theorem rayTheta_primal_fiber_eq_weightedIdealBlock
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)
    (D : RayThetaRepresentatives F m hm) (u : ℝ) (hu : 0 < u) :
    letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
    (∑ c ∈ Finset.univ.filter (fun c : RayIdealClass F m hm =>
      rayToOrdinary F m hm c = (ClassGroup.mk F
        (rayIdealFractionalIdeal F a ha))⁻¹),
      E.ψ c * RayTheta.fδ (D.coset c) ∅ u) =
        weightedIdealBlock hF hm hmt η (rayIdealFractionalIdeal F a ha) u := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  letI : Fintype {c : RayIdealClass F m hm //
    rayToOrdinary F m hm c = (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹} :=
    Fintype.ofFinite _
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite (coprimeIdealResidue F m a hm ha)
  rw [Finset.sum_subtype (F := Fintype.ofFinite _) (p := fun c : RayIdealClass F m hm =>
    rayToOrdinary F m hm c = (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹)
    _ (by intro c; simp)]
  rw [weightedIdealBlock_eq_sum_residue_averages hF m a hm ha hcop hmt η E u hu,
    coprimeIdealResidueAverage_sum_fiber hF m a hm ha hcop hmt η E D u hu]
  obtain ⟨hd, hw, _⟩ := residueFiber_normalizers_ne_zero m hm
  simp_rw [mul_left_comm (E.ψ _) (RayCoset.rayUnitTorsionCard F m : ℂ),
    ← Finset.mul_sum]
  simp [Nat.cast_mul, ← mul_assoc, hd, hw]

theorem rayTheta_dual_fiber_eq_residuePacketIntegral
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)
    (D : RayThetaRepresentatives F m hm) (u : ℝ) (hu : 0 < u) :
    letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
    (∑ c ∈ Finset.univ.filter (fun c : RayIdealClass F m hm =>
      rayToOrdinary F m hm c = (ClassGroup.mk F
        (rayIdealFractionalIdeal F a ha))⁻¹),
      E.ψ c * RayTheta.gδDual (D.coset c) ∅ u) =
        ((residueUnitImageCard F m * RayCoset.rayUnitTorsionCard F m : ℕ) : ℂ)⁻¹ *
          (RayCoset.modulusCovolume F m : ℂ)⁻¹ *
          ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
            ∑' β : {β : F // β ∈ (Theta.traceDualIdealUnit F
              (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
                FractionalIdeal (𝓞 F)⁰ F)},
              coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β *
                coprimeIdealDualKernel m a hm ha u h β
            ∂Theta.normalizedLogHaar F := by
  classical
  letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
  letI : Fintype {c : RayIdealClass F m hm //
    rayToOrdinary F m hm c = (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹} :=
    Fintype.ofFinite _
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite (coprimeIdealResidue F m a hm ha)
  rw [Finset.sum_subtype (F := Fintype.ofFinite _) (p := fun c : RayIdealClass F m hm =>
    rayToOrdinary F m hm c = (ClassGroup.mk F (rayIdealFractionalIdeal F a ha))⁻¹)
    _ (by intro c; simp)]
  have hpacket := coprimeIdealResidue_dual_common_averages hF m a hm ha hcop hmt η E u hu
  simp_rw [affineResidueScale_rayIdealFractionalIdeal] at hpacket
  change _ = _ * _ * _
  rw [show (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      ∑' β, coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β *
        coprimeIdealDualKernel m a hm ha u h β ∂Theta.normalizedLogHaar F) =
      ∑ q, coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
        coprimeIdealResidueDualAverage hF m a hm ha hcop u hu q from hpacket.symm]
  rw [coprimeIdealResidueDualAverage_sum_fiber hF m a hm ha hcop hmt η E D u hu]
  obtain ⟨hd, hw, hc⟩ := residueFiber_normalizers_ne_zero m hm
  simp_rw [mul_left_comm (E.ψ _) ((RayCoset.rayUnitTorsionCard F m : ℂ) *
    (RayCoset.modulusCovolume F m : ℂ)), ← Finset.mul_sum]
  simp only [Nat.cast_mul]
  field_simp
  <;> ring

end DedekindZetaZeroFree.Hecke.Theta

end
