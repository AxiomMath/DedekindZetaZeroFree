module

public import DedekindZetaZeroFree.Theta.Unfolding.RayClasses.OrdinaryClassFibers
public import DedekindZetaZeroFree.CharacterSums.Gauss.RayClasses.PrimitiveTracePacket
public import DedekindZetaZeroFree.Theta.RayClasses.WeightedIdealBlockClassInvariance

@[expose] public section

/-
https://github.com/LeanPool/lean-pool
Revision: 68aa6ee63d20ad76bcc15f595adfc72949991f06.
-/

noncomputable section
open Classical
open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

private theorem dual_Q_smul (q : NumberField.InfinitePlace F → ℝ)
    (c : ℝ) (x : NumberField.mixedEmbedding.euclidean.mixedSpace F) :
    RayParity.Q F q (c • x) = RayParity.Q F (fun v => c * q v) x := by
  apply (Theta.traceToMixed F).injective
  simp only [RayParity.Q, ContinuousLinearEquiv.apply_symm_apply, map_smul]
  ext v <;> simp [NumberField.mixedEmbedding.mixedSpaceOfRealSpace] <;> ring

private theorem dual_gaussian_conjugation
    (q : NumberField.InfinitePlace F → ℝ) (hq : ∀ v, q v ≠ 0)
    (x : NumberField.mixedEmbedding.euclidean.mixedSpace F) :
    RayParity.gδ F ∅ (RayParity.Q F q (Theta.traceConjugation F x)) =
      RayParity.gδ F ∅ (RayParity.Q F q x) := by
  simp only [RayParity.gδ, Finset.prod_empty, one_mul]
  rw [RayParity.Q_eq_traceRadialScale F q hq,
    RayParity.Q_eq_traceRadialScale F q hq,
    ← Theta.traceConjugation_traceRadialScale]
  simp only [Theta.latticeGaussian, LinearIsometryEquiv.norm_map]

private theorem dual_norm (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥) :
    (FractionalIdeal.absNorm (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F) : ℝ) =
      (conductorNorm F m * (Ideal.absNorm a : ℝ))⁻¹ := by
  rw [Theta.absNorm_traceDualIdealUnit, Theta.absNorm_traceDual_one]
  simp only [Units.val_mul, map_mul, rayIdealFractionalIdeal_coe,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  unfold conductorNorm
  ring

private theorem dual_radial_scale (A N u r : ℝ) (hA : 0 < A)
    (hN : 0 < N) (hu : 0 < u) :
    u ^ r * (N ^ (-r))⁻¹ = (u / A) ^ r * ((A * N)⁻¹) ^ (-r) := by
  rw [Real.div_rpow hu.le hA.le, Real.inv_rpow (mul_pos hA hN).le,
    Real.rpow_neg (mul_pos hA hN).le, inv_inv,
    Real.mul_rpow hA.le hN.le, Real.rpow_neg hN.le, inv_inv]
  field_simp

theorem coprimeIdealDualKernel_eq_conductorGaussian
    (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (u : ℝ) (hu : 0 < u)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F)})
    (h : RayCoset.logHyperplane F) :
    RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
      (((Ideal.absNorm a : ℝ) ^ (-(Module.finrank ℚ F : ℝ)⁻¹))⁻¹ •
        Theta.traceConjugation F (Theta.traceEmbedding F β.val))) =
    RayParity.gδ F ∅ (RayParity.Q F
      (RayTheta.q F (u / conductorNorm F m) (-h))
      ((FractionalIdeal.absNorm (Theta.traceDualIdealUnit F
        (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
        (-1 / (Module.finrank ℚ F : ℝ)) • Theta.traceEmbedding F β.val)) := by
  have hn : 0 < (Ideal.absNorm a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ha)
  have hA := conductorNorm_pos hm
  have hq : ∀ v, RayTheta.q F u (-h) v ≠ 0 := by
    intro v
    exact (mul_pos (Real.rpow_pos_of_pos hu _) (Real.exp_pos _)).ne'
  rw [← LinearIsometryEquiv.map_smul]
  rw [dual_gaussian_conjugation _ hq]
  rw [dual_Q_smul, dual_Q_smul, dual_norm m a hm ha]
  congr 2
  funext v
  simp only [RayTheta.q]
  have hs := dual_radial_scale (conductorNorm F m) (Ideal.absNorm a : ℝ) u
    (Module.finrank ℚ F : ℝ)⁻¹ hA hn hu
  simp only [neg_div, one_div] at *
  calc
    _ = (u ^ (Module.finrank ℚ F : ℝ)⁻¹ *
      ((Ideal.absNorm a : ℝ) ^ (-(Module.finrank ℚ F : ℝ)⁻¹))⁻¹) *
        Real.exp ((-h).val v) := by ring
    _ = _ := by rw [hs]; ring

theorem conductorScale_div_modulusCovolume
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    conductorScale F m / RayCoset.modulusCovolume F m =
      1 / Real.sqrt (Ideal.absNorm m : ℝ) := by
  have hn : 0 < (Ideal.absNorm m : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hm)
  have hd : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  simp only [conductorScale, conductorNorm, RayCoset.modulusCovolume,
    Theta.covolume_traceIdealLattice, Units.val_one, map_one, Rat.cast_one, one_mul]
  rw [Real.sqrt_mul (le_of_lt hd)]
  have hs := Real.sq_sqrt (le_of_lt hn)
  have hspos := Real.sqrt_pos.mpr hn
  have hdpos := Real.sqrt_pos.mpr hd
  field_simp
  nlinarith

theorem rayTheta_dual_fiber_eq_conjugateWeightedIdealBlock
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m) (hprim : η.IsPrimitive) :
    letI : Finite (𝓞 F ⧸ m) := m.finiteQuotientOfFreeOfNeBot hm
    letI : Fintype (𝓞 F ⧸ m) := Fintype.ofFinite _
    letI := rayTraceQuotientModule m hm
    ∀ (β₀ : ((m : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
        codifferentFractionalIdeal F).coeToSubmodule)
      (hgen : Function.Bijective (LinearMap.toSpanSingleton (𝓞 F ⧸ m)
        (rayTraceQuotient m)
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀)))
      (b : Ideal (𝓞 F)) (hb : b ≠ ⊥) (hbcop : m ⊔ b = ⊤)
      (hbimage : (b : FractionalIdeal (𝓞 F)⁰ F) =
        FractionalIdeal.spanSingleton (𝓞 F)⁰ (β₀ : F) *
          (m : FractionalIdeal (𝓞 F)⁰ F) * (codifferentFractionalIdeal F)⁻¹)
      (e₀ : AddChar (𝓞 F ⧸ m) ℂ)
      (he₀ : e₀ = rayTraceGeneratorChar m hm
        (fractionalIdealQuotientMk _ (codifferentFractionalIdeal F) β₀))
      (τ : ℂ)
      (hτ : τ = finiteRingGaussSum e₀
        ((Units.coeHom ℂ).comp (residueRayCharacter hF hm hmt η)))
      (a : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hcop : a ⊔ m = ⊤)
      (E : RayCharacterData F m hm η)
      (D : RayThetaRepresentatives F m hm) (u : ℝ) (hu : 0 < u),
      letI : Fintype (RayIdealClass F m hm) := Fintype.ofFinite _
      (∑ c ∈ Finset.univ.filter (fun c : RayIdealClass F m hm =>
        rayToOrdinary F m hm c = (ClassGroup.mk F
          (rayIdealFractionalIdeal F a ha))⁻¹),
        E.ψ c * RayTheta.gδDual (D.coset c) ∅ u) =
        (τ * η b / (RayCoset.modulusCovolume F m : ℂ)) *
          weightedIdealBlock hF hm hmt (conjugateRayCharacter η)
            (Theta.traceDualIdealUnit F
              (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm))
            (u / conductorNorm F m) := by
  intro β₀ hgen b hb hbcop hbimage e₀ he₀ τ hτ a ha hcop E D u hu
  let J := Theta.traceDualIdealUnit F
    (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm)
  have hv : 0 < u / conductorNorm F m := div_pos hu (conductorNorm_pos hm)
  rw [rayTheta_dual_fiber_eq_residuePacketIntegral hF m a hm ha hcop hmt η E D u hu]
  have hpacket := coprimeIdealResiduePacket_eq_gauss_conjugate_coefficient
    hF m hm hmt η hprim β₀ hgen b hb hbcop hbimage e₀ he₀ τ hτ a ha hcop E
  have hkernel := coprimeIdealDualKernel_eq_conductorGaussian
    hF m a hm ha hcop hmt u hu
  have hsum : ∀ h : RayCoset.logHyperplane F,
      (∑' β : {β : F // β ∈ (J : FractionalIdeal (𝓞 F)⁰ F)},
        coprimeIdealResiduePacket hF m a hm ha hcop hmt η E β *
          coprimeIdealDualKernel m a hm ha u h β) =
      (τ * η b) * ∑' β : {β : F // β ∈ (J : FractionalIdeal (𝓞 F)⁰ F)},
        conjugateRayCharacter η (integralElementIdeal J β) *
          RayParity.gδ F ∅ (RayParity.Q F
            (RayTheta.q F (u / conductorNorm F m) (-h))
            ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
              (-1 / (Module.finrank ℚ F : ℝ)) • Theta.traceEmbedding F β.val)) := by
    intro h
    rw [← tsum_mul_left]
    apply tsum_congr
    intro β
    rw [hpacket β]
    unfold coprimeIdealDualKernel
    rw [hkernel β h, conjugateRayCharacter_apply]
    ring
  dsimp only [J] at hsum
  simp_rw [hsum]
  rw [MeasureTheory.integral_const_mul]
  have hneg : weightedIdealBlockNeg hF hm hmt (conjugateRayCharacter η) J
      (u / conductorNorm F m) =
      weightedIdealBlock hF hm hmt (conjugateRayCharacter η) J
        (u / conductorNorm F m) :=
    weightedIdealBlockNeg_eq_weightedIdealBlock hF hm hmt
      (conjugateRayCharacter η) J (u / conductorNorm F m) hv
  rw [← hneg, weightedIdealBlockNeg, if_pos hv]
  dsimp only [J]
  ring

end DedekindZetaZeroFree.Hecke.Theta

end
