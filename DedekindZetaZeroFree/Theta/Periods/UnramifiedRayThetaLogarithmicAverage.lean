module

public import DedekindZetaZeroFree.Theta.Periods.CenteredLogarithmicIdealAverages
public import DedekindZetaZeroFree.Theta.Profiles.RayThetaKernelsAndZeroModes

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.Hecke.Theta

variable (F : Type) [Field F] [NumberField F]

private theorem discrSqrt_pos : 0 < Real.sqrt |(NumberField.discr F : ℝ)| := by
  apply Real.sqrt_pos.mpr
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)

 def idealNormalizedEquiv (D : RayCoset.Data F) (hD : D.m = ⊤) :
    D.a ≃ RayCoset.normalizedLattice D :=
  Equiv.ofBijective
    (fun x => ⟨RayCoset.normalizedEmbedding D x,
      Submodule.mem_map.mpr ⟨x, by simpa [hD] using x.property, rfl⟩⟩)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        have he : DedekindZetaZeroFree.AbelianQuotient.Theta.traceEmbedding F (x.val : F) =
            DedekindZetaZeroFree.AbelianQuotient.Theta.traceEmbedding F (y.val : F) :=
          (smul_right_injective _ (RayCoset.normalizationScale_pos D).ne').eq_iff.mp
            (congrArg Subtype.val h)
        apply NumberField.RingOfIntegers.coe_injective
        apply NumberField.mixedEmbedding_injective F
        simpa [DedekindZetaZeroFree.AbelianQuotient.Theta.traceEmbedding] using
          congrArg (DedekindZetaZeroFree.AbelianQuotient.Theta.traceToMixed F) he
      · intro x
        obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp x.property
        refine ⟨⟨y, by simpa [hD] using hy⟩, ?_⟩
        exact Subtype.ext he)

 def idealFractionalEquiv (D : RayCoset.Data F) :
    D.a ≃ ↥((rayIdealFractionalIdeal F D.a D.ideal_ne_bot :
      FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
  Equiv.ofBijective
    (fun x => ⟨(x.val : F), by
      change (x.val : F) ∈ (rayIdealFractionalIdeal F D.a D.ideal_ne_bot : FractionalIdeal (𝓞 F)⁰ F)
      rw [rayIdealFractionalIdeal_coe]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨x.val, x.property, rfl⟩⟩)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply NumberField.RingOfIntegers.coe_injective
        exact congrArg (fun z : ↥((rayIdealFractionalIdeal F D.a D.ideal_ne_bot :
          FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) => z.val) h
      · intro x
        have hx : x.val ∈ (rayIdealFractionalIdeal F D.a D.ideal_ne_bot : FractionalIdeal (𝓞 F)⁰ F) := x.property
        simp only [rayIdealFractionalIdeal_coe] at hx
        obtain ⟨y, hy, he⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
        exact ⟨⟨y, hy⟩, Subtype.ext he⟩)

private theorem centeredLogShape_eq (D : RayCoset.Data F)
    (t : ℝ) (ht : 0 < t) (h : RayCoset.logHyperplane F) :
    centeredLogShape F (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) t h =
      RayCoset.normalizationScale D •
        RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h := by
  have ha : 0 < (Ideal.absNorm D.a : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)
  have hd := discrSqrt_pos F
  funext v
  simp only [centeredLogShape, DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaCovolume,
    rayIdealFractionalIdeal_coe, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast,
    Pi.smul_apply, smul_eq_mul, RayTheta.q, RayCoset.normalizationScale]
  rw [Real.div_rpow ht.le (mul_pos ha hd).le, Real.mul_rpow ha.le hd.le,
    Real.rpow_neg ha.le, Real.div_rpow ht.le hd.le]
  ring

private theorem Q_smul_shape (q : NumberField.InfinitePlace F → ℝ) (r : ℝ)
    (x : euclidean.mixedSpace F) :
    RayParity.Q F q (r • x) = RayParity.Q F (r • q) x := by
  simp only [RayParity.Q, map_smul, smul_mul_assoc, mul_smul_comm]

private theorem topPrimal_integrand (D : RayCoset.Data F) (hD : D.m = ⊤)
    (t : ℝ) (ht : 0 < t) (h : RayCoset.logHyperplane F) :
    (∑' ℓ : RayCoset.normalizedLattice D,
      RayParity.gδ F ∅ (RayParity.Q F
        (RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h)
        (RayCoset.normalizedBasepoint D + (ℓ : euclidean.mixedSpace F)))) =
      centeredLogIdealTheta F (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) t h := by
  classical
  have hb : RayCoset.normalizedBasepoint D ∈ RayCoset.normalizedLattice D :=
    Submodule.mem_map.mpr ⟨D.b, by simpa [hD] using D.basepoint_mem, rfl⟩
  let b : RayCoset.normalizedLattice D := ⟨RayCoset.normalizedBasepoint D, hb⟩
  simp only [RayParity.gδ, Finset.prod_empty, one_mul, centeredLogIdealTheta, dif_pos ht]
  rw [show (∑' ℓ : RayCoset.normalizedLattice D,
      DedekindZetaZeroFree.AbelianQuotient.Theta.latticeGaussian Real.pi
        (RayParity.Q F (RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h)
          (RayCoset.normalizedBasepoint D + (ℓ : euclidean.mixedSpace F)))) =
      ∑' ℓ : RayCoset.normalizedLattice D,
        DedekindZetaZeroFree.AbelianQuotient.Theta.latticeGaussian Real.pi
          (RayParity.Q F (RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h) ℓ) from
    (Equiv.addLeft b).tsum_eq (fun ℓ =>
      DedekindZetaZeroFree.AbelianQuotient.Theta.latticeGaussian Real.pi
        (RayParity.Q F (RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h) ℓ))]
  rw [← (idealNormalizedEquiv F D hD).tsum_eq,
    DedekindZetaZeroFree.AbelianQuotient.Theta.fractionalShapeIdealTheta_eq_tsum_mixedGaussian,
    ← (idealFractionalEquiv F D).tsum_eq]
  apply tsum_congr
  intro x
  change DedekindZetaZeroFree.AbelianQuotient.Theta.latticeGaussian Real.pi
    (RayParity.Q F (RayTheta.q F (t / Real.sqrt |(NumberField.discr F : ℝ)|) h)
      (RayCoset.normalizedEmbedding D x.val)) =
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedGaussian F (x.val : F)
      (centeredLogShape F (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) t h)
  rw [RayCoset.normalizedEmbedding_apply, Q_smul_shape,
    ← centeredLogShape_eq F D t ht h,
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedGaussian_eq_latticeGaussian F _ _
      (fun v => ne_of_gt (centeredLogShape_pos F _ ht h v)),
    RayParity.Q_eq_traceRadialScale]

theorem topPrimal_eq_topLogIdealAverage
    (D : RayCoset.Data F) (hD : D.m = ⊤)
    (htop : (⊤ : Ideal (𝓞 F)) ≠ ⊥) (t : ℝ) (ht : 0 < t) :
    RayTheta.fδ D ∅ (t / Real.sqrt |(NumberField.discr F : ℝ)|) =
      topLogIdealAverage F htop
        (rayIdealFractionalIdeal F D.a D.ideal_ne_bot) t := by
  rw [RayTheta.fδ, if_pos (div_pos ht (discrSqrt_pos F))]
  simp_rw [topPrimal_integrand F D hD t ht]
  unfold topLogIdealAverage
  cases D
  cases hD
  rfl

end DedekindZetaZeroFree.Hecke.Theta

end
