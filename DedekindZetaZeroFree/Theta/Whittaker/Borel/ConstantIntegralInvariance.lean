module

public import DedekindZetaZeroFree.Theta.Whittaker.Borel.RootFibersAndHaar
public import DedekindZetaZeroFree.Theta.Periods.PartialPeriodSourcesAndRootCoinvariants

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPWildActualConstantIntegral
open KPGlobalTorusFunctionData
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem rational_root_invariant
    (θ : G F ζ hζ → ℂ)
    (hθ : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (t : F) (g : G F ζ hζ) :
    θ (N F ζ hζ (algebraMap F (Adeles F) t) * g) = θ g := by
  have he : N F ζ hζ (algebraMap F (Adeles F) t) =
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F t)) := by
    change KPRationalAdelicSplitting.pglN F ζ hζ _ = _
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    unfold KPRationalAdelicSplitting.pglN
    rw [KPRationalAdelicSplitting.N_rational]
  rw [he]
  exact hθ _ g

private theorem fiber_mk
    (θ : G F ζ hζ → ℂ)
    (hθ : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (b : borel F ζ hζ) (z : Adeles F) :
    KPWildRawSourceConstruction.sourceFiber F ζ hζ b θ (QuotientAddGroup.mk z) =
      θ (N F ζ hζ z * b.val) := by
  let R := AdeleRing.principalSubgroup (𝓞 F) F
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add R z
  obtain ⟨s, hs⟩ := r.property
  change θ (N F ζ hζ (Quotient.out (QuotientAddGroup.mk z)) * b.val) = _
  rw [hr, ← hs, add_comm, N_add, mul_assoc, rational_root_invariant F ζ hζ θ hθ]

private theorem borel_root_commutes (b : borel F ζ hζ) (y : Adeles F) :
    ∃ z : Adeles F, b.val * N F ζ hζ y = N F ζ hζ z * b.val := by
  obtain ⟨t, a, hb⟩ := KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization F ζ hζ b
  refine ⟨(p F ζ hζ t : Adeles F) * y, ?_⟩
  have hconj := ActualBorelRetraction.torus_conjugates_root F ζ hζ t y
  have hn : N F ζ hζ a * N F ζ hζ y = N F ζ hζ y * N F ζ hζ a := by
    rw [← N_add, ← N_add, add_comm]
  rw [hb]
  calc
    (t.val * N F ζ hζ a) * N F ζ hζ y = t.val * N F ζ hζ y * N F ζ hζ a := by
      rw [mul_assoc, hn, ← mul_assoc]
    _ = N F ζ hζ ((p F ζ hζ t : Adeles F) * y) * (t.val * N F ζ hζ a) := by
      rw [← hconj]
      group

theorem integral_right_root_eq
    (μ : Measure (KPCompactFourier.AdditiveQuotient F)) [μ.IsAddHaarMeasure]
    (θ : G F ζ hζ → ℂ)
    (hθ : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (b : borel F ζ hζ) (y : Adeles F) :
    (∫ x, KPWildRawSourceConstruction.sourceFiber F ζ hζ b
      (fun g => θ (g * N F ζ hζ y)) x ∂μ) =
      ∫ x, KPWildRawSourceConstruction.sourceFiber F ζ hζ b θ x ∂μ := by
  obtain ⟨z, hz⟩ := borel_root_commutes F ζ hζ b y
  have hshift (x : KPCompactFourier.AdditiveQuotient F) :
      KPWildRawSourceConstruction.sourceFiber F ζ hζ b
          (fun g => θ (g * N F ζ hζ y)) x =
        KPWildRawSourceConstruction.sourceFiber F ζ hζ b θ
          (x + QuotientAddGroup.mk z) := by
    have hx : (QuotientAddGroup.mk (KPCompactFourier.representative F x) :
        KPCompactFourier.AdditiveQuotient F) = x := Quotient.out_eq' x
    have hadd : (QuotientAddGroup.mk (KPCompactFourier.representative F x + z) :
        KPCompactFourier.AdditiveQuotient F) = x + QuotientAddGroup.mk z := by
      rw [QuotientAddGroup.mk_add, hx]
    rw [← hadd, fiber_mk F ζ hζ θ hθ]
    change θ ((N F ζ hζ (KPCompactFourier.representative F x) * b.val) * N F ζ hζ y) = _
    rw [mul_assoc, hz, ← mul_assoc, ← N_add]
  simp_rw [hshift]
  exact integral_add_right_eq_self _ _

end DedekindZetaZeroFree.KPWildActualConstantIntegral

end
