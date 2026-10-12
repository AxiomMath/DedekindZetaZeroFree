module

public import DedekindZetaZeroFree.Theta.Profiles.UniformMixedThetaTail
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PeriodicCubeIntegration
public import DedekindZetaZeroFree.Theta.Profiles.PrincipalIdealCenteredShapeCovariance

@[expose] public section

open NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.Hecke

open DedekindZetaZeroFree.AbelianQuotient.Theta

private theorem continuous_slice (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    Continuous (mixedRadialTheta F I t) := by
  change Continuous ((fun p : ℝ × Angular F ↦ mixedRadialTheta F I p.1 p.2) ∘
    (fun u : Angular F ↦ (t, u)))
  exact (continuousOn_mixedRadialTheta F I).comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨ht, Set.mem_univ _⟩)

private theorem periodic_slice (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ)
    (z : {v : InfinitePlace F // v ≠ Units.dirichletUnitTheorem.w₀} → ℤ)
    (u : Angular F) :
    mixedRadialTheta F I t (u + fun i => (z i : ℝ)) = mixedRadialTheta F I t u := by
  classical
  have h : angularLift F (u + fun i => (z i : ℝ)) =
      angularLift F u + DedekindZetaZeroFree.Theta.unitCoordinateShift z := by
    ext v
    by_cases hv : v = Units.dirichletUnitTheorem.w₀ <;>
      simp [angularLift, DedekindZetaZeroFree.Theta.unitCoordinateShift, hv]
  simpa only [mixedRadialTheta, mixedThetaShape, h, add_right_comm] using
    fractionalShapeIdealTheta_expMapBasis_add_unitCoordinateShift F I
      (angularLift F u + radialLift F ((Real.log t - Real.log (mixedThetaCovolume F I)) /
        (Module.finrank ℚ F : ℝ))) z

private theorem principal_of_class (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J) :
    ∃ a : Fˣ, (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F) := by
  have hq := congrArg (ClassGroup.equiv F) hclass
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_monoidHom_refl] at hq
  have hq' : QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range I =
      QuotientGroup.mk' (toPrincipalIdeal (𝓞 F) F).range J := hq
  rw [QuotientGroup.mk'_eq_mk'] at hq'
  rcases hq' with ⟨a, ⟨b, rfl⟩, ha⟩
  refine ⟨b, ?_⟩
  simpa only [Units.val_mul, coe_toPrincipalIdeal, mul_comm] using
    (congrArg (fun U : (FractionalIdeal (𝓞 F)⁰ F)ˣ => (U : FractionalIdeal (𝓞 F)⁰ F)) ha).symm

theorem mixedAngularAverage_class_invariant (F : Type) [Field F] [NumberField F]
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J)
    (t : ℝ) (ht : 0 < t) :
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F I t =
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F J t := by
  classical
  obtain ⟨a, ha⟩ := principal_of_class F I J hclass
  obtain ⟨d, hd⟩ := principalCenteredShapeCovariance F I J a ha
  unfold mixedAngularAverage
  simp_rw [hd t ht]
  exact (periodicCubeIntegral_translation (mixedRadialTheta F I t)
    (continuous_slice F I t ht) (periodic_slice F I t) d).symm

theorem mixedNegAngularAverage_eq_mixedAngularAverage
    (F : Type) [Field F] [NumberField F]
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) (ht : 0 < t) :
    DedekindZetaZeroFree.AbelianQuotient.Theta.mixedNegAngularAverage F I t =
      DedekindZetaZeroFree.AbelianQuotient.Theta.mixedAngularAverage F I t := by
  classical
  exact periodicCubeIntegral_negation (mixedRadialTheta F I t)
    (continuous_slice F I t ht) (periodic_slice F I t)

end DedekindZetaZeroFree.Hecke
