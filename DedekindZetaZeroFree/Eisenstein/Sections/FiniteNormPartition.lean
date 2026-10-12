module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal

namespace DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}

def logIncrement (g u : KPMsRationalCompactCrossPairing.G F ζ hζ) : ℝ :=
  Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (g * u) : ℝ≥0) : ℝ)) -
    Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))

 def rawIwasawa (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ) :
    KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ :=
  { K := D.K, compact := D.compact, decomposition := D.decomposition, overlap := D.overlap }

private theorem norm_borel_mul
    (t : KPMsRationalCompactCrossPairing.E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (g : KPMsRationalCompactCrossPairing.G F ζ hζ) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
        ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.delta F ζ hζ t *
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g :=
  KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_borel_mul F ζ hζ (rawIwasawa D) t x g

theorem logIncrement_borel_mul
    (t : KPMsRationalCompactCrossPairing.E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (g u : KPMsRationalCompactCrossPairing.G F ζ hζ) :
    logIncrement (D := D) ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) u =
      logIncrement (D := D) g u := by
  unfold logIncrement
  rw [mul_assoc, norm_borel_mul, norm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  have hn (v : (ℝ≥0)ˣ) : ((v : ℝ≥0) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero v)
  rw [Real.log_mul (hn _) (hn _), Real.log_mul (hn _) (hn _)]
  ring

theorem logIncrement_range_eq
    (u : KPMsRationalCompactCrossPairing.G F ζ hζ) :
    Set.range (fun g => logIncrement (D := D) g u) =
      Set.range (fun k : D.K => logIncrement (D := D) k.val u) := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨t, x, k, hg⟩ := D.decomposition g
    refine ⟨k, ?_⟩
    change logIncrement (D := D) k.val u = logIncrement (D := D) g u
    rw [hg, logIncrement_borel_mul]
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, rfl⟩

theorem logIncrement_range_finite
    (u : KPMsRationalCompactCrossPairing.G F ζ hζ)
    (hlc : IsLocallyConstant (fun k : D.K => logIncrement (D := D) k.val u)) :
    (Set.range (fun g => logIncrement (D := D) g u)).Finite := by
  letI : CompactSpace D.K := isCompact_iff_compactSpace.mp D.compact
  rw [logIncrement_range_eq]
  exact hlc.range_finite

end DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition

end
