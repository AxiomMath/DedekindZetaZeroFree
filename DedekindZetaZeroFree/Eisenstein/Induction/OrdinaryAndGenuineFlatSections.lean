module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.TraceCharactersAndGaussShifts
public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData
public import DedekindZetaZeroFree.Eisenstein.Induction.ExceptionalTorusSphericalSeed
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaHeightRegularity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped Classical NumberField Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

 theorem height_borel (R : PrincipalMellin.ActualRecipe S η)
    (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) (x : KPAdeles F) (g : Group R) :
    iwasawaLogHeight R ((t.val * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x) * g) =
      Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 t : NNReal) : ℝ) + iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul]
  simp only [Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (by exact_mod_cast Units.ne_zero _) (by exact_mod_cast Units.ne_zero _)

 theorem height_compact (R : PrincipalMellin.ActualRecipe S η)
    (g : Group R) (k : fullProductCompact R) : iwasawaLogHeight R (g * k.val) = iwasawaLogHeight R g := by
  unfold iwasawaLogHeight
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) g k
  rw [h]

 theorem height_one (R : PrincipalMellin.ActualRecipe S η) : iwasawaLogHeight R 1 = 0 := by
  unfold iwasawaLogHeight
  have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_compact F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) (1 : fullProductCompact R)
  change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F R.A.zeta12 R.A.primitive_zeta12 (fullProductIwasawaData R) 1 = 1 at h
  rw [h]; simp

private theorem finite_compact_mem (R : PrincipalMellin.ActualRecipe S η)
    (p : KPFinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (hk : k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p)) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k) ∈ fullProductCompact R := by
  refine Subgroup.mem_map.mpr ⟨KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k, ?_, rfl⟩
  intro v
  rw [KPAdelicCoverRestrictedProduct.localToRestricted, RestrictedProduct.mulSingleMonoidHom_apply,
    RestrictedProduct.coe_mulSingle_apply]
  rcases eq_or_ne v (Sum.inr p) with rfl | hne
  · rw [Pi.mulSingle_eq_same]; exact finite_compact_le_iwasawa_compact_factor R p hk
  · rw [Pi.mulSingle_eq_of_ne hne]; exact (iwasawaCompactFactor R v).one_mem

 def seedTwist (R : PrincipalMellin.ActualRecipe S η) (b : InducedSourceSeed R) (s : ℂ) : Functions R :=
  fun g => Complex.exp (s * (iwasawaLogHeight R g : ℂ)) * b.value g

 theorem twist_zero (R : PrincipalMellin.ActualRecipe S η) (b : InducedSourceSeed R) : seedTwist R b 0 = b.value := by
  ext g; simp [seedTwist]

private theorem twist_level (R : PrincipalMellin.ActualRecipe S η) (b : InducedSourceSeed R)
    (s : ℂ) (g u : Group R)
    (hu : u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 b.level) :
    seedTwist R b s (g * u) = seedTwist R b s g := by
  unfold seedTwist
  rw [height_compact R g ⟨u, b.level_le hu⟩, b.fixed g u hu]

 theorem twist_induced (R : PrincipalMellin.ActualRecipe S η) (b : InducedSourceSeed R) (s : ℂ) :
    KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 s (seedTwist R b s) := by
  refine ⟨⟨?_, ?_, b.level, twist_level R b s⟩, ?_⟩
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp (iwasawa_log_height_regular R).1)).cexp).mul b.induced.1.1
  · intro g
    exact ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((iwasawa_log_height_regular R).2 g))).cexp).mul (b.induced.1.2.1 g)
  · intro r x g
    unfold seedTwist
    rw [height_borel, b.induced.2 r x g]
    unfold KPGlobalExceptionalParameter.realLogPower
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    simp only [add_zero]
    rw [show (1 / 2 + s) * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) =
      s * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) +
      (1 / 2) * (Real.log ((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 r.val : NNReal) : ℝ) : ℂ) by ring,
      Complex.exp_add]
    ring

 def seedFlat (R : PrincipalMellin.ActualRecipe S η) (b : InducedSourceSeed R) :
    KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 (fullProductCompact R) := by
  refine ⟨seedTwist R b, twist_induced R b, ?_, ?_⟩
  · intro s t k
    have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
    have hk : iwasawaLogHeight R k.val = 0 := by
      simpa [height_one] using height_compact R 1 k
    have ht := height_borel R t 0 k.val
    simp only [hN, mul_one, hk, add_zero] at ht
    rw [twist_zero]
    simp only [seedTwist, ht, KPGlobalExceptionalParameter.realLogPower]
  · rw [twist_zero]; exact b.kfinite

theorem induced_ordinary_central_covariance (R : PrincipalMellin.ActualRecipe S η)
    (s : ℂ) (f : Functions R)
    (hf : KPLiteralRaw.Induced F R.A.zeta12 R.A.primitive_zeta12 s f)
    (ε : rootsOfUnity 3 F) (g : Group R) :
    f (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 ε * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε : ℂ) * f g := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F R.A.zeta12 R.A.primitive_zeta12 ε
  let r : KPGlobalCenterRationalCharacter.R F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨z.val, Subgroup.mem_sup_right z.property⟩
  have hd : KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 z.val = 1 := by
    apply Units.val_injective
    apply NNReal.rpow_left_injective (show (1 / 6 : ℝ) ≠ 0 by norm_num)
    change (KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 z.val : NNReal) = (1 : NNReal) ^ (1 / 6 : ℝ)
    rw [KPGlobalCenterRationalCharacter.nu_centralRoot]; simp
  have hc := KPGlobalCenterRationalCharacter.lambdaR_genuine F R.A.zeta12 R.A.primitive_zeta12 ε r rfl
  have h := hf.2 r 0 g
  have hN : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  have hz : z.val.val = KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F R.A.zeta12 R.A.primitive_zeta12 ε
  simpa only [r, hz, hN, mul_one,
    KPGlobalExceptionalParameter.realLogPower, hd, hc, Units.val_one, NNReal.coe_one,
    Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using h

theorem additive_quotient_probability_haar_exists : ∃ dq : Measure (KPAdditiveQuotient F),
    dq.IsAddHaarMeasure ∧ dq Set.univ = 1 := by
  let dq : Measure (KPAdditiveQuotient F) := Measure.addHaarMeasure ⊤
  exact ⟨dq, inferInstance, Measure.addHaarMeasure_self (K₀ := ⊤)⟩

theorem admissible_flat_sources
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) : Nonempty (JointRootAlignedSources R N) := by
  obtain ⟨b⟩ := induced_source_seed_exists R hR
  obtain ⟨dq, hdq, hprob⟩ := additive_quotient_probability_haar_exists (F := F)
  refine ⟨{ aligned := hR, transport := N, transport_exact := rfl, sources := {
    K := fullProductCompact R
    iwasawa := full_product_compact_iwasawa R
    flat := fun _ => seedFlat R b
    finite_companions := ?_
    level := b.level
    common_level := fun _ => twist_level R b
    ordinary := fun _ s => induced_ordinary_central_covariance R s _ (twist_induced R b s)
    exterior_spherical := ?_
    dq := dq, quotientHaar := hdq, probability := hprob } }⟩
  · letI := SArithmeticData.sunitSixthPowerQuotient_finite F R.A
    exact Finite.of_equiv (PowerQuotient R.A.Rˣ 6)
      (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv R.A.U R.A.Rˣ 6 R.A.unitEquiv).symm.toEquiv
  · intro v s p hp k hk g
    change seedTwist R b s _ = seedTwist R b s g
    unfold seedTwist
    rw [height_compact R g ⟨_, finite_compact_mem R p k hk⟩, b.spherical p hp k hk g]
end DedekindZetaZeroFree.ThetaExpansion

end
