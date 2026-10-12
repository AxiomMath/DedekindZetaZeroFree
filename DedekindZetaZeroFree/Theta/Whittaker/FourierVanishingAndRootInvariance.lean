module

public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem raw_rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ m) := by
  let n := Quotient.out (Matrix.ProjGenLinGroup.mk m)
  have hn : Matrix.ProjGenLinGroup.mk n = Matrix.ProjGenLinGroup.mk m := Quotient.out_eq' _
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn
  let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)
  have hs : φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 :=
    KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨z, rfl⟩
  change φ n = φ m
  rw [← hz, map_mul, hs, mul_one]

end DedekindZetaZeroFree.KPLiteralPeriod

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private def rootChar : AddChar (KPAdeles F) (G F ζ hζ) where
  toFun := KPGlobalTorusFunctionData.N F ζ hζ
  map_zero_eq_one' := (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  map_add_eq_mul' := KPGlobalTorusFunctionData.N_add F ζ hζ

private theorem rational_root_invariance
    (θ : Functions F ζ hζ) (hθ : Automorphic F ζ hζ θ) (t : F) (g : G F ζ hζ) :
    θ (rootChar F ζ hζ (algebraMap F (KPAdeles F) t) * g) = θ g := by
  have hr := hθ.2.1 (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n F t)) g
  rw [raw_rationalLift_mk] at hr
  change θ (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPRationalAdelicSplitting.N F ζ hζ _) * g) = _
  rw [KPRationalAdelicSplitting.N_rational]
  exact hr

private theorem rational_diagonal_invariance
    (θ : Functions F ζ hζ) (hθ : Automorphic F ζ hζ θ) (t : Fˣ) (g : G F ζ hζ) :
    θ (KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ t * g) = θ g := by
  have hr := hθ.2.1 (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F t 1)) g
  rw [raw_rationalLift_mk] at hr
  exact hr

theorem haar_fourier_vanishing_forces_root_invariance
    (ψ : ContinuousAddChar (KPAdditiveQuotient F))
    (hψ : KPReflectionSpec.NontrivialCharacter ψ)
    (μ : Measure (KPAdditiveQuotient F)) (hμ : μ.IsAddHaarMeasure)
    (θ : Functions F ζ hζ) (hθ : Automorphic F ζ hζ θ) :
    μ Set.univ ≠ ⊤ ∧ 0 < μ.real Set.univ ∧
    (∀ g, Integrable (fun x : KPAdditiveQuotient F =>
      θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) *
        star (ψ.toAddChar x)) μ) ∧
    ((∀ g, period F ζ hζ ψ μ (rightAction F ζ hζ g θ) = 0) →
      (∀ (x : KPAdeles F) g, θ (KPGlobalTorusFunctionData.N F ζ hζ x * g) = θ g) ∧
      (∀ g, (∫ x : KPAdditiveQuotient F,
        θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) ∂μ) =
          (μ.real Set.univ : ℂ) * θ g)) := by
  letI : CompactSpace (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).1
  letI : T2Space (KPAdditiveQuotient F) :=
    (additiveAdeleQuotient_compactHausdorff F).2
  letI : μ.IsAddHaarMeasure := hμ
  letI : IsFiniteMeasure μ := ⟨hμ.lt_top_of_isCompact isCompact_univ⟩
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hmass : μ Set.univ ≠ ⊤ := (hμ.lt_top_of_isCompact isCompact_univ).ne
  have hpos : 0 < μ Set.univ :=
    pos_iff_ne_zero.mpr (hμ.open_pos Set.univ isOpen_univ Set.univ_nonempty)
  have hreal : 0 < μ.real Set.univ := by
    exact ENNReal.toReal_pos hpos.ne' hmass
  let n := rootChar F ζ hζ
  have hncont : Continuous n :=
    KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ
  have hθn := rational_root_invariance F ζ hζ θ hθ
  have hfiber (g : G F ζ hζ) (x : KPAdeles F) :
      KPCompactFourier.unipotentFiber F n θ g (QuotientAddGroup.mk x) = θ (n x * g) :=
    KPGlobalGenericity.unipotentFiber_eq F n θ hθn g x
  have hfcont (g : G F ζ hζ) :
      Continuous (KPCompactFourier.unipotentFiber F n θ g) := by
    apply (QuotientAddGroup.isQuotientMap_mk
      (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
    change Continuous (fun x : KPAdeles F =>
      KPCompactFourier.unipotentFiber F n θ g (QuotientAddGroup.mk x))
    simp_rw [hfiber]
    exact hθ.1.1.comp (hncont.mul continuous_const)
  have hint (g : G F ζ hζ) : Integrable (fun x : KPAdditiveQuotient F =>
      θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) *
        star (ψ.toAddChar x)) μ := by
    exact ((hfcont g).mul ψ.continuous_toFun.star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hmass, hreal, hint, ?_⟩
  intro hvan
  let ψA : AddChar (KPAdeles F) Circle :=
    { toFun := fun x => ⟨star (ψ.toAddChar (QuotientAddGroup.mk x)), by
        change star (ψ.toAddChar (QuotientAddGroup.mk x)) ∈ Metric.sphere (0 : ℂ) 1
        rw [Metric.mem_sphere, dist_zero_right, norm_star]
        exact ψ.unitary (QuotientAddGroup.mk x)⟩
      map_zero_eq_one' := by
        apply Subtype.ext
        simp only [QuotientAddGroup.mk_zero, AddChar.map_zero_eq_one, star_one, Circle.coe_one]
      map_add_eq_mul' := by
        intro x y
        apply Subtype.ext
        simp only [QuotientAddGroup.mk_add, AddChar.map_add_eq_mul, star_mul', Circle.coe_mul] }
  have hψAcont : Continuous ψA :=
    (ψ.continuous_toFun.comp QuotientAddGroup.continuous_mk).star.subtype_mk _
  have hψAne : ψA ≠ 1 := by
    intro he
    obtain ⟨x, hx⟩ := hψ
    have he' := congrArg (fun χ : AddChar (KPAdeles F) Circle =>
      (χ (Quotient.out x) : ℂ)) he
    change star (ψ.toAddChar (QuotientAddGroup.mk (Quotient.out x))) = 1 at he'
    have hout : (QuotientAddGroup.mk (Quotient.out x) : KPAdditiveQuotient F) = x :=
      Quotient.out_eq' x
    rw [hout] at he'
    apply hx
    simpa only [star_star, star_one] using congrArg star he'
  have hψAF (t : F) : ψA (algebraMap F (KPAdeles F) t) = 1 := by
    apply Subtype.ext
    change star (ψ.toAddChar (QuotientAddGroup.mk (algebraMap F (KPAdeles F) t))) = 1
    rw [show (QuotientAddGroup.mk (algebraMap F (KPAdeles F) t) : KPAdditiveQuotient F) = 0 from
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨t, rfl⟩]
    simp only [AddChar.map_zero_eq_one, star_one]
  let ν : Measure (KPAdditiveQuotient F) := (μ Set.univ)⁻¹ • μ
  letI : ν.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul μ (ENNReal.inv_ne_zero.mpr hmass)
      (ENNReal.inv_ne_top.mpr hpos.ne')
  letI : IsProbabilityMeasure ν := ⟨by
    change ((μ Set.univ)⁻¹ • μ) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos.ne' hmass]⟩
  have hperiod (g : G F ζ hζ) :
      KPCompactFourier.fourierPeriod F ν ψA n θ g = 0 := by
    have hp := hvan g
    change (∫ x : KPAdditiveQuotient F,
      θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) *
        star (ψ.toAddChar x) ∂μ) = 0 at hp
    change (∫ x : KPAdditiveQuotient F,
      θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) *
        star (ψ.toAddChar (QuotientAddGroup.mk (Quotient.out x))) ∂ν) = 0
    simp_rw [Quotient.out_eq']
    rw [integral_smul_measure, hp, smul_zero]
  have hf := kp_right_translate_periods_force_constant F ν ψA hψAcont hψAne hψAF
    n hncont (KPGlobalTorusFunctionData.rationalDiagonalLift F ζ hζ)
    (KPWildIndependentGenericity.NonzeroPeriod.actual_rational_diagonal_conjugation F ζ hζ)
    θ hθ.1.1 hθn (rational_diagonal_invariance F ζ hζ θ hθ) hperiod
  have hct (g : G F ζ hζ) :
      θ g = ∫ x, KPCompactFourier.unipotentFiber F n θ g x ∂ν := by
    have hh := hf g (QuotientAddGroup.mk 0)
    rw [hfiber, n.map_zero_eq_one, one_mul] at hh
    exact hh
  have hinv (x : KPAdeles F) (g : G F ζ hζ) : θ (n x * g) = θ g := by
    rw [← hfiber, hf, ← hct]
  refine ⟨hinv, ?_⟩
  intro g
  have heq (x : KPAdditiveQuotient F) :
      θ (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x) * g) = θ g :=
    hinv (Quotient.out x) g
  simp_rw [heq]
  simp only [integral_const]
  exact RCLike.real_smul_eq_coe_mul _ _

end DedekindZetaZeroFree.KPLiteralPeriod

end
end
