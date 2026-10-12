module

public import DedekindZetaZeroFree.Eisenstein.Residues.Boundary.RadialHomogeneity
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.Residues.AverageArchimedeanCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryInvariance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ
open KPGlobalResidualConstruction KPMsGreenFlux
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabActualMean renaming root_mem_rational → root_mem_rational

theorem upper_integrand_descends (f : G → ℂ)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀g, f (γ.val*g)=f g)
    (g : G) (b c : KPGlobalTorusFunctionData.Adeles F)
    (hbc : (QuotientAddGroup.mk b : KPAdditiveQuotient F)=QuotientAddGroup.mk c) :
    f (KPGlobalTorusFunctionData.N F ζ hζ b*g)=f (KPGlobalTorusFunctionData.N F ζ hζ c*g) := by
  obtain ⟨t,ht⟩ := QuotientAddGroup.eq.mp hbc
  have he : c = algebraMap F (KPGlobalTorusFunctionData.Adeles F) t + b := by
    change c = algebraMap F (NumberField.AdeleRing (𝓞 F) F) t + b
    rw [ht]
    abel
  rw [he,KPGlobalTorusFunctionData.N_add,mul_assoc]
  exact (hr ⟨_,root_mem_rational t⟩ _).symm

theorem upper_integrand_continuous (f : G → ℂ) (hc : Continuous f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀g, f (γ.val*g)=f g) :
    Continuous (fun p : KPAdditiveQuotient F × G =>
      f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out p.1)*p.2)) := by
  let : IsTopologicalGroup G :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply (QuotientAddGroup.isOpenQuotientMap_mk.prodMap (IsOpenQuotientMap.id (X:=G))).continuous_comp_iff.mp
  change Continuous (fun z : KPGlobalTorusFunctionData.Adeles F × G =>
    f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk z.1))*z.2))
  have he (z : KPGlobalTorusFunctionData.Adeles F × G) :
      f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out (QuotientAddGroup.mk z.1))*z.2) =
      f (KPGlobalTorusFunctionData.N F ζ hζ z.1*z.2) :=
    upper_integrand_descends f hr z.2 _ _ (Quotient.out_eq _)
  simp_rw [he]
  exact hc.comp (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
    F ζ hζ).comp continuous_fst).mul continuous_snd)

theorem upper_continuous (f : G → ℂ) (hc : Continuous f)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀g, f (γ.val*g)=f g) :
    Continuous (upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F) f) := by
  have hj := upper_integrand_continuous f hc hr
  change Continuous (fun g => ∫q : KPAdditiveQuotient F,
    f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g) ∂KPWildKernelUpperBound.quotientHaar F)
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=Set.univ) isCompact_univ
  · exact (hj.comp continuous_swap).continuousOn
  · intro p x hp hx
    exact False.elim (hx (Set.mem_univ x))

theorem upper_unipotent (f : G → ℂ)
    (hr : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀g, f (γ.val*g)=f g)
    (a : KPGlobalTorusFunctionData.Adeles F) (g : G) :
    upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F) f
      (KPGlobalTorusFunctionData.N F ζ hζ a*g) =
    upperConstantTerm F ζ hζ (KPWildKernelUpperBound.quotientHaar F) f g := by
  let φ : KPAdditiveQuotient F → ℂ := fun q => f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)
  have he (q : KPAdditiveQuotient F) :
      f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*(KPGlobalTorusFunctionData.N F ζ hζ a*g)) =
      φ (q+QuotientAddGroup.mk a) := by
    have hq : (QuotientAddGroup.mk (Quotient.out (q+QuotientAddGroup.mk a)) : KPAdditiveQuotient F) =
        QuotientAddGroup.mk (Quotient.out q+a) := by
      rw [QuotientAddGroup.mk_add]
      exact (Quotient.out_eq (q+QuotientAddGroup.mk a)).trans
        (congrArg (fun x : KPAdditiveQuotient F => x+QuotientAddGroup.mk a) (Quotient.out_eq q).symm)
    have hd := upper_integrand_descends f hr g _ _ hq
    dsimp [φ]
    rw [hd,KPGlobalTorusFunctionData.N_add,mul_assoc]
  change (∫q, f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*(KPGlobalTorusFunctionData.N F ζ hζ a*g)) ∂KPWildKernelUpperBound.quotientHaar F) = ∫q,φ q ∂KPWildKernelUpperBound.quotientHaar F
  simp_rw [he]
  exact integral_add_right_eq_self φ (QuotientAddGroup.mk a)

theorem source_central (s : ℂ) (f : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (ε : rootsOfUnity 3 F) (g : G) :
    f.val (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * f.val g := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
  let t : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
    ⟨z.val, (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).contains_center z.property⟩
  have hp : KPGlobalTorusFunctionData.p F ζ hζ z.val = 1 := by
    unfold KPGlobalTorusFunctionData.p
    have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val.val = 1 := by
      rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
      apply MonoidHom.mem_ker.mp
      rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
      exact ⟨ε, rfl⟩
    change KPGlobalTorusFunctionData.torusRatio F
      ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val.val, z.val.property⟩ = 1
    have he : (⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ z.val.val, z.val.property⟩ :
        KPGlobalTorusFunctionData.ordinaryTorus F) = 1 := Subtype.ext hproj
    rw [he, map_one]
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ t.val = 1 := by
    simp only [KPGlobalTorusFunctionData.delta, MonoidHom.comp_apply, t, hp, map_one]
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val = 1 := by
    simp only [KPGlobalTorusFunctionData.deltaHalf, hd, Units.val_one, NNReal.coe_one,
      Real.sqrt_one, Complex.ofReal_one]
  have hn : (KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s t.val : ℂ) = 1 := by
    change KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t.val = 1
    simp only [KPGlobalTorusBorelTwistCompatibility.normPower, hd, Units.val_one,
      NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hl : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character t =
      KPGlobalTorusFunctionData.iota F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.lambdaR_genuine F ζ hζ ε t rfl
  have hc : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character t : ℂ) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) := by
    change ((KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character t : ℂ) *
      (KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s t.val : ℂ) = _
    rw [hl, hn, mul_one]
    rfl
  have htv : t.val.val = KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F ζ hζ ε
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simpa only [htv, hN, mul_one, hhalf, hc, one_mul] using f.property t 0 g

theorem source_unipotent (s : ℂ) (f : KPMsRationalCompactCrossPairing.Source F ζ hζ s)
    (a : KPGlobalTorusFunctionData.Adeles F) (g : G) :
    f.val (KPGlobalTorusFunctionData.N F ζ hζ a*g)=f.val g := by
  have h := f.property 1 a g
  simpa [KPGlobalTorusFunctionData.deltaHalf] using h
end DedekindZetaZeroFree.FourierContinuation.ResidualBoundaryInvariance

end
