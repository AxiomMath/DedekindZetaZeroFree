module

public import DedekindZetaZeroFree.Eisenstein.Sections.CanonicalFlatFamily
public import DedekindZetaZeroFree.Adeles.Quotients.RationalBorel
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.TwoCellFormulaAndOutgoingProfiles
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContFlatRationalCosetCovariance

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev L (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    KPGlobalTorusFunctionData.G F ζ hζ → ℂ :=
  (KPContFlatSourceRecipe.flatR F ζ hζ s v).val

private theorem rationalBorel_invariance (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (a : KPGlobalResidualKernel.rationalBorel F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ a.val * g) =
      L F ζ hζ s v g := by
  have hc : (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).symm
      a.val ∈ KPChamberBruhatTwoCells.rationalBorel F := by
    rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_borel,
      MulEquiv.apply_symm_apply]
    exact a.property
  have h := KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.scalar_rational_borel_invariant
    F ζ hζ s (KPContFlatSourceRecipe.flatR F ζ hζ s v) ⟨_, hc⟩ g
  rw [← KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift] at h
  simpa only [MulEquiv.apply_symm_apply] using h

theorem L_rationalBorel (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (a : KPGlobalResidualKernel.rationalBorel F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ a.val * g) =
      L F ζ hζ s v g :=
  rationalBorel_invariance F ζ hζ s v a g

theorem L_centre (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (ε : rootsOfUnity 3 F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    L F ζ hζ s v (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * L F ζ hζ s v g := by
  let t : KPGlobalTorusFunctionData.E F ζ hζ :=
    (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val
  let h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H :=
    ⟨t, (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).contains_center
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).property⟩
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hp' : KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1 := by
    unfold KPGlobalTorusFunctionData.p
    have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
        (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
      rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
      exact ⟨ε, rfl⟩
    have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val.val = 1 := by
      rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
      exact MonoidHom.mem_ker.mp hker
    have ht : ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
        (fun t ht => ht)) (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val =
          (1 : KPGlobalTorusFunctionData.ordinaryTorus F) := Subtype.ext hp
    change KPGlobalTorusFunctionData.torusRatio F _ = 1
    rw [ht, map_one]
  have hdelta : KPGlobalTorusFunctionData.delta F ζ hζ (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1 := by
    change KPGlobalTorusFunctionData.delta F ζ hζ
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε).val = 1
    simp only [KPGlobalTorusFunctionData.delta, MonoidHom.comp_apply, hp', map_one]
  have hdh : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1 := by
    simp only [KPGlobalTorusFunctionData.deltaHalf, hdelta, Units.val_one, NNReal.coe_one,
      Real.sqrt_one, Complex.ofReal_one]
  have hnc : ((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
      (h : KPGlobalTorusFunctionData.E F ζ hζ) : ℂˣ) : ℂ) = 1 := by
    change KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s
      (h : KPGlobalTorusFunctionData.E F ζ hζ) = 1
    simp only [KPGlobalTorusBorelTwistCompatibility.normPower, hdelta, Units.val_one,
      NNReal.coe_one, Real.log_one, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
  have hlam : (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h =
      KPGlobalTorusFunctionData.iota F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.lambdaR_genuine F ζ hζ ε h (by rfl)
  have hsplit : ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂˣ) =
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ).character h *
        KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
          (h : KPGlobalTorusFunctionData.E F ζ hζ) := rfl
  have hcoef : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
        (h : KPGlobalTorusFunctionData.E F ζ hζ) *
      ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂ) =
      ((KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : Circle) : ℂ) := by
    have h1 : (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character h : ℂˣ) : ℂ)
        = (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) := by
      rw [hsplit, hlam, Units.val_mul, hnc, mul_one]
    rw [hdh, one_mul, h1]
    rfl
  have htv : (h : KPGlobalTorusFunctionData.E F ζ hζ).val =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F ζ hζ ε
  have hprop := (KPContFlatSourceRecipe.flatR F ζ hζ s v).property h 0 g
  rw [htv, hN, mul_one, hcoef] at hprop
  exact hprop

theorem rationalBorel_eq :
    (KPGlobalResidualKernel.rationalBorel F ζ hζ).comap
      (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).toMonoidHom =
        KPChamberBruhatTwoCells.rationalBorel F := by
  ext g
  rw [Subgroup.mem_comap]
  exact (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_borel
    F ζ hζ g).symm

abbrev cosetEquiv : KPChamberBruhatTwoCells.RationalQuotient F ≃
    KPGlobalResidualKernel.RationalQuotient F ζ hζ :=
  KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.cosetEquiv F ζ hζ

theorem cosetEquiv_mk (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    cosetEquiv F ζ hζ (KPChamberBruhatTwoCells.rationalCoset F γ) =
      Quotient.mk (QuotientGroup.rightRel (KPGlobalResidualKernel.rationalBorel F ζ hζ))
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F γ) := by
  show Quotient.congr
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).toEquiv
    _ (Quotient.mk (QuotientGroup.rightRel (KPChamberBruhatTwoCells.rationalBorel F)) γ) = _
  rw [Quotient.congr_mk]
  rfl

abbrev matrixRationalHom : Matrix.ProjGenLinGroup (Fin 2) F →*
    KPGlobalTorusFunctionData.G F ζ hζ :=
  (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ).comp
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).toMonoidHom

def rationalTerm (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (q : KPGlobalResidualKernel.RationalQuotient F ζ hζ) : ℂ :=
  L F ζ hζ s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ (Quotient.out q) * g)

theorem rationalTerm_eq (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (γ : KPRationalAdelicSplitting.RationalPGL2 F) :
    rationalTerm F ζ hζ s v g
        (Quotient.mk (QuotientGroup.rightRel (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ) =
      L F ζ hζ s v (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) := by
  unfold rationalTerm
  have he : Quotient.mk (QuotientGroup.rightRel (KPGlobalResidualKernel.rationalBorel F ζ hζ))
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel
        (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ)) =
      Quotient.mk (QuotientGroup.rightRel (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ :=
    Quotient.out_eq _
  have hb : γ * (Quotient.out (Quotient.mk (QuotientGroup.rightRel
      (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ))⁻¹ ∈
      KPGlobalResidualKernel.rationalBorel F ζ hζ :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  have hi := rationalBorel_invariance F ζ hζ s v ⟨_, hb⟩
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel
        (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ)) * g)
  rw [map_mul, map_inv] at hi
  rw [show (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ *
      (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel
          (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ)))⁻¹) *
      (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (Quotient.out (Quotient.mk (QuotientGroup.rightRel
          (KPGlobalResidualKernel.rationalBorel F ζ hζ)) γ)) * g) =
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g from by group] at hi
  exact hi.symm

theorem rationalTerm_transport (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (q : KPChamberBruhatTwoCells.RationalQuotient F) :
    rationalTerm F ζ hζ s v g (cosetEquiv F ζ hζ q) =
      KPChamberBruhatTwoCells.rationalTerm F (matrixRationalHom F ζ hζ)
        (L F ζ hζ s v) g q := by
  have hq : cosetEquiv F ζ hζ q =
      Quotient.mk (QuotientGroup.rightRel (KPGlobalResidualKernel.rationalBorel F ζ hζ))
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
          (Quotient.out q)) := by
    conv_lhs => rw [← Quotient.out_eq q]
    exact cosetEquiv_mk F ζ hζ (Quotient.out q)
  rw [hq, rationalTerm_eq F ζ hζ s v g
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
      (Quotient.out q))]
  rw [KPChamberBruhatTwoCells.rationalTerm]
  rfl

theorem rationalTerm_transport_mk (s : ℂ)
    (v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) :
    rationalTerm F ζ hζ s v g
        (cosetEquiv F ζ hζ (KPChamberBruhatTwoCells.rationalCoset F γ)) =
      L F ζ hζ s v (matrixRationalHom F ζ hζ γ * g) := by
  rw [cosetEquiv_mk F ζ hζ γ]
  rw [rationalTerm_eq F ζ hζ s v g
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F γ)]
  rfl

end DedekindZetaZeroFree.KPContFlatRationalCosetCovariance

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
