module

public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.BorelCharacter
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Residues.RationalVectorCofactor

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal BigOperators
open MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.NormOneCofactor
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPRankOneShellRepair
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingGeometry renaming arch_center → arch_center
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem central_norm_one_correction
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ c : KPGlobalCenterRationalCharacter.Z F ζ hζ,
      KPGlobalTorusFunctionData.delta F ζ hζ (c.val * t) = 1 := by
  let w₀ : NumberField.InfinitePlace F := Classical.choice inferInstance
  let d : ℝ := ((KPGlobalTorusFunctionData.delta F ζ hζ t : ℝ≥0) : ℝ)
  have hd : 0 < d := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t)))
  let z : KPGlobalTorusFunctionData.TorusArch F := fun w =>
    if w = w₀ then (Real.exp (-Real.log d / 2) : ℂ) else 1
  have hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F := by
    intro w
    dsimp [z]
    split_ifs
    · exact_mod_cast Real.exp_ne_zero _
    · exact one_ne_zero
  have hzdelta : ((KPGlobalTorusFunctionData.delta F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z) : ℝ≥0) : ℝ) = d⁻¹ := by
    rw [KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ z hz]
    rw [Finset.prod_eq_single w₀]
    · simp only [z, ite_eq_left rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-Real.log d / 2) = -Real.log d by ring,
        Real.exp_neg, Real.exp_log hd]
    · intro w _ hw
      simp [z,hw]
    · simp
  obtain ⟨c,hc,hχ⟩ := arch_center F ζ hζ z
  refine ⟨c,?_⟩
  apply Units.ext
  apply NNReal.eq
  change ((KPGlobalTorusFunctionData.delta F ζ hζ (c.val * t) : ℝ≥0) : ℝ) = 1
  rw [map_mul, Units.val_mul, NNReal.coe_mul,hc,hzdelta]
  exact inv_mul_cancel₀ hd.ne'

private theorem central_scalar_covariance
    (f : smoothRationalFiber F ζ hζ) (c : KPGlobalCenterRationalCharacter.Z F ζ hζ)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    f.val.val (c.val * t) = (KPGlobalCenterRationalCharacter.omegaA F ζ hζ c : ℂ) * f.val.val t := by
  let r : KPGlobalCenterRationalCharacter.R F ζ hζ :=
    ⟨c.val,Subgroup.mem_sup_right c.property⟩
  have he := f.val.property r t
  have hc := KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ r 1 c (by simp [r])
  change f.val.val (c.val*t) = (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * f.val.val t at he
  rw [hc] at he
  simpa only [map_one, one_mul] using he

private theorem rationalStageEval_central
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C.exceptional ⊆ E)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (c : KPGlobalCenterRationalCharacter.Z F ζ hζ)
    (y : ∀ q : E, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q.val) :
    ActualCofactor.rationalStageEval F ζ hζ P C E hE (c.val*t) y =
      (KPGlobalCenterRationalCharacter.omegaA F ζ hζ c : ℂ) *
        ActualCofactor.rationalStageEval F ζ hζ P C E hE t y := by
  exact central_scalar_covariance F ζ hζ
    (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P
      (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C E hE
        (PiTensorProduct.tprod ℂ y))) c t

theorem exists_norm_one_rational_cofactor
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
    (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hE : C.exceptional ⊆ E) :
    let μ : ∀ q : E, Measure (LocalField F q.val) := fun q =>
      Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val)
    ∃ (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
        (C.canonical q.val).iwasawa .plus)
      (t : KPGlobalTorusFunctionData.E F ζ hζ) (b : ℂ → ℂ),
      KPGlobalTorusFunctionData.delta F ζ hζ t = 1 ∧
      MeromorphicOn b Set.univ ∧ AnalyticAt ℂ b 0 ∧ b 0 ≠ 0 ∧
      ∀ s : ℂ, b s = ActualCofactor.rationalStageEval F ζ hζ P C E hE t
        (fun q => (localHalfDifferentFactor F q.val : ℂ) •
          (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
            (μ q) (ActualCofactor.unit_mass F q.val) .plus s (φ q)).val 1) *
        ∏ _w : NumberField.InfinitePlace F, 2 * (Real.pi : ℂ) / ((1/3 : ℂ) + 2*s) := by
  obtain ⟨φ,t,b,hm,ha,hn,hb⟩ := ActualCofactor.actual_rational_nonzero_cofactor F ζ hζ P C E hE
  obtain ⟨c,hc⟩ := central_norm_one_correction F ζ hζ t
  let z : ℂ := KPGlobalCenterRationalCharacter.omegaA F ζ hζ c
  refine ⟨φ,c.val*t,fun s => z*b s,hc,?_,?_,?_,?_⟩
  · exact fun s hs => analyticAt_const.meromorphicAt.mul (hm s hs)
  · exact analyticAt_const.mul ha
  · exact mul_ne_zero (Units.ne_zero _) hn
  · intro s
    dsimp only
    rw [hb s,rationalStageEval_central,mul_assoc]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.NormOneCofactor

end
