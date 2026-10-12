module

public import DedekindZetaZeroFree.Eisenstein.Induction.AdelicSectionDescent
public import DedekindZetaZeroFree.Metaplectic.Torus.LocalNorms

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusEvaluation
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

 def evaluation (g : RestrictedCover F ζ hζ) (q : HeightOneSpectrum (𝓞 F))
    (x : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) : ℂ :=
  localUntwistedEvaluation F ζ hζ P C q ((LocalSeed.finite F ζ hζ P C q).val
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q)))) x

 theorem formula (g raw : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = e.val) :
    (RawSource.value F ζ hζ P C g).val.val e = RawSource.archProduct F ζ hζ g *
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (raw (Sum.inl w)).epsilon : ℂ)) *
      ∏ᶠ q, evaluation F ζ hζ P C g q (t q) := by
  let s := SourceTensor.evaluatedStage F ζ hζ P C g
  have hf := FullTorusFormula.finiteTensorRealization_full_raw_formula F ζ hζ P C s.val s.property
    (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (g (Sum.inr q.val)))) raw t e ht he
  change RawSource.archProduct F ζ hζ g *
    (SourceTensor.realization F ζ hζ P C (SourceTensor.evaluatedTensor F ζ hζ P C g)).val.val e = _
  rw [SourceTensor.evaluatedTensor, SourceTensor.realization_stage, hf]
  rw [mul_assoc]
  congr 2
  apply finprod_congr
  intro q
  unfold evaluation
  congr 1
  split_ifs with hq
  · rfl
  · exact (SourceTensor.evaluatedStage_tail F ζ hζ P C g q hq).symm

 theorem evaluation_finiteSupport (g raw : RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    Function.HasFiniteMulSupport (fun q => evaluation F ζ hζ P C g q (t q)) := by
  let s := SourceTensor.evaluatedStage F ζ hζ P C g
  have hf := local_evaluation_finiteSupport F ζ hζ P C s.val s.property
    (fun q => (LocalSeed.finite F ζ hζ P C q.val).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (g (Sum.inr q.val)))) raw t ht
  convert hf using 1
  funext q
  unfold evaluation
  congr 1
  split_ifs with hq
  · rfl
  · exact SourceTensor.evaluatedStage_tail F ζ hζ P C g q hq

 theorem norm_mul (q : HeightOneSpectrum (𝓞 F))
    (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate (x*t))) (1/6 : ℝ) : ℂ) =
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate x)) (1/6 : ℝ) : ℂ) *
    (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) := by
  rw [map_mul]
  simp only [KPGlobalCenterRationalCharacter.localAbs, Units.val_mul, nnnorm_mul, NNReal.coe_mul]
  exact (congrArg (fun z : ℝ => (z : ℂ)) (Real.mul_rpow
    (NNReal.coe_nonneg ‖((C.canonical q).borel.coordinate x : q.adicCompletion F)‖₊)
    (NNReal.coe_nonneg ‖((C.canonical q).borel.coordinate t : q.adicCompletion F)‖₊))).trans
      (Complex.ofReal_mul _ _)

 theorem untwisted_tau (q : HeightOneSpectrum (𝓞 F))
    (v : LocalFiber F ζ hζ P C q) (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    localUntwistedEvaluation F ζ hζ P C q (localTau F ζ hζ P C q t v) x =
    localUntwistedEvaluation F ζ hζ P C q v (x*t) *
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) := by
  unfold localUntwistedEvaluation
  change v.val (x*t) / _ = _
  rw [norm_mul F ζ hζ P C]
  have hx : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
    ((C.canonical q).borel.coordinate x)) (1/6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F _ _) _).ne'
  have ht : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
    ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast KPGlobalCenterRationalCharacter.localAbs_pos F _ _) _).ne'
  field_simp

 theorem evaluation_left (u g : RestrictedCover F ζ hζ)
    (q : HeightOneSpectrum (𝓞 F)) (x t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : t.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q))) :
    evaluation F ζ hζ P C (u*g) q x =
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t)) (1/2 : ℝ) : ℂ) *
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t)) (1/6 : ℝ) : ℂ) *
      evaluation F ζ hζ P C g q (x*t) := by
  unfold evaluation
  change localUntwistedEvaluation F ζ hζ P C q ((LocalSeed.finite F ζ hζ P C q).val
    (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (u (Sum.inr q)*g (Sum.inr q)))) x = _
  rw [LocalTorus.finite, LocalTorus.finite_deltaHalf]
  change (Real.rpow _ (1/2 : ℝ) : ℂ) *
    ((localTau F ζ hζ P C q t _).val x) / _ = _
  rw [mul_div_assoc]
  change (Real.rpow _ (1/2 : ℝ) : ℂ) * localUntwistedEvaluation F ζ hζ P C q
    (localTau F ζ hζ P C q t _) x = _
  rw [untwisted_tau]
  ring
  exact ht

 theorem phase_mul (x u : RestrictedCover F ζ hζ) :
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ ((x*u) (Sum.inl w)).epsilon : ℂ)) =
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (x (Sum.inl w)).epsilon : ℂ)) *
    (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (u (Sum.inl w)).epsilon : ℂ)) := by
  have hm w : ((x*u) (Sum.inl w)).epsilon = (x (Sum.inl w)).epsilon * (u (Sum.inl w)).epsilon := by
    change (x (Sum.inl w) * u (Sum.inl w)).epsilon = _
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  simp_rw [hm, map_mul, Units.val_mul]
  exact Finset.prod_mul_distrib

end DedekindZetaZeroFree.EisensteinReferenceSections.SourceTorusEvaluation

end
