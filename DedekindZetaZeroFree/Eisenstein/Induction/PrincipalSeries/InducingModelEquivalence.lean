module

public import DedekindZetaZeroFree.Metaplectic.Kubota.Induction.UnitaryRationalFiberComparison
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalInducingAdapter
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

 def fiberCongr (q : HeightOneSpectrum (𝓞 F))
    (S T : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (h : S = T) : KPLocalStoneVonNeumann.InducedModule S.polarization ≃ₗ[ℂ]
      KPLocalStoneVonNeumann.InducedModule T.polarization := by
  cases h
  exact LinearEquiv.refl ℂ _

def bad : Finset (Places F) := PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet F ζ hζ P C

 instance level_nonempty {J : Type*} (E : Finset J) :
    Nonempty (RestrictedTensorSimple.Level E) := ⟨⟨E, le_rfl⟩⟩

 def coreCongr {J : Type*} {V W : J → Type*}
    [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (e : ∀ j, V j) (f : ∀ j, W j) (E : Finset J)
    (a : ∀ j, V j ≃ₗ[ℂ] W j) (ha : ∀ j, a j (e j) = f j) :
    RestrictedTensorSimple.Core V e E ≃ₗ[ℂ] RestrictedTensorSimple.Core W f E :=
  Module.DirectLimit.congr (fun s => PiTensorProduct.congr (fun j : s.val => a j.val))
    (by
      intro s t hst
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro x
      change PiTensorProduct.congr (fun j : t.val => a j.val)
        (RestrictedTensorSimple.insert V e s.val t.val hst (PiTensorProduct.tprod ℂ x)) =
        RestrictedTensorSimple.insert W f s.val t.val hst
          (PiTensorProduct.congr (fun j : s.val => a j.val) (PiTensorProduct.tprod ℂ x))
      rw [RestrictedTensorSimple.insert_pure, PiTensorProduct.congr_tprod,
        PiTensorProduct.congr_tprod, RestrictedTensorSimple.insert_pure]
      congr 1
      funext j
      split_ifs with h
      · rfl
      · exact ha j.val)

 theorem bad_eq : bad F ζ hζ P C = ScalarAbsorption.fullBad (A := NumberField.InfinitePlace F) C.exceptional := by
  ext v
  cases v <;> simp [bad, PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.badSet, ScalarAbsorption.fullBad]

 def archAbsorption :
    RestrictedTensorSimple.Core (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.LocalFiberOnPlaces F ζ hζ P C)
      (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.canonRef F ζ hζ P C) (bad F ζ hζ P C) ≃ₗ[ℂ]
    RestrictedTensorSimple.Core (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
      (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional := by
  rw [bad_eq]
  let a : ∀ v : Places F,
      PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.LocalFiberOnPlaces F ζ hζ P C v ≃ₗ[ℂ]
      ScalarAbsorption.FullV (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C) v :=
    fun v => match v with
      | .inl _ => LinearEquiv.refl ℂ ℂ
      | .inr q => LinearEquiv.refl ℂ (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q)
  exact (coreCongr (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.canonRef F ζ hζ P C)
    (ScalarAbsorption.fullReference _ (KPGlobalTorusFiniteStages.localReference F ζ hζ P C))
    (ScalarAbsorption.fullBad (A := NumberField.InfinitePlace F) C.exceptional) a
    (by intro v; cases v <;> rfl)).trans
      (ScalarAbsorption.equivalence (A := NumberField.InfinitePlace F)
        (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
        (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional
        (fun q _ => PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.localReference_ne_zero F ζ hζ P C q))

def finiteTensorMap :
    RestrictedTensorSimple.Core (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
      (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional →ₗ[ℂ]
      KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ
        (KPGlobalTorusFiniteStages.productModel F ζ hζ P) :=
  (TorusCoreComparison.finiteTensorCore_lift_exists F ζ hζ P C).choose

 def finiteComparison :
    RestrictedTensorSimple.Core (KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C)
      (KPGlobalTorusFiniteStages.localReference F ζ hζ P C) C.exceptional →ₗ[ℂ]
      ↥(smoothRationalFiber F ζ hζ) :=
  (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.productUnitaryToRational F ζ hζ P).comp
    (finiteTensorMap F ζ hζ P C)

def rationalTau : Representation ℂ (B F ζ hζ) (RationalFiber F ζ hζ) :=
  (KPGlobalTorusFunctionData.rightTranslation
    (KPGlobalCenterRationalCharacter.R F ζ hζ)
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom).comp
      (ActualBorelRetraction.retraction F ζ hζ)

theorem rationalTau_center (z : KPGlobalCenterRationalCharacter.Z F ζ hζ)
    (b : B F ζ hζ) (hb : b.val = z.val.val) (f : RationalFiber F ζ hζ) :
    rationalTau F ζ hζ b f =
      (KPGlobalCenterRationalCharacter.omegaA F ζ hζ z : ℂ) • f := by
  have hbb : b = ActualBorelRetraction.torusInBorel F ζ hζ z.val := Subtype.ext hb
  subst b
  let r : KPGlobalCenterRationalCharacter.R F ζ hζ :=
    ⟨z.val, (KPGlobalCenterRationalCharacter.R_eq_product F ζ hζ z.val).mpr
      ⟨1, z, by simp⟩⟩
  have hr : KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r =
      KPGlobalCenterRationalCharacter.omegaA F ζ hζ z :=
    KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ r 1 z (by simp [r])
  apply Subtype.ext
  funext g
  change f.val (g * ActualBorelRetraction.retraction F ζ hζ
      (ActualBorelRetraction.torusInBorel F ζ hζ z.val)) = _
  rw [ActualBorelRetraction.retraction_torus,
    Subgroup.mem_center_iff.mp z.property g]
  change f.val (z.val * g) =
    (KPGlobalCenterRationalCharacter.omegaA F ζ hζ z : ℂ) * f.val g
  have hf := f.property r g
  change f.val (z.val * g) =
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * f.val g at hf
  rwa [hr] at hf

def delta : B F ζ hζ →* (ℝ≥0)ˣ :=
  (KPGlobalTorusFunctionData.delta F ζ hζ).comp (ActualBorelRetraction.retraction F ζ hζ)

 def sqrtHom : (ℝ≥0)ˣ →* (ℝ≥0)ˣ where
  toFun x := Units.mk0 (NNReal.sqrt x.val) (by intro h; have := congrArg (fun z : ℝ≥0 => z * z) h; rw [NNReal.mul_self_sqrt] at this; exact x.ne_zero (by simpa using this))
  map_one' := by apply Units.ext; simp
  map_mul' x y := by apply Units.ext; exact NNReal.sqrt_mul _ _

def deltaHalf : B F ζ hζ →* (ℝ≥0)ˣ := sqrtHom.comp (delta F ζ hζ)

theorem deltaHalf_square (b : B F ζ hζ) :
    deltaHalf F ζ hζ b * deltaHalf F ζ hζ b = delta F ζ hζ b := by
  apply Units.ext
  exact NNReal.mul_self_sqrt _

theorem delta_torus (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (b : B F ζ hζ) (hb : b.val = t.val) :
    delta F ζ hζ b = KPGlobalTorusFunctionData.delta F ζ hζ t := by
  have hbb : b = ActualBorelRetraction.torusInBorel F ζ hζ t := Subtype.ext hb
  subst b
  change KPGlobalTorusFunctionData.delta F ζ hζ
    (ActualBorelRetraction.retraction F ζ hζ
      (ActualBorelRetraction.torusInBorel F ζ hζ t)) = _
  rw [ActualBorelRetraction.retraction_torus]

 def smoothTau : Representation ℂ (B F ζ hζ) ↥(smoothRationalFiber F ζ hζ) :=
  (KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
    (KPGlobalTorusPeriodizationInverse.rationalModel F ζ hζ)).comp
      (ActualBorelRetraction.retraction F ζ hζ)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalInducingAdapter

end
