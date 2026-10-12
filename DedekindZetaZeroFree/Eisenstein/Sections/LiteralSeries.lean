module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree
namespace KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev R := KPGlobalCenterRationalCharacter.R F ζ hζ
abbrev Functions := G F ζ hζ → ℂ

def rationalLift (γ : Matrix.ProjGenLinGroup (Fin 2) F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ (Quotient.out γ))

def rightAction : Representation ℂ (G F ζ hζ) (Functions F ζ hζ) where
  toFun a :=
    { toFun := fun f g => f (g * a)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f g; simp
  map_mul' := by intros; ext f g; simp [mul_assoc]

def Smooth (f : Functions F ζ hζ) : Prop :=
  Continuous f ∧
  (∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
    (fun x => f (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
    (KPGlobalResidualConstruction.archDomain F)) ∧
  ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
    ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U → f (g * u) = f g

def Induced (s : ℂ) (f : Functions F ζ hζ) : Prop :=
  Smooth F ζ hζ f ∧ ∀ (r : R F ζ hζ) (x : KPAdeles F) g,
    f ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * f g

def IwasawaCompact (K : Subgroup (G F ζ hζ)) : Prop :=
  IsCompact (K : Set (G F ζ hζ)) ∧
  (∀ g, ∃ (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (k : K),
    g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) ∧
  ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2),
    KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈ K

def KFinite (K : Subgroup (G F ζ hζ)) (f : Functions F ζ hζ) : Prop :=
  ∃ S : Submodule ℂ (Functions F ζ hζ), Module.Finite ℂ S ∧ f ∈ S ∧
    ∀ k : K, ∀ v ∈ S, rightAction F ζ hζ k.val v ∈ S

abbrev Flat (K : Subgroup (G F ζ hζ)) :=
  {f : ℂ → Functions F ζ hζ // (∀ s, Induced F ζ hζ s (f s)) ∧
    (∀ s (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K),
      f s (t.val * k.val) =
        KPGlobalExceptionalParameter.realLogPower
          (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) s *
        f 0 (t.val * k.val)) ∧ KFinite F ζ hζ K (f 0)}

def eisenstein (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K) (s : ℂ) (g : G F ζ hζ) : ℂ :=
  ∑' c : KPChamberBruhatTwoCells.RationalQuotient F,
    f.val s (rationalLift F ζ hζ (Quotient.out c) * g)

def Automorphic (f : Functions F ζ hζ) : Prop :=
  Smooth F ζ hζ f ∧
  (∀ γ g, f (rationalLift F ζ hζ γ * g) = f g) ∧
  ∀ ε g, f (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
    (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * f g

def residueSpan (K : Subgroup (G F ζ hζ))
    (cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ) : Submodule ℂ (Functions F ζ hζ) :=
  Submodule.span ℂ {v | ∃ f a, v = rightAction F ζ hζ a (cleared f 0)}

def residueCore (K : Subgroup (G F ζ hζ))
    (cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ) : Submodule ℂ (Functions F ζ hζ) :=
  KPGlobalEisensteinData.hcHeckeCore
    ((rightAction F ζ hζ).comp K.subtype)
    ((rightAction F ζ hζ).comp (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype)
    (residueSpan F ζ hζ K cleared)

def ExceptionalGerm (K : Subgroup (G F ζ hζ))
    (E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ) : Prop :=
  (∀ f s, (1 : ℝ) / 3 < s.re → ∀ g,
    E f s g = eisenstein F ζ hζ K f s g) ∧
  (∀ f, ∃ (U : Set ℂ) (radius : ℝ),
    IsOpen U ∧ IsConnected U ∧
    {s : ℂ | (1 : ℝ) / 3 < s.re} ⊆ U ∧
    0 < radius ∧ Metric.ball (0 : ℂ) radius ⊆ U ∧
    (∀ g, MeromorphicOn (fun s => E f s g) U) ∧
    (∀ s ∈ Metric.ball (0 : ℂ) radius, s ≠ 0 → cleared f s = s • E f s) ∧
    (∀ g, AnalyticOnNhd ℂ (fun s => cleared f s g) (Metric.ball (0 : ℂ) radius)))

end KPLiteralRaw

end DedekindZetaZeroFree

end

section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteral
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ

def IwasawaCompact (K : Subgroup (G F ζ hζ)) : Prop :=
  IsCompact (K : Set (G F ζ hζ)) ∧
  (∀ g, ∃ (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (k : K),
    g = (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * k.val) ∧
  ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2),
    KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈ K
end DedekindZetaZeroFree.KPLiteral

end
end
