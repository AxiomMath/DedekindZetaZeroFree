module

public import DedekindZetaZeroFree.Theta.Whittaker.RotatedFirstRootRapidDecay
public import DedekindZetaZeroFree.Theta.Profiles.InducedAmplitudeDerivativeBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.EquivariantSmoothSections

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalEisensteinData

open MeasureTheory
open scoped Topology NNReal

section Core

variable {K Gfin H : Type*} [Group K] [Group Gfin] [TopologicalSpace Gfin]
    [AddCommGroup H] [Module ℂ H]

structure CompactTypeStage (ρK : Representation ℂ K H) where
  space : Submodule ℂ H
  finiteDimensional : FiniteDimensional ℂ space
  invariant : CompactProjectors.IsStable ρK space

def finiteLevelTypeStage (ρK : Representation ℂ K H)
    (ρfin : Representation ℂ Gfin H) (smoothSpace : Submodule ℂ H)
    (U : CompactOpenLevel Gfin) (T : CompactTypeStage ρK) : Submodule ℂ H :=
  smoothSpace ⊓ fixedSubmodule ρfin U.toOpenSubgroup.toSubgroup ⊓ T.space

def hcHeckeCore (ρK : Representation ℂ K H) (ρfin : Representation ℂ Gfin H)
    (smoothSpace : Submodule ℂ H) : Submodule ℂ H :=
  ⨆ U : CompactOpenLevel Gfin, ⨆ T : CompactTypeStage ρK,
    finiteLevelTypeStage ρK ρfin smoothSpace U T

end Core

section ScalarOperators

variable {G Q A Y : Type*} [Group G] [MeasurableSpace A] [MeasurableSpace Y]

def EisensteinSummable (rationalLift : Q → G) (fR : G → ℂ) (g : G) : Prop :=
  Summable (fun γ : Q => ‖fR (rationalLift γ * g)‖)

def eisenstein (rationalLift : Q → G) (fR : G → ℂ) (g : G)
    (_h : EisensteinSummable rationalLift fR g) : ℂ :=
  ∑' γ : Q, fR (rationalLift γ * g)

end ScalarOperators

section SmoothTopology

variable {G H : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]

structure DifferentialCompact (G J : Type*) [TopologicalSpace G] where
  compact : Set G
  isCompact : IsCompact compact
  operator : J

instance {J : Type*} (i : DifferentialCompact G J) : CompactSpace i.compact :=
  isCompact_iff_compactSpace.mp i.isCompact

def derivativeRestriction {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (i : DifferentialCompact G J) : H →ₗ[ℂ] C(i.compact, ℂ) where
  toFun h := (D i.operator h).restrict i.compact
  map_add' := by intro x y; ext g; simp
  map_smul' := by intro c x; ext g; simp

def smoothSeminorm {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (i : DifferentialCompact G J) : Seminorm ℂ H :=
  (normSeminorm ℂ C(i.compact, ℂ)).comp (derivativeRestriction D i)

def SmoothPowerSeriesOn {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (z₀ : ℂ) (ρ : ℝ) (a : ℕ → H) (f : ℂ → H) : Prop :=
  ∀ i : DifferentialCompact G J, ∀ r : ℝ, 0 ≤ r → r < ρ →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N, ∀ z ∈ Metric.closedBall z₀ r,
      smoothSeminorm D i ((∑ q ∈ Finset.range M, (z - z₀) ^ q • a q) - f z) < ε

def SmoothHolomorphicOn {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (f : ℂ → H) (O : Set ℂ) : Prop :=
  ∀ z₀ ∈ O, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z₀ ρ ⊆ O ∧
    ∃ a : ℕ → H, SmoothPowerSeriesOn D z₀ ρ a f

structure SimplePoleGerm {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ)) (f : ℂ → H) where
  radius : ℝ
  radius_pos : 0 < radius
  cleared : ℂ → H
  holomorphic : SmoothHolomorphicOn D cleared (Metric.ball 0 radius)
  clears : ∀ s ∈ Metric.ball 0 radius, s ≠ 0 → cleared s = s • f s

end SmoothTopology

end DedekindZetaZeroFree.KPGlobalEisensteinData

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPGlobalEisensteinData

open MeasureTheory
open scoped Topology NNReal

section Induction

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V]

def modularTwist (B : Subgroup G) (δ : B →* (ℝ≥0)ˣ) (s : ℂ) : B →* ℂ where
  toFun b := Complex.exp (s * (Real.log ((δ b : ℝ≥0) : ℝ) : ℂ))
  map_one' := by simp
  map_mul' a b := by
    have ha : ((δ a : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast (δ a).ne_zero
    have hb : ((δ b : ℝ≥0) : ℝ) ≠ 0 := by exact_mod_cast (δ b).ne_zero
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul ha hb,
      Complex.ofReal_add, mul_add, Complex.exp_add]

def tau (B : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ : B →* (ℝ≥0)ˣ) (s : ℂ) : Representation ℂ B V where
  toFun b := modularTwist B δ s b • τ₀ b
  map_one' := by simp [modularTwist]
  map_mul' a b := by
    ext v
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply,
      map_smul, smul_smul, mul_comm]

def induction (B : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ δhalf : B →* (ℝ≥0)ˣ) (s : ℂ) : Submodule ℂ (G → V) :=
  EqSections B (tau B τ₀ δ s) δhalf

def weylBorel (B : Subgroup G) (w : G) : Subgroup G :=
  B.comap (MulAut.conj w).toMonoidHom

def weylToBorel (B : Subgroup G) (w : G) : weylBorel B w →* B :=
  (((MulAut.conj w).toMonoidHom.comp (Subgroup.subtype (weylBorel B w))).codRestrict B
    (by intro b; exact b.property))

def weylInduction (B : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ δhalf : B →* (ℝ≥0)ˣ) (w : G) (s : ℂ) : Submodule ℂ (G → V) :=
  EqSections (weylBorel B w) ((tau B τ₀ δ s).comp (weylToBorel B w))
    (δhalf.comp (weylToBorel B w))

def compactRestriction (B K : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ δhalf : B →* (ℝ≥0)ˣ) (s : ℂ) :
    induction B τ₀ δ δhalf s →ₗ[ℂ] (K → V) where
  toFun f k := f.val k
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def compactPicture (B K : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ δhalf : B →* (ℝ≥0)ˣ) (s : ℂ) : Submodule ℂ (K → V) :=
  (compactRestriction B K τ₀ δ δhalf s).range

structure FlatSection (B K : Subgroup G) (τ₀ : Representation ℂ B V)
    (δ δhalf : B →* (ℝ≥0)ˣ) where
  profile : K → V
  sectionValue : ∀ s : ℂ, induction B τ₀ δ δhalf s
  flat : ∀ s : ℂ, compactRestriction B K τ₀ δ δhalf s (sectionValue s) = profile

end Induction

section Core

variable {K Gfin H : Type*} [Group K] [Group Gfin] [TopologicalSpace Gfin]
    [AddCommGroup H] [Module ℂ H]

end Core

section ScalarOperators

variable {G Q A Y : Type*} [Group G] [MeasurableSpace A] [MeasurableSpace Y]

def IntertwinerIntegrable (μ : Measure A) (w : G) (n : A → G)
    (fR : G → ℂ) (g : G) : Prop :=
  Integrable (fun x => fR (w * n x * g)) μ

def intertwiner (μ : Measure A) (w : G) (n : A → G)
    (fR : G → ℂ) (g : G) (_h : IntertwinerIntegrable μ w n fR g) : ℂ :=
  ∫ x, fR (w * n x * g) ∂μ

def ConstantTermIntegrable (μ : Measure Y) (orbit : Y → G → ℂ) (g : G) : Prop :=
  Integrable (fun x => orbit x g) μ

def constantTerm (μ : Measure Y) (orbit : Y → G → ℂ) (g : G)
    (_h : ConstantTermIntegrable μ orbit g) : ℂ := ∫ x, orbit x g ∂μ

end ScalarOperators

section SmoothTopology

variable {G H : Type*} [TopologicalSpace G] [AddCommGroup H] [Module ℂ H]

def smoothAutomorphicTopology {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ)) :
    TopologicalSpace H := (SeminormFamily.moduleFilterBasis (smoothSeminorm D)).topology

structure HolomorphicCompactSection {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (core : Submodule ℂ H) (O : Set ℂ) where
  profile : ℂ → H
  in_core : ∀ s ∈ O, profile s ∈ core
  holomorphic : SmoothHolomorphicOn D profile O

structure FlatHolomorphicCompactSection {J : Type*} (D : J → H →ₗ[ℂ] C(G, ℂ))
    (core : Submodule ℂ H) (O : Set ℂ) extends HolomorphicCompactSection D core O where
  fixedProfile : H
  flat : ∀ s ∈ O, profile s = fixedProfile

def residue {J : Type*} {D : J → H →ₗ[ℂ] C(G, ℂ)} {f : ℂ → H}
    (germ : SimplePoleGerm D f) : H := germ.cleared 0

end SmoothTopology

end DedekindZetaZeroFree.KPGlobalEisensteinData

end
end
