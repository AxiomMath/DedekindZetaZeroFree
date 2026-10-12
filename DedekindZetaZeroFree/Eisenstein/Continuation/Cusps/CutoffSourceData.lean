module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.IncomingCasimirEigenfunctions
public import DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPCutoffSource

open scoped ContDiff Topology
open MeasureTheory

structure SmoothCuspCutoff (T : ℝ) where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  zero_below : ∀ t, t ≤ T → toFun t = 0
  one_above : ∀ t, T + 1 ≤ t → toFun t = 1

def radialCutoff (d : ℕ) (χ : ℝ → ℝ) (s b : ℂ) (t : ℝ) : ℂ :=
  (χ t : ℂ) * KPIncomingCasimir.heightFactor d s t * b

def radialCommutator (d : ℕ) (χ : ℝ → ℝ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-((d : ℂ)⁻¹) * ((deriv (deriv χ) t : ℝ) : ℂ) + 2 * ((deriv χ t : ℝ) : ℂ)) * w t -
    2 * (d : ℂ)⁻¹ * ((deriv χ t : ℝ) : ℂ) * deriv w t

def incomingCommutatorMultiplier (d : ℕ) (χ : ℝ → ℝ)
    (s : ℂ) (t : ℝ) : ℂ :=
  -((d : ℂ)⁻¹) * ((deriv (deriv χ) t : ℝ) : ℂ) + 2 * ((deriv χ t : ℝ) : ℂ) -
    2 * ((4 : ℂ) / 3 + 2 * s) * ((deriv χ t : ℝ) : ℂ)

theorem radialCutoff_smooth (d : ℕ) {T : ℝ} (χ : SmoothCuspCutoff T) (s b : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialCutoff d χ.toFun s b) := by
  unfold radialCutoff KPIncomingCasimir.heightFactor
  have hcast : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := by
    have hcoe : (fun t : ℝ => (t : ℂ)) = Complex.ofRealCLM := by
      funext t
      exact (Complex.ofRealCLM_apply t).symm
    rw [hcoe]
    exact Complex.ofRealCLM.contDiff
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (χ.toFun t : ℂ)) :=
    hcast.comp χ.smooth
  exact (hχ.mul (Complex.contDiff_exp.comp
    ((contDiff_const.mul hcast) : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => ((d : ℂ) * ((4 : ℂ) / 3 + 2 * s)) * (t : ℂ))))).mul contDiff_const

private theorem wave_hasDerivAt (d : ℕ) (s b : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => KPIncomingCasimir.heightFactor d s u * b)
      ((d : ℂ) * ((4 : ℂ) / 3 + 2 * s) *
        (KPIncomingCasimir.heightFactor d s t * b)) t := by
  unfold KPIncomingCasimir.heightFactor
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, one_mul,
    mul_assoc, mul_comm, mul_left_comm] using
    (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
      ((d : ℂ) * ((4 : ℂ) / 3 + 2 * s))).cexp.mul_const b)

private theorem cutoff_hasDerivAt {T : ℝ} (χ : SmoothCuspCutoff T) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (χ.toFun u : ℂ)) ((deriv χ.toFun t : ℝ) : ℂ) t := by
  exact ((χ.smooth.differentiable (by simp)) t).hasDerivAt.ofReal_comp

theorem radialCutoff_equation (d : ℕ) (hd : 0 < d) {T : ℝ}
    (χ : SmoothCuspCutoff T) (s b : ℂ) (t : ℝ) :
    KPIncomingCasimir.radialLaplacian d (radialCutoff d χ.toFun s b) t -
        KPContinuation.spectralCoordinate (d : ℤ) s * radialCutoff d χ.toFun s b t =
      incomingCommutatorMultiplier d χ.toFun s t *
        (KPIncomingCasimir.heightFactor d s t * b) := by
  let c : ℂ := (d : ℂ) * ((4 : ℂ) / 3 + 2 * s)
  let w : ℝ → ℂ := fun u => KPIncomingCasimir.heightFactor d s u * b
  have hw (u : ℝ) : HasDerivAt w (c * w u) u := wave_hasDerivAt d s b u
  have hχ' (u : ℝ) : HasDerivAt (fun v : ℝ => ((deriv χ.toFun v : ℝ) : ℂ))
      ((deriv (deriv χ.toFun) u : ℝ) : ℂ) u :=
    (((χ.smooth.of_le (show (2 : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).differentiable_deriv_two)
      u).hasDerivAt.ofReal_comp
  have hrad : radialCutoff d χ.toFun s b = fun u => (χ.toFun u : ℂ) * w u := by
    funext u
    exact mul_assoc _ _ _
  have hfirst : deriv (radialCutoff d χ.toFun s b) =
      fun u => ((deriv χ.toFun u : ℝ) : ℂ) * w u + (χ.toFun u : ℂ) * (c * w u) := by
    funext u
    rw [hrad]
    exact ((cutoff_hasDerivAt χ u).mul (hw u)).deriv
  have hsecond : deriv (deriv (radialCutoff d χ.toFun s b)) t =
      ((deriv (deriv χ.toFun) t : ℝ) : ℂ) * w t +
        ((deriv χ.toFun t : ℝ) : ℂ) * (c * w t) +
        (((deriv χ.toFun t : ℝ) : ℂ) * (c * w t) +
          (χ.toFun t : ℂ) * (c * (c * w t))) := by
    rw [hfirst]
    exact (((hχ' t).mul (hw t)).add
      ((cutoff_hasDerivAt χ t).mul ((hw t).const_mul c))).deriv
  unfold KPIncomingCasimir.radialLaplacian
  rw [hsecond, hfirst]
  simp only [incomingCommutatorMultiplier, radialCutoff,
    KPContinuation.spectralCoordinate, Int.cast_natCast]
  dsimp [w, c]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  field_simp
  ring

theorem incoming_commutator_support (d : ℕ) {T : ℝ}
    (χ : SmoothCuspCutoff T) (s b : ℂ) :
    tsupport (fun t => incomingCommutatorMultiplier d χ.toFun s t *
      (KPIncomingCasimir.heightFactor d s t * b)) ⊆ Set.Icc T (T + 1) := by
  apply closure_minimal _ isClosed_Icc
  apply Function.support_subset_iff'.mpr
  intro t ht
  have hconst : ∃ c : ℝ, χ.toFun =ᶠ[𝓝 t] (fun _ => c) := by
    by_cases hlow : t < T
    · refine ⟨0, ?_⟩
      filter_upwards [Iio_mem_nhds hlow] with u hu
      exact χ.zero_below u (le_of_lt hu)
    · have hhigh : T + 1 < t := by
        simp only [Set.mem_Icc, not_and_or, not_le] at ht
        rcases ht with ht | ht
        · exact (hlow ht).elim
        · exact ht
      refine ⟨1, ?_⟩
      filter_upwards [Ioi_mem_nhds hhigh] with u hu
      exact χ.one_above u (le_of_lt hu)
  obtain ⟨c, hc⟩ := hconst
  have hfirst : deriv χ.toFun t = 0 := by
    simpa only [deriv_const] using hc.deriv_eq
  have hsecond : deriv (deriv χ.toFun) t = 0 := by
    simpa only [deriv_const', deriv_const] using hc.deriv.deriv_eq
  simp [incomingCommutatorMultiplier, hfirst, hsecond]

section AllCusps
variable {X A H : Type*} [Fintype A] [AddCommGroup H] [Module ℂ H]

def cutoffSum (ends : A → Set X) (height : A → X → ℝ)
    (χ : A → ℝ → ℝ) (realize : ℂ → H →ₗ[ℂ] (X → ℂ))
    (f : ℂ → H) (s : ℂ) (x : X) : ℂ := by
  classical
  exact ∑ a, if x ∈ ends a then (χ a (height a x) : ℂ) * realize s (f s) x else 0

def commutatorSum (d : ℕ) (ends : A → Set X) (height : A → X → ℝ)
    (χ : A → ℝ → ℝ) (realize : ℂ → H →ₗ[ℂ] (X → ℂ))
    (f : ℂ → H) (s : ℂ) (x : X) : ℂ := by
  classical
  exact ∑ a, if x ∈ ends a then
    incomingCommutatorMultiplier d (χ a) s (height a x) * realize s (f s) x else 0

def closedCollars [TopologicalSpace X] (ends : A → Set X)
    (height : A → X → ℝ) (T : ℝ) : Set X :=
  ⋃ a, closure {x | x ∈ ends a ∧ height a x ∈ Set.Icc T (T + 1)}

theorem cutoffSum_at_every_cusp {T : ℝ} (ends : A → Set X)
    (hdisjoint : Pairwise (fun a b => Disjoint (ends a) (ends b)))
    (height : A → X → ℝ) (χ : A → SmoothCuspCutoff T)
    (realize : ℂ → H →ₗ[ℂ] (X → ℂ)) (f : ℂ → H)
    (a : A) (s : ℂ) (x : X) (hx : x ∈ ends a) (ht : T + 1 ≤ height a x) :
    cutoffSum ends height (fun a => (χ a).toFun) realize f s x = realize s (f s) x := by
  classical
  unfold cutoffSum
  rw [Finset.sum_eq_single a]
  · simp [hx, (χ a).one_above _ ht]
  · intro b _ hba
    have hxb : x ∉ ends b := by
      intro hb
      exact Set.disjoint_left.mp (hdisjoint hba) hb hx
    simp [hxb]
  · simp

end AllCusps

def ChartSmoothHolomorphicOn {n : ℕ} (B : KPContLocalNorm.LocalBall n)
    (g : ℂ → KPContLocalNorm.Space n → ℂ) (Ω : Set ℂ) : Prop :=
  (∀ s ∈ Ω, ContDiffOn ℝ (⊤ : ℕ∞) (g s) B.carrier) ∧
  ∀ (K : Set (KPContLocalNorm.Space n)) (hcompact : IsCompact K), K ⊆ B.carrier →
    ∀ m : ℕ,
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
      ∃ j : ℂ → KPContLocalNorm.CompactJets K m,
        DifferentiableOn ℂ j Ω ∧
        ∀ s ∈ Ω, ∀ α, ∀ x : K, j s α x =
          KPContLocalNorm.coordinateDerivative α (g s) x

def ChartSobolevHolomorphicOn {n : ℕ} (B : KPContLocalNorm.LocalBall n)
    (g : ℂ → KPContLocalNorm.Space n → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ k : ℕ, ∃ v : ℂ → (KPContLocalNorm.MultiIndex n k → KPContLocalNorm.BallL2 B),
    DifferentiableOn ℂ v Ω ∧
    ∀ s ∈ Ω, ∀ α,
      MemLp (KPContLocalNorm.coordinateDerivative α (g s)) 2
        (volume.restrict B.carrier) ∧
      (fun x => v s α x) =ᵐ[volume.restrict B.carrier]
        KPContLocalNorm.coordinateDerivative α (g s)

end DedekindZetaZeroFree.KPCutoffSource

end
