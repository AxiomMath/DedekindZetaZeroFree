module

public import DedekindZetaZeroFree.Eisenstein.Induction.Genuineness
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalInvariance
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations

@[expose] public section

noncomputable section
open scoped Topology
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy

theorem clearing_value_eq_on (A B a b : ℂ → ℂ) (c : ℂ)
    (U V : Set ℂ) (hU : IsOpen U) (hconn : IsConnected U)
    (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    (hA : MeromorphicOn A U) (hB : MeromorphicOn B U)
    (hagree : ∀ s ∈ V, A s = c * B s)
    (ra rb : ℝ) (hra : 0 < ra) (hrb : 0 < rb)
    (hball : Metric.ball (0 : ℂ) ra ⊆ U)
    (ha : AnalyticOnNhd ℂ a (Metric.ball (0 : ℂ) ra))
    (hb : AnalyticOnNhd ℂ b (Metric.ball (0 : ℂ) rb))
    (hca : ∀ s ∈ Metric.ball (0 : ℂ) ra, s ≠ 0 → a s = s * A s)
    (hcb : ∀ s ∈ Metric.ball (0 : ℂ) rb, s ≠ 0 → b s = s * B s) :
    a 0 = c * b 0 := by
  obtain ⟨z, hz⟩ := hne
  have hmul : MeromorphicOn (fun s => c * B s) U :=
    (MeromorphicOn.const c).mul hB
  have hzEq : A =ᶠ[𝓝[≠] z] (fun s => c * B s) :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hV.mem_nhds hz)).mono
      (fun s hs => hagree s hs)
  have hzTop : meromorphicOrderAt (A - fun s => c * B s) z = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hzEq] with s hs
    simpa using sub_eq_zero.mpr hs
  have h0U : (0 : ℂ) ∈ U := hball (by simpa using hra)
  have h0Top := (hA.sub hmul).meromorphicOrderAt_eq_top_of_isPreconnected
    hconn.isPreconnected (hVU hz) h0U hzTop
  have hEq : A =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => c * B s) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp h0Top] with s hs
    exact sub_eq_zero.mp hs
  have hma : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ Metric.ball (0 : ℂ) ra :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa using hra))
  have hmb : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ∈ Metric.ball (0 : ℂ) rb :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.isOpen_ball.mem_nhds (by simpa using hrb))
  have hab : a =ᶠ[𝓝[≠] (0 : ℂ)] (fun s => c * b s) := by
    filter_upwards [hEq, hma, hmb, self_mem_nhdsWithin] with s hs hsa hsb hs0
    have hne0 : s ≠ 0 := by simpa using hs0
    rw [hca s hsa hne0, hcb s hsb hne0, hs]
    ring
  exact (((ha 0 (by simpa using hra)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (continuousAt_const.mul (hb 0 (by simpa using hrb)).continuousAt)).mp hab).eq_of_nhds

open scoped NumberField Classical
open NumberField MeasureTheory ValuativeRel KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem residue_covariance (K : Subgroup (G F ζ hζ))
    (E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E cleared) (f : Flat F ζ hζ K)
    (g₁ g₂ : G F ζ hζ) (c : ℂ)
    (hchamber : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
      eisenstein F ζ hζ K f s g₁ = c * eisenstein F ζ hζ K f s g₂) :
    cleared f 0 g₁ = c * cleared f 0 g₂ := by
  obtain ⟨U, r, hU, hconn, hchamberU, hr, hball, hmer, hclear, hanal⟩ := hGerm.2 f
  refine clearing_value_eq_on (fun s => E f s g₁) (fun s => E f s g₂)
    (fun s => cleared f s g₁) (fun s => cleared f s g₂) c U
    {s : ℂ | (1 : ℝ) / 3 < s.re} hU hconn
    (isOpen_lt continuous_const Complex.continuous_re)
    ⟨1, by norm_num⟩ hchamberU (hmer g₁) (hmer g₂)
    ?_ r r hr hr hball (hanal g₁) (hanal g₂) ?_ ?_
  · intro s hs
    rw [hGerm.1 f s hs g₁, hGerm.1 f s hs g₂]
    exact hchamber s hs
  · intro s hs hne
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (hclear s hs hne) g₁
  · intro s hs hne
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun (hclear s hs hne) g₂

theorem residue_rational (K : Subgroup (G F ζ hζ))
    (E cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hGerm : ExceptionalGerm F ζ hζ K E cleared) (f : Flat F ζ hζ K)
    (γ : Matrix.ProjGenLinGroup (Fin 2) F) (g : G F ζ hζ) :
    cleared f 0 (rationalLift F ζ hζ γ * g) = cleared f 0 g := by
  simpa using residue_covariance F ζ hζ K E cleared hGerm f
    (rationalLift F ζ hζ γ * g) g 1 (by
      intro s hs
      simpa using eisenstein_rational F ζ hζ K f s hs γ g)

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy

end
