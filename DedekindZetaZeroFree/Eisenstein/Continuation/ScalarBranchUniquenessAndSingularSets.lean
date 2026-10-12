module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SelectedPoleSets
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.LocallyFinitePoleGeometry

@[expose] public section

noncomputable section
open scoped Topology
open Filter
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open ResidueContinuity.ScalarSourcePoleGeometry
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R} {B : JointRootAlignedSources R N}
variable {v : R.A.UnitQuotient}

theorem SelectedScalarBranch.analyticAt_chamber
    (D : SelectedScalarBranch R B v) {s : ℂ} (hs : (1 / 3 : ℝ) < s.re)
    (g : Group R) : AnalyticAt ℂ (fun z => D.E z g) s := by
  have hraw := KPLiteralExceptionalResidue.LiteralChamberAnalytic.raw_chamber_analytic
    F R.A.zeta12 R.A.primitive_zeta12 B.sources.K B.sources.iwasawa
    (B.sources.flat v) s hs g
  have heq : (fun z => D.E z g) =ᶠ[𝓝 s]
      (fun z => KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) z g) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact D.chamber z hz g
  exact hraw.congr heq.symm

theorem SelectedScalarBranch.analyticAt_of_germ
    (D : SelectedScalarBranch R B v) (g : Group R) {s : ℂ}
    (hs : s ∈ KPContinuation.spectralDomain) {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a s)
    (he : (fun z => D.E z g) =ᶠ[𝓝[≠] s] a) :
    AnalyticAt ℂ (fun z => D.E z g) s := by
  have hn : (fun z => D.E z g) =ᶠ[𝓝 s] a :=
    ((D.normal g hs).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      ha.meromorphicNFAt).mp he
  exact ha.congr hn.symm

theorem selectedPoleSet_of_regular (D : SelectedScalarBranch R B v)
    (P : Set ℂ) (hP : P ⊆ KPContinuation.spectralDomain)
    (hiso : IsolatedPoles KPContinuation.spectralDomain P)
    (hreg : ∀ s ∈ KPContinuation.spectralDomain, s ∉ P →
      ∀ g, AnalyticAt ℂ (fun z => D.E z g) s) :
    Nonempty (SelectedPoleSet D) := by
  let Q : Set ℂ := P \ {s : ℂ | (1 / 3 : ℝ) < s.re}
  refine ⟨{
    poles := Q
    subset := fun s hs => hP hs.1
    isolated := hiso.mono (fun _ hs => hs.1)
    chamber_disjoint := ?_
    regular := ?_ }⟩
  · intro s hs hq
    exact hq.2 hs
  · intro s hs hq g
    by_cases hc : (1 / 3 : ℝ) < s.re
    · exact D.analyticAt_chamber hc g
    · exact hreg s hs (fun hp => hq ⟨hp, hc⟩) g

end DedekindZetaZeroFree.ThetaExpansion

end
