module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SixthRootAlignment
public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.PositiveAxisSheetDisintegration

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical Topology
open NumberField MeasureTheory
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev Group (R : PrincipalMellin.ActualRecipe S η) :=
  KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12
abbrev Functions (R : PrincipalMellin.ActualRecipe S η) := Group R → ℂ

def localIdele (R : PrincipalMellin.ActualRecipe S η) (y : R.A.G) :
    KPAdelicCoverRestrictedProduct.Ideles F :=
  (∏ w : InfinitePlace F, KPRationalAdelicSplitting.localIdele F (Sum.inl w) (y.1 w)) *
    ∏ p : R.A.Sf, KPRationalAdelicSplitting.localIdele F (Sum.inr p.val) (y.2 p)
def diagonal (R : PrincipalMellin.ActualRecipe S η) (y : R.A.G) : Group R :=
  KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y)
def fourier (R : PrincipalMellin.ActualRecipe S η)
    (dq : Measure (KPAdditiveQuotient F)) (theta : Functions R) (g : Group R) : ℂ :=
  ∫ q, theta (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ) ∂dq
def upper (R : PrincipalMellin.ActualRecipe S η)
    (dq : Measure (KPAdditiveQuotient F)) (theta : Functions R) (g : Group R) : ℂ :=
  ∫ q, theta (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * g) ∂dq

def upperLieDirection (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) (imaginary : Bool) : w.Completion :=
  if imaginary then
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm Complex.I
  else 1

def upperLieDerivative (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F) (imaginary : Bool) (f : Functions R) : Functions R := fun g =>
  deriv (fun t : ℝ => f (g * KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12
    (KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
        upperLieDirection R w imaginary)))) 0

inductive FlatOperation (R : PrincipalMellin.ActualRecipe S η)
    (K : Subgroup (Group R)) (seed : R.A.UnitQuotient → KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 K) :
    (ℂ → Functions R) → Prop
  | seed (v) : FlatOperation R K seed (seed v).val
  | add {f h} : FlatOperation R K seed f → FlatOperation R K seed h →
      FlatOperation R K seed (fun s => f s + h s)
  | smul (c : ℂ) {f} : FlatOperation R K seed f → FlatOperation R K seed (fun s => c • f s)
  | finite_translate (q : R.A.Sf)
      (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val)) {f} :
      FlatOperation R K seed f → FlatOperation R K seed (fun s =>
        KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
            (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) a)) (f s))
  | complex_derivative (w : InfinitePlace F) (imaginary : Bool) {f} :
      FlatOperation R K seed f → FlatOperation R K seed (fun s => upperLieDerivative R w imaginary (f s))

structure AdmissibleFlatSources (R : PrincipalMellin.ActualRecipe S η) where
  K : Subgroup (Group R)
  iwasawa : KPLiteralRaw.IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K
  flat : R.A.UnitQuotient → KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 K
  finite_companions : Finite R.A.UnitQuotient
  level : KPGlobalTorusFunctionData.FiniteLevel F R.A.zeta12 R.A.primitive_zeta12
  common_level : ∀ v s g u, u ∈ KPGlobalTorusFunctionData.globalLevel
    F R.A.zeta12 R.A.primitive_zeta12 level → (flat v).val s (g * u) = (flat v).val s g
  ordinary : ∀ v s ε g,
    (flat v).val s (KPAdelicCoverRestrictedProduct.pglCentralInjection
      F R.A.zeta12 R.A.primitive_zeta12 ε * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε : ℂ) *
        (flat v).val s g
  exterior_spherical : ∀ v s (p : KPFinitePlace F), p ∉ R.A.Sf →
    ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
    k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
    ∀ g, (flat v).val s (g * KPAdelicCoverRestrictedProduct.scalarQuotient F
      R.A.zeta12 R.A.primitive_zeta12 (KPAdelicCoverRestrictedProduct.localInjection
        F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) = (flat v).val s g
  dq : Measure (KPAdditiveQuotient F)
  quotientHaar : dq.IsAddHaarMeasure
  probability : dq Set.univ = 1

structure Realization (R : PrincipalMellin.ActualRecipe S η)
    (Q : AdmissibleFlatSources R) where
  E : R.A.UnitQuotient → ℂ → C(Group R, ℂ)
  meromorphic : ∀ v g, MeromorphicOn (fun s => E v s g) KPContinuation.spectralDomain
  chamber : ∀ v s, (1 / 3 : ℝ) < s.re → ∀ g,
    E v s g = KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12 Q.K (Q.flat v) s g
  radius : ℝ
  radius_pos : 0 < radius
  disc_domain : Metric.ball (0 : ℂ) radius ⊆ KPContinuation.spectralDomain
  cleared : R.A.UnitQuotient → ℂ → Functions R
  clears : ∀ v s, s ∈ Metric.ball (0 : ℂ) radius → s ≠ 0 → cleared v s = s • (E v s : Functions R)
  smooth : ∀ v s, s ∈ Metric.ball (0 : ℂ) radius →
    KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (cleared v s)
  common_cleared_level : ∀ v s, s ∈ Metric.ball (0 : ℂ) radius → ∀ g u,
    u ∈ KPGlobalTorusFunctionData.globalLevel F R.A.zeta12 R.A.primitive_zeta12 Q.level →
      cleared v s (g * u) = cleared v s g
  analytic : ∀ v g, AnalyticOnNhd ℂ (fun s => cleared v s g) (Metric.ball (0 : ℂ) radius)
  coefficients : R.A.UnitQuotient → ℕ → Functions R
  coefficients_smooth : ∀ v n, KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (coefficients v n)
  compact_smooth_taylor : ∀ v g (m : ℕ) (C : Set (KPGlobalResidualConstruction.ArchCoordinates F)),
    IsCompact C → C ⊆ KPGlobalResidualConstruction.archDomain F →
    ∀ r : ℝ, 0 < r → r < radius → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ M : ℕ, N ≤ M → ∀ s : ℂ, ‖s‖ ≤ r → ∀ x ∈ C,
      ‖iteratedFDeriv ℝ m (fun x =>
        cleared v s (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 x) -
        ∑ n ∈ Finset.range M, s ^ n * coefficients v n
          (g * KPGlobalResidualConstruction.archChart F R.A.zeta12 R.A.primitive_zeta12 x)) x‖ < ε
  automorphic : ∀ v, KPLiteralRaw.Automorphic F R.A.zeta12 R.A.primitive_zeta12 (cleared v 0)

namespace Realization
def theta {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
    (T : Realization R Q) (v : R.A.UnitQuotient) : Functions R := T.cleared v 0
end Realization

structure Packet (R : PrincipalMellin.ActualRecipe S η) (Q : AdmissibleFlatSources R) where
  seed : R.A.UnitQuotient → KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K
  seed_spherical : ∀ v s (p : KPFinitePlace F), p ∉ R.A.Sf →
    ∀ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p),
    k ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) →
    ∀ g, (seed v).val s (g * KPAdelicCoverRestrictedProduct.scalarQuotient F
      R.A.zeta12 R.A.primitive_zeta12 (KPAdelicCoverRestrictedProduct.localInjection
        F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p) k)) = (seed v).val s g
  operations : ∀ v, FlatOperation R Q.K seed (Q.flat v).val
  v₀ : InfinitePlace F
  cutoff : ∀ p : R.A.Sf, Subgroup (p.val.adicCompletion F)ˣ
  cutoff_open : ∀ p, IsOpen (cutoff p : Set (p.val.adicCompletion F)ˣ)
  cutoff_compact : ∀ p, IsCompact (cutoff p : Set (p.val.adicCompletion F)ˣ)
  cutoff_sixth : ∀ p z, z ∈ cutoff p → ∃ t : (p.val.adicCompletion F)ˣ, t ^ 6 = z
  exponents : R.A.UnitQuotient → InfinitePlace F → ℤ
  first_root : ∀ v w, exponents v w = 1 ∨ exponents v w = -1
  branch : R.A.UnitQuotient → R.A.G →* ℂ
  branch_global : ∀ v y, branch v y =
    (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id y : ℂ) *
      R.σ ((R.A.H_S (R.A.diagonal (R.probe.unitReps.representative v).val) y : Fˣ) : F)
  branch_exact : ∀ v y, (∀ p : R.A.Sf, y.2 p ∈ cutoff p) → branch v y =
    ∏ w : InfinitePlace F,
      DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (y.1 w : w.Completion)) ^ exponents v w
  cutoff_kernel : ∀ v y, (∀ w, y.1 w = 1) →
    (∀ p : R.A.Sf, y.2 p ∈ cutoff p) → branch v y = 1

namespace Packet
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
def scale (_P : Packet R Q) (_w : InfinitePlace F) : ℝ := 4 * Real.pi
theorem scale_pos (P : Packet R Q) (w : InfinitePlace F) : 0 < P.scale w := by
  dsimp [scale]; positivity
def forwardProfile (P : Packet R Q) (v : R.A.UnitQuotient) (y : R.A.G) : ℂ :=
  (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
    ∏ w : InfinitePlace F, ((‖(y.1 w : w.Completion)‖ ^ 2 : ℝ) : ℂ) *
      DHCubic.angular (InfinitePlace.Completion.extensionEmbedding w (y.1 w : w.Completion)) ^ P.exponents v w *
      (KThird (P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2)) : ℂ)
def positiveSheet (P : Packet R Q) (x : ThetaProfileHaarSheets.PositiveAxis) : ℝ := by
  letI : MeasurableSpace R.A.G1 := borel _
  exact MeasureTheory.integral R.probe.domain.measure (fun z : R.A.G1 =>
    let y := z.val * R.A.radialSection x.val x.property
    (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
      ∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2 *
        KThird (P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2)))
def A₀ (P : Packet R Q) : ℝ := ∏ w : InfinitePlace F, (4 / P.scale w ^ 2)

theorem A₀_pos (P : Packet R Q) : 0 < P.A₀ := by
  unfold A₀
  exact Finset.prod_pos (fun w _ => div_pos (by norm_num) (sq_pos_of_pos (P.scale_pos w)))

def C₀ (P : Packet R Q) : ℝ :=
  (∫ x : ThetaProfileHaarSheets.PositiveAxis, P.positiveSheet x ∂ThetaProfileHaarSheets.positiveHaar) /
    (Real.Gamma (5 / 6) * Real.Gamma (7 / 6)) ^ Fintype.card (InfinitePlace F)
def kernel (P : Packet R Q) (x : ℝ) : ℂ :=
  thetaProfileGaussianKernel P.C₀ P.A₀ (Fintype.card (InfinitePlace F)) x

theorem forwardProfile_one_ne_zero (P : Packet R Q) (v : R.A.UnitQuotient) :
    P.forwardProfile v 1 ≠ 0 := by
  unfold forwardProfile
  have hcut : ∀ p : R.A.Sf, (1 : R.A.G).2 p ∈ P.cutoff p := fun p => (P.cutoff p).one_mem
  rw [if_pos hcut]
  apply mul_ne_zero one_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  have he : InfinitePlace.Completion.extensionEmbedding w ((1 : R.A.G).1 w : w.Completion) = 1 := by simp
  have hn : ‖((1 : R.A.G).1 w : w.Completion)‖ = 1 := by simp
  rw [he, hn]
  simp only [one_pow, Real.sqrt_one, mul_one, Complex.ofReal_one]
  apply mul_ne_zero
  · apply mul_ne_zero one_ne_zero
    apply zpow_ne_zero
    simp [DHCubic.angular]
  · exact Complex.ofReal_ne_zero.mpr (KThird_pos _ (P.scale_pos w)).ne'
end Packet

namespace Realization
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
def sheetIntegrand (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (κ : R.A.V) (y : R.A.G) : ℂ :=
  (if κ * (QuotientGroup.mk' R.A.sixthPowers y)⁻¹ ∈ R.probe.correction.B then 1 else 0) *
    (R.σ ((R.probe.correction.H κ (QuotientGroup.mk' R.A.sixthPowers y) : Fˣ) : F) ^ 2)⁻¹ *
    P.branch v y * fourier R Q.dq (T.theta v)
      (diagonal R y * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)
def sheet (T : Realization R Q) (P : Packet R Q)
    (v : R.A.UnitQuotient) (κ : R.A.V) (x : ThetaProfileHaarSheets.PositiveAxis) : ℂ := by
  letI : MeasurableSpace R.A.G1 := borel _
  exact MeasureTheory.integral R.probe.domain.measure (fun y : R.A.G1 =>
    T.sheetIntegrand P v κ (y.val * R.A.radialSection x.val x.property))
def H (T : Realization R Q) (P : Packet R Q) (v : R.A.UnitQuotient) (κ : R.A.V) (x : ℝ) : ℂ :=
  if hx : 0 < x then ∫ t : ThetaProfileHaarSheets.PositiveAxis,
    P.kernel t.val * T.sheet P v κ ⟨x / t.val, div_pos hx t.property⟩ ∂ThetaProfileHaarSheets.positiveHaar else 0
end Realization
end DedekindZetaZeroFree.MomentSources

end
