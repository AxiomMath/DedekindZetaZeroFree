module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.Scales
public import DedekindZetaZeroFree.Moments.Reflected.RankOneExpansion
public import DedekindZetaZeroFree.Nonvanishing.Mellin.TripleMellinInitialEstimates

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

noncomputable section

open scoped NumberField Classical

structure FixedData {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus) where
  recipe : PrincipalMellin.ActualRecipe S η
  rootAligned : MomentSources.RootAligned recipe
  source : MomentSources.SelectedMomentSource recipe

theorem FixedData.exists {F : Type} [Field F] [NumberField F]
    (S : SArithmeticData F) (η : RayClassCharacter F S.modulus)
    (hη : η.IsPrincipal) (P : PrincipalRayHeckeData F S.modulus η) :
    Nonempty (FixedData S η) := by
  obtain ⟨R, hR, ⟨N⟩⟩ := ThetaExpansion.selected_rank_one_expansion S η hη P
  exact ⟨⟨R, hR, N⟩⟩

private theorem recipe_M_estimates {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) :
    DifferentiableOn ℂ R.W.M {z : ℂ | 0 < z.re} ∧
    (∀ (σ0 σ1 B : ℝ), 0 < σ0 → σ0 ≤ σ1 → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc σ0 σ1, ∀ τ : ℝ,
        ‖R.W.M ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-B)) := by
  have hne : ∀ v, R.probe.finiteTrace v ≠ 1 := by
    intro v he
    obtain ⟨x, hx⟩ := R.probe.finiteTrace_ne_one R.A R.σ R.target R.traceBad v
    exact hx (by rw [he]; rfl)
  let w : NumberField.InfinitePlace F := Classical.choice inferInstance
  obtain ⟨dt, hdt, hdis, hsheet⟩ := probe_sheet_mellin_estimates F R.A
    R.probe.finiteTrace R.probe.continuousTrace R.probe.traceCompatible hne
    R.probe.additiveMeasure R.probe.multiplicativeMeasure
    R.probe.additiveHaar R.probe.multiplicativeHaar w
    R.probe.W0 R.probe.W1 R.probe.annular R.probe.compactSupport R.probe.supportUnits
  rcases hsheet with ⟨_, _, _, hM, hMd, _, _, _⟩
  exact ⟨hM, hMd⟩

namespace FixedData

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

abbrev A : SArithmeticData F := D.recipe.A

def context : D.recipe.A.GeneralArithmeticContext D.recipe.σ D.recipe.target
    D.recipe.traceBad :=
  PrincipalMellinGrowth.recipeContext D.recipe

structure Row where

  toFrequency : CorrectionFactors.Frequency D.context

  isRep : ∃ h : toFrequency.u ≠ 0,
    (⟨toFrequency.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈ D.recipe.probe.frequencies.reps

namespace Row

variable {D}

abbrev u (r : D.Row) : D.recipe.A.R := r.toFrequency.u

instance : Coe D.Row (CorrectionFactors.Frequency D.context) := ⟨Row.toFrequency⟩

abbrev generates (r : D.Row) := r.toFrequency.generates

abbrev allowed (r : D.Row) := r.toFrequency.allowed

abbrev sixthFree (r : D.Row) := r.toFrequency.sixthFree

abbrev j (r : D.Row) := r.toFrequency.j

abbrev unitPart (r : D.Row) := r.toFrequency.unitPart

abbrev theta (r : D.Row) := r.toFrequency.theta

theorem ext {r r' : D.Row} (h : r.toFrequency = r'.toFrequency) : r = r' := by
  cases r; cases r'; cases h; rfl

theorem toFrequency_injective : Function.Injective (Row.toFrequency (D := D)) :=
  fun _ _ h => ext h

private theorem frequency_ext_of_u_ideal {f g : CorrectionFactors.Frequency D.context}
    (hu : f.u = g.u) (hI : f.ideal = g.ideal) : f = g := by
  obtain ⟨u, I, a, b, c⟩ := f
  obtain ⟨u', I', a', b', c'⟩ := g
  have hu' : u = u' := hu
  have hI' : I = I' := hI
  subst hu'
  subst hI'
  rfl

theorem u_injective : Function.Injective (Row.u (D := D)) := by
  intro r r' h
  have hu : r.toFrequency.u = r'.toFrequency.u := h
  have hI : r.toFrequency.ideal = r'.toFrequency.ideal := by
    apply D.recipe.A.exteriorIdealEquiv.injective
    apply Subtype.ext
    rw [D.recipe.A.exteriorIdealEquiv_apply, D.recipe.A.exteriorIdealEquiv_apply,
      ← r.toFrequency.generates.2, ← r'.toFrequency.generates.2]
    exact congrArg (fun x : D.recipe.A.R => Ideal.span {x}) hu
  exact ext (frequency_ext_of_u_ideal hu hI)

theorem u_mem_reps (r : D.Row) :
    ∃ h : r.u ≠ 0, (⟨r.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈
      D.recipe.probe.frequencies.reps := r.isRep

theorem u_ne_zero (r : D.Row) : r.u ≠ 0 := r.isRep.choose

theorem u_unique {r r' : D.Row} (h : r.u = r'.u) : r = r' := u_injective h

end Row

def q (u : D.Row) : ℝ :=
  (FiniteTransform.exteriorNorm D.recipe.A.R.toSubring u.u : ℝ)

def inducers (u : D.Row) : FrequencyCharacterMasks.PrimitiveInducers u.toFrequency :=
  (MaskedHeckeMeromorphic.masked_hecke_meromorphic u.toFrequency).choose

def rowContinuation (u : D.Row) (i : MaskedHeckeMeromorphic.Row) :
    MaskedHeckeMeromorphic.RowContinuation u.toFrequency (D.inducers u) i :=
  ((MaskedHeckeMeromorphic.masked_hecke_meromorphic u.toFrequency).choose_spec i).some

def psi (u : D.Row) : Ideal (𝓞 F) → ℂ :=
  FrequencyCharacterMasks.plusCoefficient u.toFrequency

def lam (u : D.Row) : Ideal (𝓞 F) → ℂ :=
  FrequencyCharacterMasks.minusCoefficient u.toFrequency

def omega (u : D.Row) : Detector.PrimitiveFrequencyCharacter F :=
  (D.inducers u).minus

def LpsiRaw (u : D.Row) (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.incompleteL u.toFrequency MaskedHeckeMeromorphic.Row.plus s

def LlamRaw (u : D.Row) (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.incompleteL u.toFrequency MaskedHeckeMeromorphic.Row.minus s

def Lpsi (u : D.Row) (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.quotientRepresentative u.toFrequency (D.inducers u)
    MaskedHeckeMeromorphic.Row.plus (D.rowContinuation u .plus).J s

def Llam (u : D.Row) (s : ℂ) : ℂ :=
  MaskedHeckeMeromorphic.quotientRepresentative u.toFrequency (D.inducers u)
    MaskedHeckeMeromorphic.Row.minus (D.rowContinuation u .minus).J s

abbrev rowDeletionSet (u : D.Row) (i : MaskedHeckeMeromorphic.Row) :
    Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :=
  MaskedHeckeMeromorphic.deletionSet u.toFrequency i

theorem Lpsi_eq_raw (u : D.Row) (s : ℂ) (hs : 1 < s.re) : D.Lpsi u s = D.LpsiRaw u s :=
  ((D.rowContinuation u .plus).regular_equality s hs).symm

theorem Llam_eq_raw (u : D.Row) (s : ℂ) (hs : 1 < s.re) : D.Llam u s = D.LlamRaw u s :=
  ((D.rowContinuation u .minus).regular_equality s hs).symm

theorem Lpsi_hasSum (u : D.Row) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 F) => D.psi u I * (Ideal.absNorm I : ℂ) ^ (-s)) (D.Lpsi u s) :=
  (D.rowContinuation u .plus).series s hs

theorem Llam_hasSum (u : D.Row) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 F) => D.lam u I * (Ideal.absNorm I : ℂ) ^ (-s)) (D.Llam u s) :=
  (D.rowContinuation u .minus).series s hs

theorem Lpsi_eq_J_mask (u : D.Row) (s : ℂ) :
    D.Lpsi u s = (D.rowContinuation u .plus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .plus)
        (fun p => (D.inducers u).plus.character p.asIdeal) s /
      (s - 1) ^ MaskedHeckeMeromorphic.poleIndicator (D.inducers u).plus := rfl

theorem Llam_eq_J_mask (u : D.Row) (s : ℂ) :
    D.Llam u s = (D.rowContinuation u .minus).J s *
      Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .minus)
        (fun p => (D.omega u).character p.asIdeal) s /
      (s - 1) ^ MaskedHeckeMeromorphic.poleIndicator (D.omega u) := rfl

theorem Lpsi_meromorphicOn (u : D.Row) : MeromorphicOn (D.Lpsi u) {s : ℂ | 0 < s.re} :=
  (D.rowContinuation u .plus).meromorphic_germs

theorem Llam_meromorphicOn (u : D.Row) : MeromorphicOn (D.Llam u) {s : ℂ | 0 < s.re} :=
  (D.rowContinuation u .minus).meromorphic_germs

theorem Lpsi_mask_ne_zero (u : D.Row) (s : ℂ) (hs : 0 < s.re) :
    Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .plus)
      (fun p => (D.inducers u).plus.character p.asIdeal) s ≠ 0 :=
  (D.rowContinuation u .plus).B_nowhere_zero s hs

theorem Llam_mask_ne_zero (u : D.Row) (s : ℂ) (hs : 0 < s.re) :
    Detector.finiteEulerDeletionMask F (D.rowDeletionSet u .minus)
      (fun p => (D.omega u).character p.asIdeal) s ≠ 0 :=
  (D.rowContinuation u .minus).B_nowhere_zero s hs

theorem Lpsi_analyticOnNhd (u : D.Row) :
    AnalyticOnNhd ℂ (D.Lpsi u) ({s : ℂ | 0 < s.re} \ {1}) := by
  intro s hs
  have hJ := (D.rowContinuation u .plus).J_holomorphic s hs.1
  have hB := (D.rowContinuation u .plus).B_holomorphic s hs.1
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have hp : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ MaskedHeckeMeromorphic.poleIndicator
      (D.inducers u).plus) s :=
    ((analyticAt_id.sub analyticAt_const).pow _)
  exact (hJ.mul hB).div hp (pow_ne_zero _ hne)

theorem Llam_analyticOnNhd (u : D.Row) :
    AnalyticOnNhd ℂ (D.Llam u) ({s : ℂ | 0 < s.re} \ {1}) := by
  intro s hs
  have hJ := (D.rowContinuation u .minus).J_holomorphic s hs.1
  have hB := (D.rowContinuation u .minus).B_holomorphic s hs.1
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have hp : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ MaskedHeckeMeromorphic.poleIndicator
      (D.omega u)) s :=
    ((analyticAt_id.sub analyticAt_const).pow _)
  exact (hJ.mul hB).div hp (pow_ne_zero _ hne)

def zetaS (s : ℂ) : ℂ := InitialSeparatedEuler.zetaS D.recipe.A s

def zetaSCont : ℂ → ℂ := D.recipe.L

def I (X Y Z : ℝ) : ℂ :=
  NormalizedProbe.probe D.recipe.A D.recipe.probe.coefficients D.recipe.probe.domain
    D.recipe.probe.W0 D.recipe.probe.W1 X Y Z

def Iscale (Z : ℝ) : ℂ := D.I (Scales.xScale Z) (Scales.yScale Z) Z

def M : ℂ → ℂ := D.recipe.W.M

def W1Hat : ℂ → ℂ := D.recipe.W.W1Hat

theorem M_one_sixth_ne_zero : D.M (1 / 6) ≠ 0 :=
  D.recipe.mellinWeight_ne_zero

theorem W1Hat_one_ne_zero : D.W1Hat 1 ≠ 0 :=
  D.recipe.realMellinWeight_ne_zero

theorem M_differentiableOn : DifferentiableOn ℂ D.M {z : ℂ | 0 < z.re} :=
  (recipe_M_estimates D.recipe).1

theorem M_vertical_decay (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ k * ‖D.M z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (recipe_M_estimates D.recipe).2 a b (k : ℝ) ha hab (Nat.cast_nonneg k)
  refine ⟨C, fun z hza hzb => ?_⟩
  have h := hb z.re ⟨hza, hzb⟩ z.im
  rw [Complex.re_add_im] at h
  have h' : ‖D.M z‖ ≤ C * (1 + |z.im|) ^ (-(k : ℝ)) := h
  have hpos : (0 : ℝ) < 1 + |z.im| := by positivity
  have hk : (1 + |z.im|) ^ k * (1 + |z.im|) ^ (-(k : ℝ)) = 1 := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne')]
  calc (1 + |z.im|) ^ k * ‖D.M z‖ ≤ (1 + |z.im|) ^ k * (C * (1 + |z.im|) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = C * ((1 + |z.im|) ^ k * (1 + |z.im|) ^ (-(k : ℝ))) := by ring
    _ = C := by rw [hk, mul_one]

theorem W1Hat_vertical_decay (a b : ℝ) (hab : a ≤ b) (k : ℕ) :
    ∃ C : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ k * ‖D.W1Hat z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := DedekindZetaZeroFree.PrincipalMellinComparison.principal_real_weight_rapid_strip_decay
    D.recipe a b (k : ℝ) (Nat.cast_nonneg k)
  refine ⟨C, fun z hza hzb => ?_⟩
  have hz : z ∈ DedekindZetaZeroFree.comparisonClosedStrip a b := ⟨hza, hzb⟩
  have h := hb z hz
  have hpos : (0 : ℝ) < 1 + |z.im| := by positivity
  have hk : (1 + |z.im|) ^ k * (1 + |z.im|) ^ (-(k : ℝ)) = 1 := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne')]
  calc (1 + |z.im|) ^ k * ‖D.W1Hat z‖ ≤ (1 + |z.im|) ^ k * (C * (1 + |z.im|) ^ (-(k : ℝ))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * ((1 + |z.im|) ^ k * (1 + |z.im|) ^ (-(k : ℝ))) := by ring
    _ = C := by rw [hk, mul_one]

end FixedData

def PowerBoundEps (g : ℝ → ℝ → ℂ) (v : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ‖g ε Z‖ ≤ C * Z ^ (v ε)

end

end DedekindZetaZeroFree.Quantitative
