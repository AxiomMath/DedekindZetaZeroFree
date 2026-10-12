module

public import DedekindZetaZeroFree.Theta.Whittaker.ArchimedeanRootDerivatives
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def direction (imaginary : Bool) : ℂ := if imaginary then Complex.I else 1

def upperCoordinates (w : InfinitePlace F) (imaginary : Bool) (t : ℝ) : ArchCoordinates F :=
  fun v => ![if v = w then (t : ℂ) * direction imaginary else 0, 1, 0]

def upperCurve (w : InfinitePlace F) (imaginary : Bool) (t : ℝ) : Group R :=
  KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12
    (KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
        upperLieDirection R w imaginary))

theorem upperCoordinates_zero (w : InfinitePlace F) (b : Bool) :
    upperCoordinates w b 0 = archBase F := by
  funext v i
  fin_cases i <;> simp [upperCoordinates, archBase]

theorem upperCoordinates_smooth (w : InfinitePlace F) (b : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (upperCoordinates w b) := by
  apply contDiff_pi.mpr; intro v
  apply contDiff_pi.mpr; intro i
  fin_cases i <;> simp only [upperCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  · change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => if v = w then (t : ℂ) * direction b else 0)
    split_ifs
    · exact Complex.ofRealCLM.contDiff.mul contDiff_const
    · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem upperCoordinates_chart (w : InfinitePlace F) (b : Bool) (t : ℝ) :
    archChart F R.A.zeta12 R.A.primitive_zeta12 (upperCoordinates w b t) = upperCurve R w b t := by
  unfold archChart upperCurve KPRationalAdelicSplitting.pglN
    KPRationalAdelicSplitting.N
  dsimp only
  apply congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
  apply congrArg (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12)
  apply RestrictedProduct.ext
  intro v
  dsimp only [KPRationalAdelicSplitting.NTuple, KPRationalAdelicSplitting.NCoordinates]
  cases v
  case inr v =>
    change 1 = KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr v) 0
    simp
  case inl v =>
    change KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex _).symm
          (upperCoordinates w b t v 0)) *
      KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v) _ *
      KPStandardLocalRootLifts.LowerN F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex _).symm
          (upperCoordinates w b t v 2)) =
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl v)
        (Pi.single w
          ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
            upperLieDirection R w b) v)
    by_cases hv : v = w
    · subst v
      cases b <;> simp [upperCoordinates, upperLieDirection, direction, map_mul]
    · simp [upperCoordinates, hv, upperLieDirection]

theorem upperCurve_zero (w : InfinitePlace F) (b : Bool) : upperCurve R w b 0 = 1 := by
  rw [← upperCoordinates_chart, upperCoordinates_zero,
    KPInterface.ResidueConstruction.Raw.archChart_base]

theorem upperCurve_hasDeriv (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) (g : Group R) :
    HasDerivAt (fun t => f (g * upperCurve R w b t)) (upperLieDerivative R w b f g) 0 := by
  have hbase : archBase F ∈ archDomain F := by intro v; simp [archBase]
  have hO : IsOpen (archDomain F) := KPGlobalTorusBorelTwistCompatibility.groupArchDomain_open F
  have hc := (hf.2.1 g).contDiffAt (hO.mem_nhds hbase)
  have ht := upperCoordinates_smooth (F := F) w b
  have hd : DifferentiableAt ℝ (fun t => f (g * upperCurve R w b t)) 0 := by
    simp_rw [← upperCoordinates_chart]
    exact ((upperCoordinates_zero w b).symm ▸ hc |>.comp 0 ht.contDiffAt).differentiableAt (by simp)
  exact hd.hasDerivAt

theorem upperCurve_add (w : InfinitePlace F) (b : Bool) (s t : ℝ) :
    upperCurve R w b (s + t) = upperCurve R w b s * upperCurve R w b t := by
  have ha : KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm ((s + t : ℝ) : ℂ) *
        upperLieDirection R w b) =
    KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (s : ℂ) *
        upperLieDirection R w b) +
    KPRationalAdelicSplitting.localAdele F (Sum.inl w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm (t : ℂ) *
        upperLieDirection R w b) := by
    simp only [Complex.ofReal_add, map_add, add_mul, KPRationalAdelicSplitting.localAdele]
    apply Prod.ext
    · exact Pi.single_add _ _ _
    · change 0 = (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) + 0
      simp
  unfold upperCurve KPRationalAdelicSplitting.pglN
  rw [ha, KPRationalAdelicSplitting.N_add, map_mul]

theorem upperCurve_hasDerivAt (w : InfinitePlace F) (b : Bool) (f : Functions R)
    (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f) (g : Group R) (t : ℝ) :
    HasDerivAt (fun s => f (g * upperCurve R w b s))
      (upperLieDerivative R w b f (g * upperCurve R w b t)) t := by
  have hd : HasDerivAt (fun s : ℝ => s - t) 1 t := by simpa using (hasDerivAt_id t).sub_const t
  have hout : HasDerivAt (fun s => f ((g * upperCurve R w b t) * upperCurve R w b s))
      (upperLieDerivative R w b f (g * upperCurve R w b t)) (t - t) := by
    simpa only [sub_self] using (upperCurve_hasDeriv R w b f hf (g * upperCurve R w b t))
  have h := hout.scomp (h := fun s : ℝ => s - t) t hd
  convert h using 1
  · funext s
    simp only [Function.comp_def, mul_assoc, ← upperCurve_add]
    congr 2
    ring
  · simp

end DedekindZetaZeroFree.RootDerivatives

end
