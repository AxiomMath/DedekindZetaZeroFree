module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CutoffDerivativeBounds
public import DedekindZetaZeroFree.Analysis.ClosedOperators.ClosedGraphLimits
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.LaplacianPairingInvariance

@[expose] public section

set_option maxHeartbeats 400000
noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Filter
namespace DedekindZetaZeroFree
namespace KPCuspCutoffGraph

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev Fiber := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U
abbrev Coordinates := HyperbolicChart.Space (KPCuspLogShape.dimension F)
abbrev Arch := KPFiniteCuspAtlas.SymmetricSpace F

def toArch (p : Coordinates F) : Arch F :=
  fun i => (⟨p (i,0), p (i,1)⟩, p (i,2))

def fromArch (x : Arch F) : Coordinates F :=
  WithLp.toLp 2 (fun ik => ![(x ik.1).1.re, (x ik.1).1.im, (x ik.1).2] ik.2)

abbrev Cotangent := PiLp 2 (fun _ : Fin (KPCuspLogShape.dimension F) × Fin 3 =>
  Fiber F ζ hζ U)

variable (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Presentation := Σ _ : Fin a.componentCount, Arch F

def measure : Measure (Presentation F ζ hζ hF U a) :=
  Measure.sum fun i => Measure.map (fun x => (⟨i,x⟩ : Presentation F ζ hζ hF U a))
    ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict
      (a.cuspAtlas i).fundamentalDomain)

abbrev H := Lp (Fiber F ζ hζ U) 2 (measure F ζ hζ hF U a)
abbrev V := Lp (Cotangent F ζ hζ U) 2 (measure F ζ hζ hF U a)

abbrev Sections := ∀ i : Fin a.componentCount,
  KPCuspGenuineMonodromy.sections F ζ hζ U (a.representative i) (a.line i).rho

def basePoint (i : Fin a.componentCount) (x : Arch F) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
    (KPCuspSiegel.projection F _ x)

def IsCompactlySupported (s : Sections F ζ hζ hF U a) : Prop :=
  ∃ K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsCompact K ∧
    ∀ i x, basePoint F ζ hζ hF U a i x ∉ K → (s i).val x = 0

def IsSmooth (s : Sections F ζ hζ hF U a) : Prop :=
  ∀ i, ContDiff ℝ (⊤ : ℕ∞) (s i).val

def scalarTests : Submodule ℂ (Sections F ζ hζ hF U a) where
  carrier := {s | IsSmooth F ζ hζ hF U a s ∧ IsCompactlySupported F ζ hζ hF U a s}
  zero_mem' := by
    refine ⟨fun i => contDiff_const, ∅, isCompact_empty, ?_⟩
    intro i x hx
    rfl
  add_mem' := by
    rintro s t ⟨hs, K, hK, hsK⟩ ⟨ht, L, hL, htL⟩
    refine ⟨fun i => (hs i).add (ht i), K ∪ L, hK.union hL, ?_⟩
    intro i x hx
    simp only [Set.mem_union, not_or] at hx
    change (s i).val x + (t i).val x = 0
    rw [hsK i x hx.1, htL i x hx.2, add_zero]
  smul_mem' := by
    rintro c s ⟨hs, K, hK, hsK⟩
    refine ⟨fun i => (hs i).const_smul c, K, hK, ?_⟩
    intro i x hx
    change c • (s i).val x = 0
    rw [hsK i x hx, smul_zero]

def smoothSections : Submodule ℂ (Sections F ζ hζ hF U a) where
  carrier := {s | IsSmooth F ζ hζ hF U a s}
  zero_mem' := by exact fun i => contDiff_const
  add_mem' := by intro s t hs ht; exact fun i => (hs i).add (ht i)
  smul_mem' := by intro c s hs; exact fun i => (hs i).const_smul c

def scalarValue (s : Sections F ζ hζ hF U a) : Presentation F ζ hζ hF U a → Fiber F ζ hζ U :=
  fun p => ⟨(s p.1).val p.2, (s p.1).property.1 p.2⟩

def gradientComplex (s : Sections F ζ hζ hF U a) (i : Fin a.componentCount)
    (x : Arch F) (ik : Fin (KPCuspLogShape.dimension F) × Fin 3) : ℂ :=
  HyperbolicChart.differential (KPCuspLogShape.dimension F)
    ((s i).val ∘ toArch F) (fromArch F x) ik.1 ik.2

theorem gradient_mem_fiber (s : smoothSections F ζ hζ hF U a)
    (i : Fin a.componentCount) (x : Arch F) (ik : Fin (KPCuspLogShape.dimension F) × Fin 3) :
    gradientComplex F ζ hζ hF U a s.val i x ik ∈ Fiber F ζ hζ U := by
  rcases (a.line i).rank with h | h
  · have hz : (s.val i).val = 0 := by
      funext y
      have hy := (s.val i).property.1 y
      rw [h] at hy
      exact hy
    rcases ik with ⟨j,k⟩
    fin_cases k <;>
      simp [gradientComplex, hz, HyperbolicChart.differential,
        HyperbolicChart.coordinateDerivative, Fiber, h]
  · change _ ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U
    rw [h]
    trivial

def gradient (s : smoothSections F ζ hζ hF U a) :
    Presentation F ζ hζ hF U a → Cotangent F ζ hζ U :=
  fun p => WithLp.toLp 2 (fun ik => ⟨gradientComplex F ζ hζ hF U a s.val p.1 p.2 ik,
    gradient_mem_fiber F ζ hζ hF U a s p.1 p.2 ik⟩)

def localLaplacianComplex (s : Sections F ζ hζ hF U a) (i : Fin a.componentCount)
    (x : Arch F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    ((s i).val ∘ toArch F) (fromArch F x)

theorem localLaplacian_is_section (s : smoothSections F ζ hζ hF U a) :
    ∀ i, localLaplacianComplex F ζ hζ hF U a s.val i ∈
      KPCuspGenuineMonodromy.sections F ζ hζ U (a.representative i) (a.line i).rho := by
  intro i
  have hsm : ContDiff ℝ (⊤ : ℕ∞) ((s.val i).val ∘ toArch F) :=
    (s.property i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)
  refine ⟨?_, ?_⟩
  · intro x
    rcases (a.line i).rank with h | h
    · have hz : (s.val i).val = 0 := by
        funext y
        have hy := (s.val i).property.1 y
        rw [h] at hy
        exact hy
      have hd (j : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
          HyperbolicChart.coordinateDerivative (KPCuspLogShape.dimension F) j k 0 = 0 := by
        funext p
        simp [HyperbolicChart.coordinateDerivative]
      simp [localLaplacianComplex, hz, HyperbolicChart.laplacian, hd, Fiber, h]
    · rw [h]; trivial
  · intro γ x
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (γ : KPCuspArithmetic.PGL2 F)
    let g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
      fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A
    have ha (y : Arch F) : KPArch.productAction (KPCuspLogShape.dimension F) g y =
        (γ : KPCuspArithmetic.PGL2 F) • y := by
      change _ = KPCuspSiegel.action F _ y
      rw [← hA, KPCuspSiegel.action_mk]
      rfl
    have hi (y : Arch F) : toArch F (fromArch F y) = y := by
      funext j
      simp [fromArch, toArch]
    have hc : (fun y : Coordinates F => (s.val i).val
        (toArch F (fromArch F (KPArch.productAction _ g (toArch F y))))) =ᶠ[nhds (fromArch F x)]
        (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ) *
          (s.val i).val (toArch F y)) := by
      apply Filter.Eventually.of_forall
      intro y
      dsimp only
      rw [hi, ha]
      exact (s.val i).property.2 γ _
    have hl := KPCompactGreenRadialIntegrability.laplacian_action_invariant
      (KPCuspLogShape.dimension F) g ((s.val i).val ∘ toArch F) (fromArch F x)
      (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ) hc
      (hsm.contDiffAt) (hsm.contDiffAt)
    change HyperbolicChart.laplacian _ _ _ = _
    change HyperbolicChart.laplacian _ _
        (fromArch F (KPArch.productAction _ g (toArch F (fromArch F x)))) = _ at hl
    rw [hi, ha] at hl
    exact hl

def localLaplacianSection (s : smoothSections F ζ hζ hF U a) : Sections F ζ hζ hF U a :=
  fun i => ⟨localLaplacianComplex F ζ hζ hF U a s.val i,
    localLaplacian_is_section F ζ hζ hF U a s i⟩

def covector (W : Cotangent F ζ hζ U) (x v : Arch F) : ℂ :=
  ∑ i, ((W (i,0) : ℂ) * (v i).2 + (Real.exp (-(x i).2) : ℂ) *
    ((W (i,1) : ℂ) * (v i).1.re + (W (i,2) : ℂ) * (v i).1.im))

def IsCotangentTest (W : ∀ i : Fin a.componentCount, Arch F → Cotangent F ζ hζ U) : Prop :=
  (∀ i, ContDiff ℝ (⊤ : ℕ∞) (W i)) ∧
  (∀ i (γ : KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) x v,
    covector F ζ hζ U (W i ((γ : KPCuspArithmetic.PGL2 F) • x))
      ((γ : KPCuspArithmetic.PGL2 F) • x)
      (fderiv ℝ (fun y : Arch F => (γ : KPCuspArithmetic.PGL2 F) • y) x v) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ) *
      covector F ζ hζ U (W i x) x v) ∧
  ∃ K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsCompact K ∧
    ∀ i x, basePoint F ζ hζ hF U a i x ∉ K → W i x = 0

 theorem covector_add (A B : Cotangent F ζ hζ U) (x v : Arch F) :
    covector F ζ hζ U (A + B) x v =
      covector F ζ hζ U A x v + covector F ζ hζ U B x v := by
  simp only [covector, PiLp.add_apply, Submodule.coe_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

 theorem covector_smul (c : ℂ) (A : Cotangent F ζ hζ U) (x v : Arch F) :
    covector F ζ hζ U (c • A) x v = c * covector F ζ hζ U A x v := by
  simp only [covector, PiLp.smul_apply, Submodule.coe_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

def cotangentTests : Submodule ℂ (∀ i : Fin a.componentCount, Arch F → Cotangent F ζ hζ U) where
  carrier := {W | IsCotangentTest F ζ hζ hF U a W}
  zero_mem' := by
    refine ⟨fun i => contDiff_const, ?_, ∅, isCompact_empty, ?_⟩
    · intro i γ x v
      simp [covector]
    · intro i x _
      rfl
  add_mem' := by
    rintro W W' ⟨hW1, hW2, K, hKc, hK⟩ ⟨hW1', hW2', L, hLc, hL⟩
    refine ⟨fun i => (hW1 i).add (hW1' i), ?_, K ∪ L, hKc.union hLc, ?_⟩
    · intro i γ x v
      simp only [Pi.add_apply]
      rw [covector_add, covector_add, hW2 i γ x v, hW2' i γ x v]
      ring
    · intro i x hx
      simp only [Set.mem_union, not_or] at hx
      simp only [Pi.add_apply]
      rw [hK i x hx.1, hL i x hx.2, add_zero]
  smul_mem' := by
    rintro c W ⟨hW1, hW2, K, hKc, hK⟩
    refine ⟨fun i => (hW1 i).const_smul c, ?_, K, hKc, ?_⟩
    · intro i γ x v
      simp only [Pi.smul_apply]
      rw [covector_smul, covector_smul, hW2 i γ x v]
      ring
    · intro i x hx
      simp only [Pi.smul_apply]
      rw [hK i x hx, smul_zero]

 def archCLM : Coordinates F →L[ℝ] Arch F :=
  LinearMap.toContinuousLinearMap {
    toFun := toArch F
    map_add' := by intro x y; ext i <;> simp [toArch]; rfl
    map_smul' := by intro c x; ext i : 1; apply Prod.ext <;> simp [toArch, Complex.real_smul]; apply Complex.ext <;> simp }
 def realCLM : Arch F →L[ℝ] Coordinates F :=
  LinearMap.toContinuousLinearMap {
    toFun := fromArch F
    map_add' := by intro x y; ext i; rcases i with ⟨i,k⟩; fin_cases k <;> simp [fromArch, Complex.real_smul]
    map_smul' := by intro c x; ext i; rcases i with ⟨i,k⟩; fin_cases k <;> simp [fromArch, Complex.real_smul] }
private lemma arch_real (x : Arch F) : toArch F (fromArch F x) = x := by
  funext j; simp [fromArch, toArch]

private lemma differential_smooth (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (HyperbolicChart.differential d f) := by
  apply contDiff_pi.mpr; intro j
  apply contDiff_pi.mpr; intro k
  have hd (l : Fin 3) : ContDiff ℝ ∞ (HyperbolicChart.coordinateDerivative d j l f) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hr : ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d => Real.exp (p (j,2))) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin 3 => ℝ) (j,2)).contDiff.exp
  have he : ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d => (Real.exp (p (j,2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  fin_cases k
  · simpa [HyperbolicChart.differential] using hd 2
  · simpa [HyperbolicChart.differential] using he.mul (hd 0)
  · simpa [HyperbolicChart.differential] using he.mul (hd 1)
private lemma gradient_smooth (s : scalarTests F ζ hζ hF U a) (i : Fin a.componentCount) :
    ContDiff ℝ ∞ (fun x : Arch F => gradient F ζ hζ hF U a ⟨s.val,s.property.1⟩ ⟨i,x⟩) := by
  apply (contDiff_piLp 2).mpr
  intro ik
  have hh := differential_smooth _ ((s.val i).val ∘ toArch F)
    ((s.property.1 i).comp (archCLM F).contDiff)
  have hc : ContDiff ℝ ∞ (fun x : Arch F => gradientComplex F ζ hζ hF U a s.val i x ik) :=
    ((contDiff_pi.mp (contDiff_pi.mp hh ik.1) ik.2).comp (realCLM F).contDiff)
  let P := (Fiber F ζ hζ U).orthogonalProjectionOnto
  convert (P.restrictScalars ℝ).contDiff.comp hc using 1
  funext x
  exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _).symm
private lemma clm_coordinate_sum (L : Coordinates F →L[ℝ] ℂ) (p : Coordinates F) :
    L p = ∑ j, ∑ k, (p (j,k) : ℂ) * L (HyperbolicChart.coordinateVector _ j k) := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin (KPCuspLogShape.dimension F) × Fin 3) ℝ).sum_repr p)
  rw [map_sum] at h
  rw [← h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  simp only [map_smul, EuclideanSpace.basisFun_repr, Complex.real_smul]
  congr 2
  ext ik
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, HyperbolicChart.coordinateVector]
private lemma covector_gradient (s : scalarTests F ζ hζ hF U a)
    (i : Fin a.componentCount) (x v : Arch F) :
    covector F ζ hζ U (gradient F ζ hζ hF U a ⟨s.val,s.property.1⟩ ⟨i,x⟩) x v =
      fderiv ℝ (s.val i).val x v := by
  let L := fderiv ℝ ((s.val i).val ∘ toArch F) (fromArch F x)
  have hL : L = (fderiv ℝ (s.val i).val x).comp (archCLM F) := by
    change fderiv ℝ ((s.val i).val ∘ (archCLM F)) (fromArch F x) = _
    rw [fderiv_comp _ ((s.property.1 i).differentiable (by simp) _) (archCLM F).differentiableAt,
      (archCLM F).fderiv]
    change (fderiv ℝ (s.val i).val (toArch F (fromArch F x))).comp _ = _
    rw [arch_real]
  have hh := clm_coordinate_sum F L (fromArch F v)
  have he : L (fromArch F v) = fderiv ℝ (s.val i).val x v := by
    rw [hL]; change (fderiv ℝ (s.val i).val x) (toArch F (fromArch F v)) = _
    rw [arch_real]
  rw [← he, hh]
  unfold covector
  apply Finset.sum_congr rfl; intro j _
  simp only [Fin.sum_univ_three, gradient, gradientComplex, WithLp.ofLp_toLp,
    HyperbolicChart.differential, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  have he : (Real.exp (-(x j).2) : ℂ) * (Real.exp ((fromArch F x) (j,2)) : ℂ) = 1 := by
    simp only [fromArch, WithLp.ofLp_toLp, Matrix.cons_val_two]
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  change L (HyperbolicChart.coordinateVector _ j 2) * (v j).2 +
    (Real.exp (-(x j).2) : ℂ) *
      ((Real.exp ((fromArch F x) (j,2)) : ℂ) * L (HyperbolicChart.coordinateVector _ j 0) * (v j).1.re +
        (Real.exp ((fromArch F x) (j,2)) : ℂ) * L (HyperbolicChart.coordinateVector _ j 1) * (v j).1.im) =
    (v j).1.re * L (HyperbolicChart.coordinateVector _ j 0) +
      (v j).1.im * L (HyperbolicChart.coordinateVector _ j 1) +
      (v j).2 * L (HyperbolicChart.coordinateVector _ j 2)
  calc
    _ = ((Real.exp (-(x j).2) : ℂ) * (Real.exp ((fromArch F x) (j,2)) : ℂ)) *
        ((v j).1.re * L (HyperbolicChart.coordinateVector _ j 0) + (v j).1.im * L (HyperbolicChart.coordinateVector _ j 1)) +
        (v j).2 * L (HyperbolicChart.coordinateVector _ j 2) := by ring
    _ = _ := by rw [he]; ring
private lemma arithmetic_action_differentiable (γ : KPCuspArithmetic.PGL2 F) :
    Differentiable ℝ (fun x : Arch F => γ • x) := by
  obtain ⟨A,hA⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  let g : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A
  have ha : (fun x : Arch F => γ • x) = KPArch.productAction _ g := by
    funext x
    change KPCuspSiegel.action F γ x = _
    rw [← hA, KPCuspSiegel.action_mk]; rfl
  rw [ha]
  exact (KPArch.productAction_contDiff _ g).differentiable (by simp)
private lemma basePoint_continuous (i : Fin a.componentCount) :
    Continuous (basePoint F ζ hζ hF U a i) := by
  have h : Continuous (fun x : Arch F => a.components ⟨i, KPCuspSiegel.projection F _ x⟩) :=
    a.components.continuous.comp (continuous_sigmaMk.comp (KPCuspSiegel.continuous_projection F _))
  change Continuous (fun x : Arch F => basePoint F ζ hζ hF U a i x)
  simpa only [basePoint, a.components_formula] using h

theorem differential_test (s : scalarTests F ζ hζ hF U a) :
    IsCotangentTest F ζ hζ hF U a
      (fun i x => gradient F ζ hζ hF U a ⟨s.val, s.property.1⟩ ⟨i,x⟩) := by
  refine ⟨gradient_smooth F ζ hζ hF U a s, ?_, ?_⟩
  · intro i γ x v
    rw [covector_gradient, covector_gradient]
    have hd : (fderiv ℝ (s.val i).val ((γ : KPCuspArithmetic.PGL2 F) • x)).comp
        (fderiv ℝ (fun y : Arch F => (γ : KPCuspArithmetic.PGL2 F) • y) x) =
        (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ) • fderiv ℝ (s.val i).val x := by
      rw [← fderiv_comp x ((s.property.1 i).differentiable (by simp) _)
        (arithmetic_action_differentiable F _ x)]
      have he : ((s.val i).val ∘ (fun y : Arch F => (γ : KPCuspArithmetic.PGL2 F) • y)) =
          (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ) • (s.val i).val := by
        funext y; exact (s.val i).property.2 γ y
      rw [he, (((s.property.1 i).differentiable (by simp) x).hasFDerivAt.const_smul _).fderiv]
    exact congrArg (fun L : Arch F →L[ℝ] ℂ => L v) hd
  · obtain ⟨K,hK,hsK⟩ := s.property.2
    refine ⟨K,hK,?_⟩
    intro i x hx
    letI := CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U a
    have hn : ∀ᶠ p : Coordinates F in nhds (fromArch F x),
        basePoint F ζ hζ hF U a i (toArch F p) ∉ K :=
      ((hK.isClosed.isOpen_compl).preimage ((basePoint_continuous F ζ hζ hF U a i).comp
        (archCLM F).continuous)).mem_nhds (by change basePoint F ζ hζ hF U a i (toArch F (fromArch F x)) ∉ K; rw [arch_real]; exact hx)
    have hz : ((s.val i).val ∘ toArch F) =ᶠ[nhds (fromArch F x)] 0 :=
      hn.mono fun p hp => hsK i _ hp
    have hfd := hz.fderiv_eq (𝕜 := ℝ)
    apply PiLp.ext; intro ik; apply Subtype.ext
    rcases ik with ⟨j,k⟩
    fin_cases k <;> simp [gradient, gradientComplex, HyperbolicChart.differential,
      HyperbolicChart.coordinateDerivative, hfd]

 theorem diff_add (d : ℕ) (f g : HyperbolicChart.Space d → ℂ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (p : HyperbolicChart.Space d)
    (j : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (fun q => f q + g q) p j k =
      HyperbolicChart.differential d f p j k + HyperbolicChart.differential d g p j k := by
  fin_cases k <;> simp [HyperbolicChart.differential, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    KPCuspCutoffGraphApproximation.coordinateDerivative_add d _ _ f g hf hg] <;> ring
 theorem diff_smul (d : ℕ) (f : HyperbolicChart.Space d → ℂ)
    (hf : Differentiable ℝ f) (c : ℂ) (p : HyperbolicChart.Space d)
    (j : Fin d) (k : Fin 3) :
    HyperbolicChart.differential d (fun q => c * f q) p j k =
      c * HyperbolicChart.differential d f p j k := by
  have hc (l : Fin 3) : HyperbolicChart.coordinateDerivative d j l (fun q => c * f q) p =
      c * HyperbolicChart.coordinateDerivative d j l f p := by
    unfold HyperbolicChart.coordinateDerivative
    rw [show (fun q => c * f q) = c • f by rfl]
    rw [((hf p).hasFDerivAt.const_smul c).fderiv]
    rfl
  fin_cases k <;> simp [HyperbolicChart.differential, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, hc] <;> ring

def differential : scalarTests F ζ hζ hF U a →ₗ[ℂ] cotangentTests F ζ hζ hF U a where
  toFun s := ⟨fun i x => gradient F ζ hζ hF U a ⟨s.val, s.property.1⟩ ⟨i,x⟩,
    differential_test F ζ hζ hF U a s⟩
  map_add' := by
    intro s t
    apply Subtype.ext
    funext i x
    apply PiLp.ext
    intro ik
    apply Subtype.ext
    exact diff_add _ _ _
      (((s.property.1 i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)).differentiable (by simp))
      (((t.property.1 i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)).differentiable (by simp))
      (fromArch F x) ik.1 ik.2
  map_smul' := by
    intro c s
    apply Subtype.ext
    funext i x
    apply PiLp.ext
    intro ik
    apply Subtype.ext
    exact diff_smul _ _
      (((s.property.1 i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)).differentiable (by simp))
      c (fromArch F x) ik.1 ik.2

def divergenceComplex (W : cotangentTests F ζ hζ hF U a) (i : Fin a.componentCount)
    (x : Arch F) : ℂ :=
  HyperbolicChart.codifferential (KPCuspLogShape.dimension F)
    (fun p j k => (W.val i (toArch F p) (j,k) : ℂ)) (fromArch F x)

theorem divergence_is_section (W : cotangentTests F ζ hζ hF U a) :
    ∀ i, divergenceComplex F ζ hζ hF U a W i ∈
      KPCuspGenuineMonodromy.sections F ζ hζ U (a.representative i) (a.line i).rho := by
  intro i
  refine ⟨?_, ?_⟩
  · intro x
    rcases (a.line i).rank with h | h
    · have hz : W.val i = 0 := by
        funext y
        ext ik
        have hy := (W.val i y ik).property
        change (W.val i y ik : ℂ) ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U at hy
        rw [h] at hy
        exact hy
      simp [divergenceComplex, hz, HyperbolicChart.codifferential,
        HyperbolicChart.coordinateDerivative, Fiber, h]
    · rw [h]; trivial
  · intro γ x
    exact KPCuspCutoffGraphApproximation.arithmetic_codifferential_covariant F ζ hζ U (W.val i)
      (W.property.1 i) (γ : KPCuspArithmetic.PGL2 F)
      (KPCuspGenuineMonodromy.chi F ζ hζ ((a.line i).rho γ) : ℂ)
      (W.property.2.1 i γ) x

def divergenceSection (W : cotangentTests F ζ hζ hF U a) : Sections F ζ hζ hF U a :=
  fun i => ⟨divergenceComplex F ζ hζ hF U a W i,
    divergence_is_section F ζ hζ hF U a W i⟩

private theorem smooth_codifferential (d : ℕ)
    (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (hW : ∀ j k, ContDiff ℝ ∞ (fun p => W p j k)) :
    ContDiff ℝ ∞ (HyperbolicChart.codifferential d W) := by
  apply ContDiff.sum; intro j _
  have hd (l k : Fin 3) : ContDiff ℝ ∞
      (HyperbolicChart.coordinateDerivative d j l (fun p => W p j k)) :=
    ((hW j k).fderiv_right (by simp)).clm_apply contDiff_const
  have hr : ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d => Real.exp (p (j,2))) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d × Fin 3 => ℝ) (j,2)).contDiff.exp
  have he : ContDiff ℝ ∞ (fun p : HyperbolicChart.Space d => (Real.exp (p (j,2)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  exact (((hd 2 0).neg.add (contDiff_const.mul (hW j 0))).sub
    (he.mul (hd 0 1))).sub (he.mul (hd 1 2))

private theorem cotangent_coefficient_smooth
    (W : cotangentTests F ζ hζ hF U a) (i : Fin a.componentCount)
    (j : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    ContDiff ℝ ∞ (fun p : Coordinates F => (W.val i (toArch F p) (j,k) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun p : Coordinates F => W.val i (toArch F p)) :=
    (W.property.1 i).comp (archCLM F).contDiff
  have hp := (contDiff_piLp 2).mp h (j,k)
  exact ((Fiber F ζ hζ U).subtypeL.restrictScalars ℝ).contDiff.comp hp

theorem divergence_test (W : cotangentTests F ζ hζ hF U a) :
    divergenceSection F ζ hζ hF U a W ∈ scalarTests F ζ hζ hF U a := by
  refine ⟨?_, ?_⟩
  · intro i
    exact (smooth_codifferential _ _
      (cotangent_coefficient_smooth F ζ hζ hF U a W i)).comp (realCLM F).contDiff
  · obtain ⟨K,hK,hWK⟩ := W.property.2.2
    refine ⟨K,hK,?_⟩
    intro i x hx
    letI := CoreChartLocalizers.quotient_hausdorff F ζ hζ hF U a
    have hn : ∀ᶠ p : Coordinates F in nhds (fromArch F x),
        basePoint F ζ hζ hF U a i (toArch F p) ∉ K :=
      ((hK.isClosed.isOpen_compl).preimage ((basePoint_continuous F ζ hζ hF U a i).comp
        (archCLM F).continuous)).mem_nhds
        (by change basePoint F ζ hζ hF U a i (toArch F (fromArch F x)) ∉ K
            rw [arch_real]; exact hx)
    have hz (j : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
        (fun p : Coordinates F => (W.val i (toArch F p) (j,k) : ℂ)) =ᶠ[nhds (fromArch F x)] 0 :=
      hn.mono fun p hp => by dsimp only; rw [hWK i _ hp]; rfl
    have hd (j : Fin (KPCuspLogShape.dimension F)) (l k : Fin 3) :
        HyperbolicChart.coordinateDerivative _ j l
          (fun p : Coordinates F => (W.val i (toArch F p) (j,k) : ℂ)) (fromArch F x) = 0 := by
      simp [HyperbolicChart.coordinateDerivative, (hz j k).fderiv_eq]
    change divergenceComplex F ζ hζ hF U a W i x = 0
    simp [divergenceComplex, HyperbolicChart.codifferential, hd, arch_real, hWK i x hx]

 theorem codiff_add (d : ℕ) (W W' : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (hW : ∀ j k, Differentiable ℝ (fun p => W p j k))
    (hW' : ∀ j k, Differentiable ℝ (fun p => W' p j k)) (p : HyperbolicChart.Space d) :
    HyperbolicChart.codifferential d (fun q j k => W q j k + W' q j k) p =
      HyperbolicChart.codifferential d W p + HyperbolicChart.codifferential d W' p := by
  simp only [HyperbolicChart.codifferential]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [KPCuspCutoffGraphApproximation.coordinateDerivative_add _ _ _ _ _ (hW j 0) (hW' j 0),
    KPCuspCutoffGraphApproximation.coordinateDerivative_add _ _ _ _ _ (hW j 1) (hW' j 1),
    KPCuspCutoffGraphApproximation.coordinateDerivative_add _ _ _ _ _ (hW j 2) (hW' j 2)]
  ring
 theorem codiff_smul (d : ℕ) (W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d)
    (hW : ∀ j k, Differentiable ℝ (fun p => W p j k)) (c : ℂ) (p : HyperbolicChart.Space d) :
    HyperbolicChart.codifferential d (fun q j k => c * W q j k) p =
      c * HyperbolicChart.codifferential d W p := by
  have hc (j : Fin d) (l k : Fin 3) :
      HyperbolicChart.coordinateDerivative d j l (fun q => c * W q j k) p =
      c * HyperbolicChart.coordinateDerivative d j l (fun q => W q j k) p := by
    unfold HyperbolicChart.coordinateDerivative
    rw [show (fun q => c * W q j k) = c • (fun q => W q j k) by rfl]
    rw [((hW j k p).hasFDerivAt.const_smul c).fderiv]
    rfl
  simp only [HyperbolicChart.codifferential]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hc, hc, hc]; ring

set_option synthInstance.maxHeartbeats 200000 in
 theorem cotangent_coefficient_differentiable
    (W : cotangentTests F ζ hζ hF U a) (i : Fin a.componentCount)
    (j : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    Differentiable ℝ (fun p : Coordinates F => (W.val i (toArch F p) (j,k) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun p : Coordinates F => W.val i (toArch F p)) :=
    (W.property.1 i).comp (KPCuspCutoffGraphApproximation.cutoff_toArch_contDiff F)
  let P : Cotangent F ζ hζ U →L[ℝ] Fiber F ζ hζ U :=
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (KPCuspLogShape.dimension F) × Fin 3 => Fiber F ζ hζ U)
      (j,k)
  have hP : ContDiff ℝ ∞ (fun p : Coordinates F => W.val i (toArch F p) (j,k)) := by
    simpa only [Function.comp_def, P, ContinuousLinearMap.coe_restrictScalars, PiLp.proj_apply] using
      P.contDiff.comp h
  have h' : ContDiff ℝ ∞ (fun p : Coordinates F => (W.val i (toArch F p) (j,k) : ℂ)) := by
    exact ((Fiber F ζ hζ U).subtypeL.restrictScalars ℝ).contDiff.comp hP
  exact h'.differentiable (by simp)

def divergence : cotangentTests F ζ hζ hF U a →ₗ[ℂ] scalarTests F ζ hζ hF U a where
  toFun W := ⟨divergenceSection F ζ hζ hF U a W, divergence_test F ζ hζ hF U a W⟩
  map_add' := by
    intro W W'
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext x
    exact codiff_add _ _ _
      (cotangent_coefficient_differentiable F ζ hζ hF U a W i)
      (cotangent_coefficient_differentiable F ζ hζ hF U a W' i) (fromArch F x)
  map_smul' := by
    intro c W
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext x
    exact codiff_smul _ _ (cotangent_coefficient_differentiable F ζ hζ hF U a W i)
      c (fromArch F x)

private theorem toArch_contDiff : ContDiff ℝ ∞ (toArch F) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.prodMk
  · have h : (fun p : Coordinates F => (⟨p (i,0), p (i,1)⟩ : ℂ)) =
        fun p => Complex.ofRealCLM (p (i,0)) + Complex.ofRealCLM (p (i,1)) * Complex.I := by
      funext p
      rw [Complex.mk_eq_add_mul_I, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply]
    rw [h]; fun_prop
  · fun_prop

private theorem fromArch_toArch (p : Coordinates F) : fromArch F (toArch F p) = p := by
  ext ik
  rcases ik with ⟨i,k⟩
  fin_cases k <;> simp [fromArch, toArch]

private theorem gradient_apply (s : scalarTests F ζ hζ hF U a) (i : Fin a.componentCount)
    (p : Coordinates F) (j : Fin (KPCuspLogShape.dimension F)) (k : Fin 3) :
    (((differential F ζ hζ hF U a s).val i (toArch F p)) (j,k) : ℂ) =
      HyperbolicChart.differential (KPCuspLogShape.dimension F)
        (fun q : Coordinates F => (s.val i).val (toArch F q)) (fromArch F (toArch F p)) j k :=
  rfl

theorem divergence_differential_local (s : scalarTests F ζ hζ hF U a) :
    (divergence F ζ hζ hF U a (differential F ζ hζ hF U a s)).val =
      localLaplacianSection F ζ hζ hF U a ⟨s.val, s.property.1⟩ := by
  funext i
  apply Subtype.ext
  funext x
  have hd : 1 ≤ KPCuspLogShape.dimension F :=
    Nat.succ_le_of_lt (KPCuspLogShape.dimension_pos F hF)
  have hf : ContDiff ℝ ∞ (fun p : Coordinates F => (s.val i).val (toArch F p)) :=
    (s.property.1 i).comp (toArch_contDiff F)
  show HyperbolicChart.codifferential (KPCuspLogShape.dimension F)
      (fun p : Coordinates F => fun j : Fin (KPCuspLogShape.dimension F) => fun k : Fin 3 =>
        (((differential F ζ hζ hF U a s).val i (toArch F p)) (j,k) : ℂ)) (fromArch F x)
    = HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
      (fun p : Coordinates F => (s.val i).val (toArch F p)) (fromArch F x)
  rw [show (fun p : Coordinates F => fun j : Fin (KPCuspLogShape.dimension F) => fun k : Fin 3 =>
        (((differential F ζ hζ hF U a s).val i (toArch F p)) (j,k) : ℂ)) =
      (fun p : Coordinates F => fun j : Fin (KPCuspLogShape.dimension F) => fun k : Fin 3 =>
        HyperbolicChart.differential (KPCuspLogShape.dimension F)
          (fun q : Coordinates F => (s.val i).val (toArch F q)) (fromArch F (toArch F p)) j k) from by
    funext p j k
    exact gradient_apply F ζ hζ hF U a s i p j k]
  rw [show (fun p : Coordinates F => fun j : Fin (KPCuspLogShape.dimension F) => fun k : Fin 3 =>
        HyperbolicChart.differential (KPCuspLogShape.dimension F)
          (fun q : Coordinates F => (s.val i).val (toArch F q)) (fromArch F (toArch F p)) j k) =
      HyperbolicChart.differential (KPCuspLogShape.dimension F)
        (fun q : Coordinates F => (s.val i).val (toArch F q)) from by
    funext p j k
    rw [fromArch_toArch]]
  rw [HyperbolicChart.codifferential_differential _ hd _ hf]

def highEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
        ((a.cuspAtlas i).representative c) T

def closedHighEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) ''
        (KPCuspSiegel.action F ((a.cuspAtlas i).representative c) ''
          {x | T ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x}))

def core : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  Set.univ \ highEnds F ζ hζ hF U a a.threshold

def scalarLift (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) (i : Fin a.componentCount) :
    Coordinates F → ℂ :=
  fun p => (r (basePoint F ζ hζ hF U a i (toArch F p)) : ℂ)

def scalarGradientNorm (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℝ :=
  Real.sqrt (∑ j : Fin (KPCuspLogShape.dimension F), ∑ k : Fin 3,
    ‖HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (scalarLift F ζ hζ hF U a r i) (fromArch F x) j k‖ ^ 2)

def scalarLaplacian (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    (scalarLift F ζ hζ hF U a r i) (fromArch F x)

structure Cutoffs where
  rho : ℕ → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  smooth : ∀ n i, ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Arch F => rho n (basePoint F ζ hζ hF U a i x))
  compact_support : ∀ n, HasCompactSupport (rho n)
  nonnegative : ∀ n x, 0 ≤ rho n x
  le_one : ∀ n x, rho n x ≤ 1

  height_bound : ℕ
  above_atlas_threshold : a.threshold < (height_bound : ℝ)
  on_core : ∀ n, height_bound ≤ n → ∀ x ∈ core F ζ hζ hF U a, rho n x = 1
  on_sublevel : ∀ n, height_bound ≤ n →
    ∀ x ∉ highEnds F ζ hζ hF U a n, rho n x = 1
  above_next : ∀ n, height_bound ≤ n →
    ∀ x ∈ closedHighEnds F ζ hζ hF U a (n+1), rho n x = 0
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  derivative_bound : ∀ n i x,
    scalarGradientNorm F ζ hζ hF U a (rho n) i x +
      ‖scalarLaplacian F ζ hζ hF U a (rho n) i x‖ ≤ bound

theorem cutoffs_exist : Nonempty (Cutoffs F ζ hζ hF U a) := by
  let r := KPCuspCutoffGraphApproximation.CutoffScalars.rho a
  obtain ⟨B,hB,hbound⟩ := KPCuspCutoffGraphApproximation.CutoffBounds.rho_derivative_bound a
  refine ⟨{
    rho := r
    smooth := KPCuspCutoffGraphApproximation.CutoffScalars.rho_smooth a
    compact_support := KPCuspCutoffGraphApproximation.CutoffScalars.rho_compact_support a
    nonnegative := fun n x => (KPCuspCutoffGraphApproximation.CutoffScalars.rho_bounds a n x).1
    le_one := fun n x => (KPCuspCutoffGraphApproximation.CutoffScalars.rho_bounds a n x).2
    height_bound := KPCuspCutoffGraphApproximation.CutoffScalars.heightBound a
    above_atlas_threshold := KPCuspCutoffGraphApproximation.CutoffScalars.above_threshold a
    on_core := ?_
    on_sublevel := ?_
    above_next := KPCuspCutoffGraphApproximation.CutoffScalars.rho_above_next a
    bound := B
    bound_nonnegative := hB
    derivative_bound := hbound }⟩
  · intro n _ x hx
    apply KPCuspCutoffGraphApproximation.CutoffScalars.rho_on_core
    simpa only [core, highEnds, Set.mem_diff, Set.mem_univ, true_and,
      KPCuspCutoffGraphApproximation.CutoffScalars.endRegion, Set.iUnion_sigma] using hx
  · intro n hn x hx
    apply KPCuspCutoffGraphApproximation.CutoffScalars.rho_on_integer_sublevel a n hn
    simpa only [highEnds, KPCuspCutoffGraphApproximation.CutoffScalars.endRegion,
      Set.iUnion_sigma] using hx

theorem cutoff_is_section (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (s : Sections F ζ hζ hF U a) :
    ∀ i, (fun x => (r (basePoint F ζ hζ hF U a i x) : ℂ) * (s i).val x) ∈
      KPCuspGenuineMonodromy.sections F ζ hζ U (a.representative i) (a.line i).rho := by
  intro i
  refine ⟨fun x => (Fiber F ζ hζ U).smul_mem
    (r (basePoint F ζ hζ hF U a i x) : ℂ) ((s i).property.1 x), ?_⟩
  intro γ x
  have hb : basePoint F ζ hζ hF U a i ((γ : KPCuspArithmetic.PGL2 F) • x) =
      basePoint F ζ hζ hF U a i x := by
    unfold basePoint
    congr 1
    exact KPCuspSiegel.projection_action F _ γ x
  dsimp only
  rw [hb, (s i).property.2 γ x]
  ring

def cutoffSection (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (s : Sections F ζ hζ hF U a) : Sections F ζ hζ hF U a :=
  fun i => ⟨fun x => (r (basePoint F ζ hζ hF U a i x) : ℂ) * (s i).val x,
    cutoff_is_section F ζ hζ hF U a r s i⟩

 def rawCutoffs (r : Cutoffs F ζ hζ hF U a) :
    KPCuspCutoffGraphApproximation.Cutoffs F ζ hζ hF U a where
  rho := r.rho
  smooth := r.smooth
  compact_support := r.compact_support
  nonnegative := r.nonnegative
  le_one := r.le_one
  height_bound := r.height_bound
  above_atlas_threshold := r.above_atlas_threshold
  on_core := r.on_core
  on_sublevel := r.on_sublevel
  above_next := r.above_next
  bound := r.bound
  bound_nonnegative := r.bound_nonnegative
  derivative_bound := r.derivative_bound

end KPCuspCutoffGraph

end DedekindZetaZeroFree

end
