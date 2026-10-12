module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.NormalPrincipalCoefficient

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsGreenConstantFlux

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPMsFixedHaarDisintegration.Cover F ζ hζ
abbrev X := KPMsFixedHaarDisintegration.X F ζ hζ
abbrev K := NumberField.InfinitePlace F → KPCplxPrincipalSeriesCharts.compactSubgroup

instance : MeasurableSpace (K F) := borel _
instance : BorelSpace (K F) := ⟨rfl⟩

def compactInsertion (k : K F) : Cover F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun w => (k w).val)

def rightDerivative (w : NumberField.InfinitePlace F) (j : Fin 6)
    (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,j) t))) 0

def casimir (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
    (rightDerivative F ζ hζ w 0 (rightDerivative F ζ hζ w 0 f) g -
     rightDerivative F ζ hζ w 1 (rightDerivative F ζ hζ w 1 f) g +
     2 * (rightDerivative F ζ hζ w 2 (rightDerivative F ζ hζ w 4 f) g +
          rightDerivative F ζ hζ w 4 (rightDerivative F ζ hζ w 2 f) g -
          rightDerivative F ζ hζ w 3 (rightDerivative F ζ hζ w 5 f) g -
          rightDerivative F ζ hζ w 5 (rightDerivative F ζ hζ w 3 f) g))

def Smooth (f : Cover F ζ hζ → ℂ) : Prop :=
  Continuous f ∧ ∀ g, ContDiff ℝ (⊤ : ℕ∞)
    (fun a : KPSmoothActualFlowData.LieCoordinates F =>
      f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.exponential F a)))

def KFinite (f : Cover F ζ hζ → ℂ) : Prop :=
  Module.Finite ℂ (Submodule.span ℂ
    (Set.range (fun k : K F => fun g => f (g * compactInsertion F ζ hζ k))))

section Atlas
variable {F ζ hζ} {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Cusps := KPMsFixedHaarDisintegration.CuspIndex A

def cuspRepresentative (j : Cusps A) : Cover F ζ hζ :=
  KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
    (KPRationalAdelicSplitting.rationalPGLQuotient F
      ((A.cuspAtlas j.1).representative j.2).out)

def constantTerm (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∫ q, f (cuspRepresentative A j *
    KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
    (cuspRepresentative A j)⁻¹ * g) ∂dn

def balancedArch (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    KPSmoothActualFlowData.GInfinity F := fun w =>
  let i := (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex})
    ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.upperUnipotent (p.1 i) *
      KPCplxCharacterHaar.diagonal (Units.mk0
        (Real.exp (KPMsFixedHaarDisintegration.logHeight (F := F) r + p.2.val i) : ℂ)
        (by exact_mod_cast Real.exp_ne_zero _))) * (k w).val

def cuspLift (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    Cover F ζ hζ :=
  cuspRepresentative A j *
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (balancedArch (ζ := ζ) (hζ := hζ) p k r) *
    (A.representative j.1).val

def angularValue (f : Cover F ζ hζ → ℂ)
    (ω : KPMsFixedHaarDisintegration.Omega A) (k : K F) (r : ℝ) : ℂ :=
  f (cuspLift A ω.1 ((0 : KPCuspCharts.Horizontal F), ω.2.out) k r)

def endSet (j : Cusps A) (Y : ℝ) :
    Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y)

def truncate (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) (Y : ℝ)
    (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  f g - ∑ j : Cusps A,
    if P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) ∈ endSet A j Y
    then constantTerm A dn j f g else 0

def quotientFunction (f : Cover F ζ hζ → ℂ) (x : X F ζ hζ) : ℂ := f x.out

def Eigenfunction (s : ℂ) (f : Cover F ζ hζ → ℂ) : Prop :=
  (∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
    f (γ.val * g) = f g) ∧
  (∀ u : U.toOpenSubgroup, ∀ g, f (g * u.val.val) = f g) ∧
  (∀ ε : rootsOfUnity 3 F, ∀ g,
    f (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f g) ∧
  Smooth F ζ hζ f ∧ KFinite F ζ hζ f ∧
  ∀ g, casimir F ζ hζ f g =
    KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) s * f g

def TwoWaves (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (s : ℂ) (f : Cover F ζ hζ → ℂ)
    (plus minus : KPMsFixedHaarDisintegration.Omega A → K F → ℂ) : Prop :=
  ∀ ω k r, KPMsFixedHaarDisintegration.AdmissibleCutoff A r →
    constantTerm A dn ω.1 f (cuspLift A ω.1 (0, ω.2.out) k r) =
      Complex.exp (((2 : ℂ) / 3 + s) * (Real.log r : ℂ)) * plus ω k +
      Complex.exp (((1 : ℂ) / 3 - s) * (Real.log r : ℂ)) * minus ω k

def RapidTails (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (Y₀ : ℝ) (f : Cover F ζ hζ → ℂ) : Prop :=
  ∀ (word : List (KPSmoothActualFlowData.B F)) (N : ℕ)
      (B : Set (KPCuspCharts.Cross F)), IsCompact B →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j p, p ∈ B → ∀ k r, Y₀ ≤ r → 0 < r →
      let df := word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) f
      let nc := fun ρ => df (cuspLift A j p k ρ) -
        constantTerm A dn j df (cuspLift A j p k ρ)
      ‖nc r‖ + ‖deriv nc r‖ ≤ C * r ^ (-(N : ℤ))

theorem radial_coefficient_identification (w : ℝ → ℂ)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (Set.Ioi 0)) (r : ℝ) (hr : 0 < r) :
    KPIncomingCasimir.radialLaplacian (KPCuspLogShape.dimension F)
      (fun t => w (Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)))
      (KPMsFixedHaarDisintegration.logHeight (F := F) r) =
        -(4 * (KPCuspLogShape.dimension F : ℂ) * (r : ℂ) ^ 2) * deriv (deriv w) r := by
  let d := KPCuspLogShape.dimension F
  by_cases hd : d = 0
  · simp [KPIncomingCasimir.radialLaplacian, d, hd, KPMsFixedHaarDisintegration.logHeight]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  let c : ℝ := 2 * (d : ℝ)
  let e : ℝ → ℝ := fun t => Real.exp (c * t)
  have he (t : ℝ) : HasDerivAt e (c * e t) t := by
    simpa [e, mul_comm] using ((hasDerivAt_id t).const_mul c).exp
  have hw1 (x : ℝ) (hx : 0 < x) : HasDerivAt w (deriv w x) x :=
    ((hw.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hw' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv w) (Set.Ioi 0) :=
    hw.deriv_of_isOpen isOpen_Ioi (by simp)
  have hw2 (x : ℝ) (hx : 0 < x) : HasDerivAt (deriv w) (deriv (deriv w) x) x :=
    ((hw'.contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hfirst : deriv (fun t => w (e t)) = fun t => (c * e t) • deriv w (e t) := by
    funext t
    exact ((hw1 (e t) (Real.exp_pos _)).scomp t (he t)).deriv
  have hsecond (t : ℝ) : deriv (fun t => (c * e t) • deriv w (e t)) t =
      (c * (c * e t)) • deriv w (e t) +
        (c * e t) • ((c * e t) • deriv (deriv w) (e t)) := by
    simpa only [Pi.smul_def', Function.comp_def, add_comm] using
      (((he t).const_mul c).smul ((hw2 (e t) (Real.exp_pos _)).scomp t (he t))).deriv
  have her : e (KPMsFixedHaarDisintegration.logHeight (F := F) r) = r := by
    dsimp [e, c, KPMsFixedHaarDisintegration.logHeight, d]
    rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hdR), Real.exp_log hr]
  change -((d : ℂ)⁻¹ * deriv (deriv (fun t => w (e t))) _) +
    2 * deriv (fun t => w (e t)) _ = _
  rw [hfirst, hsecond]
  dsimp only
  simp only [her]
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  dsimp [c]
  push_cast
  field_simp
  ring

def wronskian (u v : ℝ → ℂ) (r : ℝ) : ℂ :=
  star (deriv u r) * v r - star (u r) * deriv v r

def constantFlux (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (β : Measure (KPMsFixedHaarDisintegration.Omega A))
    (dk : Measure (K F)) (u v : Cover F ζ hζ → ℂ) (Y : ℝ) : ℂ :=
  ∫ ω, ∫ k, wronskian
    (fun r => constantTerm A dn ω.1 u (cuspLift A ω.1 (0,ω.2.out) k r))
    (fun r => constantTerm A dn ω.1 v (cuspLift A ω.1 (0,ω.2.out) k r)) Y ∂dk ∂β

def angularPairing (β : Measure (KPMsFixedHaarDisintegration.Omega A))
    (dk : Measure (K F))
    (p q : KPMsFixedHaarDisintegration.Omega A → K F → ℂ) : ℂ :=
  ∫ ω, ∫ k, star (p ω k) * q ω k ∂dk ∂β

def fourWaveFlux (β : Measure (KPMsFixedHaarDisintegration.Omega A))
    (dk : Measure (K F)) (z t : ℂ) (Y : ℝ)
    (puPlus puMinus pvPlus pvMinus : KPMsFixedHaarDisintegration.Omega A → K F → ℂ) : ℂ :=
  (z - t) * Complex.exp (((1 : ℂ) / 3 + z + t) * (Real.log Y : ℂ)) *
    angularPairing A β dk puPlus pvPlus +
  ((1 : ℂ) / 3 + z + t) * Complex.exp ((z - t) * (Real.log Y : ℂ)) *
    angularPairing A β dk puPlus pvMinus -
  ((1 : ℂ) / 3 + z + t) * Complex.exp ((t - z) * (Real.log Y : ℂ)) *
    angularPairing A β dk puMinus pvPlus +
  (t - z) * Complex.exp ((-(1 : ℂ) / 3 - z - t) * (Real.log Y : ℂ)) *
    angularPairing A β dk puMinus pvMinus

private theorem ray_deriv {f g : ℝ → ℂ} {Y : ℝ}
    (hf : DifferentiableAt ℝ f Y) (hg : HasDerivAt g (deriv g Y) Y)
    (hfg : ∀ r, Y ≤ r → f r = g r) : deriv f Y = deriv g Y := by
  have h := hg.hasDerivWithinAt.congr (fun r hr => hfg r hr) (hfg Y le_rfl)
  have hh := ((uniqueDiffOn_Ici Y) Y (Set.mem_Ici.mpr le_rfl)).eq hf.hasDerivAt.hasDerivWithinAt h
  simpa using congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) hh
private theorem wave_deriv (a : ℂ) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => Complex.exp (a * (Real.log x : ℂ)))
      (a * Complex.exp (a * (Real.log r : ℂ)) / (r : ℂ)) r := by
  convert (((Real.hasDerivAt_log hr.ne').ofReal_comp).const_mul a).cexp using 1 <;> simp <;> ring
private theorem exp_product (a b : ℂ) (Y : ℝ) (hY : 0 < Y) :
    Complex.exp (a * (Real.log Y : ℂ)) * Complex.exp (b * (Real.log Y : ℂ)) / (Y : ℂ) =
      Complex.exp ((a + b - 1) * (Real.log Y : ℂ)) := by
  have h : Complex.exp (Real.log Y : ℂ) = (Y : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hY]
  rw [← h, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring
private theorem expansion (z t : ℂ) (Y : ℝ) (hY : 0 < Y)
    (p q a b : ℂ) :
    wronskian
      (fun r => Complex.exp (((2 : ℂ)/3 + star z) * (Real.log r : ℂ)) * p +
        Complex.exp (((1 : ℂ)/3 - star z) * (Real.log r : ℂ)) * q)
      (fun r => Complex.exp (((2 : ℂ)/3 + t) * (Real.log r : ℂ)) * a +
        Complex.exp (((1 : ℂ)/3 - t) * (Real.log r : ℂ)) * b) Y =
    (z-t) * Complex.exp (((1 : ℂ)/3+z+t)*(Real.log Y : ℂ)) * (star p*a) +
    ((1 : ℂ)/3+z+t)*Complex.exp ((z-t)*(Real.log Y : ℂ)) * (star p*b) -
    ((1 : ℂ)/3+z+t)*Complex.exp ((t-z)*(Real.log Y : ℂ)) * (star q*a) +
    (t-z)*Complex.exp ((-(1 : ℂ)/3-z-t)*(Real.log Y : ℂ)) * (star q*b) := by
  dsimp [wronskian]
  have du := ((wave_deriv ((2 : ℂ)/3+star z) Y hY).mul_const p |>.add
        ((wave_deriv ((1 : ℂ)/3-star z) Y hY).mul_const q)).deriv
  have dv := ((wave_deriv ((2 : ℂ)/3+t) Y hY).mul_const a |>.add
        ((wave_deriv ((1 : ℂ)/3-t) Y hY).mul_const b)).deriv
  simp only [Pi.add_def, Complex.star_def] at du dv
  rw [du, dv]
  simp only [star_add, star_mul, star_div₀, star_sub, star_star, star_ofNat,
    star_div₀, star_one, Complex.star_def, ← Complex.exp_conj, map_add, map_sub,
    map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, map_star,
    map_one, RingHomCompTriple.comp_apply, starRingEnd_self_apply, RingHom.id_apply]
  have hp := exp_product ((2 : ℂ)/3+z) ((2 : ℂ)/3+t) Y hY
  have hq := exp_product ((2 : ℂ)/3+z) ((1 : ℂ)/3-t) Y hY
  have ha := exp_product ((1 : ℂ)/3-z) ((2 : ℂ)/3+t) Y hY
  have hb := exp_product ((1 : ℂ)/3-z) ((1 : ℂ)/3-t) Y hY
  have e1 : (2 : ℂ)/3+z+((2 : ℂ)/3+t)-1 = (1 : ℂ)/3+z+t := by ring
  have e2 : (2 : ℂ)/3+z+((1 : ℂ)/3-t)-1 = z-t := by ring
  have e3 : (1 : ℂ)/3-z+((2 : ℂ)/3+t)-1 = t-z := by ring
  have e4 : (1 : ℂ)/3-z+((1 : ℂ)/3-t)-1 = -(1 : ℂ)/3-z-t := by ring
  rw [e1] at hp; rw [e2] at hq; rw [e3] at ha; rw [e4] at hb
  rw [← hp, ← hq, ← ha, ← hb]
  ring
private theorem nested_four {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f1 f2 f3 f4 : α → β → ℂ) (c1 c2 c3 c4 : ℂ)
    (h1 : Integrable (Function.uncurry f1) (μ.prod ν))
    (h2 : Integrable (Function.uncurry f2) (μ.prod ν))
    (h3 : Integrable (Function.uncurry f3) (μ.prod ν))
    (h4 : Integrable (Function.uncurry f4) (μ.prod ν)) :
    (∫ a, ∫ b, c1*f1 a b+c2*f2 a b-c3*f3 a b+c4*f4 a b ∂ν ∂μ) =
    c1*(∫ a, ∫ b, f1 a b ∂ν ∂μ)+c2*(∫ a, ∫ b, f2 a b ∂ν ∂μ)-
    c3*(∫ a, ∫ b, f3 a b ∂ν ∂μ)+c4*(∫ a, ∫ b, f4 a b ∂ν ∂μ) := by
  rw [integral_integral (((h1.const_mul c1).add (h2.const_mul c2)).sub
      (h3.const_mul c3) |>.add (h4.const_mul c4))]
  have e1 := integral_add (((h1.const_mul c1).add (h2.const_mul c2)).sub (h3.const_mul c3))
    (h4.const_mul c4)
  have e2 := integral_sub ((h1.const_mul c1).add (h2.const_mul c2)) (h3.const_mul c3)
  have e3 := integral_add (h1.const_mul c1) (h2.const_mul c2)
  simp only [Pi.add_apply, Pi.sub_apply, Function.uncurry] at e1 e2 e3
  rw [e1, e2, e3]
  simp only [integral_const_mul, integral_integral h1, integral_integral h2,
    integral_integral h3, integral_integral h4]

theorem constant_flux_four_waves
    (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (β : Measure (KPMsFixedHaarDisintegration.Omega A)) (dk : Measure (K F))
    [IsFiniteMeasure β] [IsProbabilityMeasure dk]
    (z t : ℂ) (u v : Cover F ζ hζ → ℂ) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff A Y)
    (puPlus puMinus pvPlus pvMinus : KPMsFixedHaarDisintegration.Omega A → K F → ℂ)
    (hcu : TwoWaves A dn (star z) u puPlus puMinus)
    (hcv : TwoWaves A dn t v pvPlus pvMinus)
    (hdu : ∀ (ω : KPMsFixedHaarDisintegration.Omega A) (k : K F), DifferentiableAt ℝ
      (fun r => constantTerm A dn ω.1 u (cuspLift A ω.1 (0,ω.2.out) k r)) Y)
    (hdv : ∀ (ω : KPMsFixedHaarDisintegration.Omega A) (k : K F), DifferentiableAt ℝ
      (fun r => constantTerm A dn ω.1 v (cuspLift A ω.1 (0,ω.2.out) k r)) Y)
    (hpuPlus : MemLp (Function.uncurry puPlus) 2 (β.prod dk))
    (hpuMinus : MemLp (Function.uncurry puMinus) 2 (β.prod dk))
    (hpvPlus : MemLp (Function.uncurry pvPlus) 2 (β.prod dk))
    (hpvMinus : MemLp (Function.uncurry pvMinus) 2 (β.prod dk)) :
    constantFlux A dn β dk u v Y =
      fourWaveFlux A β dk z t Y puPlus puMinus pvPlus pvMinus := by
  have hmono (r : ℝ) (hr : Y ≤ r) : KPMsFixedHaarDisintegration.AdmissibleCutoff A r := by
    refine ⟨lt_of_lt_of_le hY.1 hr, hY.2.trans ?_⟩
    exact div_le_div_of_nonneg_right (Real.log_le_log hY.1 hr) (by positivity)
  have hpoint (ω : KPMsFixedHaarDisintegration.Omega A) (k : K F) :
      wronskian
        (fun r => constantTerm A dn ω.1 u (cuspLift A ω.1 (0,ω.2.out) k r))
        (fun r => constantTerm A dn ω.1 v (cuspLift A ω.1 (0,ω.2.out) k r)) Y =
      (z-t)*Complex.exp (((1 : ℂ)/3+z+t)*(Real.log Y : ℂ))*(star (puPlus ω k)*pvPlus ω k)+
      ((1 : ℂ)/3+z+t)*Complex.exp ((z-t)*(Real.log Y : ℂ))*(star (puPlus ω k)*pvMinus ω k)-
      ((1 : ℂ)/3+z+t)*Complex.exp ((t-z)*(Real.log Y : ℂ))*(star (puMinus ω k)*pvPlus ω k)+
      (t-z)*Complex.exp ((-(1 : ℂ)/3-z-t)*(Real.log Y : ℂ))*(star (puMinus ω k)*pvMinus ω k) := by
    have eu := hcu ω k Y hY
    have ev := hcv ω k Y hY
    have du := ray_deriv (hdu ω k)
      (((wave_deriv ((2 : ℂ)/3+star z) Y hY.1).mul_const (puPlus ω k)).add
        ((wave_deriv ((1 : ℂ)/3-star z) Y hY.1).mul_const (puMinus ω k))
        |>.differentiableAt.hasDerivAt)
      (fun r hr => hcu ω k r (hmono r hr))
    have dv := ray_deriv (hdv ω k)
      (((wave_deriv ((2 : ℂ)/3+t) Y hY.1).mul_const (pvPlus ω k)).add
        ((wave_deriv ((1 : ℂ)/3-t) Y hY.1).mul_const (pvMinus ω k))
        |>.differentiableAt.hasDerivAt)
      (fun r hr => hcv ω k r (hmono r hr))
    rw [wronskian, du, dv, eu, ev]
    exact expansion z t Y hY.1 _ _ _ _
  unfold constantFlux fourWaveFlux angularPairing
  simp_rw [hpoint]
  exact nested_four β dk _ _ _ _ _ _ _ _
    (hpuPlus.star.integrable_mul hpvPlus)
    (hpuPlus.star.integrable_mul hpvMinus)
    (hpuMinus.star.integrable_mul hpvPlus)
    (hpuMinus.star.integrable_mul hpvMinus)

def nonconstantFlux
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) (dk : Measure (K F))
    (u v : Cover F ζ hζ → ℂ) (Y : ℝ) : ℂ :=
  ∫ ω, ∫ x, ∫ k, wronskian
    (fun r => u (cuspLift A x.1 x.2.out k r) -
      constantTerm A dn x.1 u (cuspLift A x.1 x.2.out k r))
    (fun r => v (cuspLift A x.1 x.2.out k r) -
      constantTerm A dn x.1 v (cuspLift A x.1 x.2.out k r)) Y
    ∂dk ∂D.unipotent ω ∂KPMsFixedHaarDisintegration.probability A D.beta

end Atlas
end DedekindZetaZeroFree.KPMsGreenConstantFlux

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
