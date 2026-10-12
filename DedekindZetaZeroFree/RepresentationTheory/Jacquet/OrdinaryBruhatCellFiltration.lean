module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OpenCellKernelAndActions
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.TestFunctionCoinvariantsAndIntegration
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.InductionReciprocity

@[expose] public section

section
noncomputable section

set_option maxHeartbeats 4000000

namespace DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.QuotientExactness

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain MeasureTheory
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
local instance : ValuativeRel (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w
local instance : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
local instance : MeasurableSpace (KPRankOneInduction.LocalField F w) := borel _
local instance : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  (τB : Representation ℂ (Borel F ζ hζ w) E)
  (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB)
  (μ : Measure (KPRankOneInduction.LocalField F w)) [μ.IsAddHaarMeasure]

 abbrev cellAction := inducedRepresentation F ζ hζ w m hm τB
 abbrev cellQuotient := OrdinaryCoinvariants F ζ hζ w
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
 abbrev cellMk := rootCoinvariantsMk
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
  (upperRoot F ζ hζ w) 1

theorem ordinary_cell_quotient_exact
    (hroot : ∀ x, τB (rootInBorel F ζ hζ w x) = 1)
    (i : E →ₗ[ℂ] cellQuotient F ζ hζ w m hm τB)
    (p : cellQuotient F ζ hζ w m hm τB →ₗ[ℂ] E)
    (hi : ∀ φ : KPJacquetOpenCell.TestFunctions F w (E := E),
      i (KPJacquetOpenTestFunction.ordinaryIntegral μ φ) =
        cellMk F ζ hζ w m hm τB
          (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB φ))
    (hp : ∀ f : Induced F ζ hζ w m τB,
      p (cellMk F ζ hζ w m hm τB f) = ev1 F ζ hζ w m τB f) :
    Function.Injective i ∧ LinearMap.range i = LinearMap.ker p ∧
      Function.Surjective p := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  letI : AddCommGroup (Induced F ζ hζ w m τB) := inferInstance
  letI : Module ℂ (Induced F ζ hζ w m τB) := inferInstance
  let K := KPRankOneInduction.LocalField F w
  let ρU := KPJacquetOpenTestFunction.translationRepresentation (K := K) (E := E)
  let ρV : Representation ℂ (Multiplicative K) (Induced F ζ hζ w m τB) :=
    (cellAction F ζ hζ w m hm τB).comp (upperRoot F ζ hζ w)
  let ρW : Representation ℂ (Multiplicative K) E := 1
  let ext := KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB
  let ev := ev1 F ζ hζ w m τB
  have hext : ∀ x φ, ext (ρU x φ) = ρV x (ext φ) := by
    intro x φ
    have he : ρU x φ = KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm
        τB hτB (rootInBorel F ζ hζ w x) φ := by
      apply Subtype.ext
      apply LocallyConstant.ext
      intro y
      exact (KPJacquetOpenCell.upperRoot_action F ζ hζ w m hm τB hτB hroot
        (Multiplicative.toAdd x) y φ).symm
    rw [he]
    exact KPJacquetOpenCell.ext_w_borel F ζ hζ w m hm τB hτB
      (rootInBorel F ζ hζ w x) φ
  have hV : KPCoinvariants.IsSmooth ρV := by
    intro f
    obtain ⟨J, hJ⟩ := (ev1_smooth_borel F ζ hζ w m hm τB hτB).1 f
    have hc : Continuous (upperRoot F ζ hζ w) :=
      (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1.comp continuous_toAdd
    let H := Representation.stabilizer ρV f
    have hH : IsOpen (H : Set (Multiplicative K)) :=
      Subgroup.isOpen_of_openSubgroup H
        (U := J.comap (upperRoot F ζ hζ w) hc)
        (by intro x hx; exact hJ _ hx)
    exact hH.preimage continuous_ofAdd
  let ie' : Representation.IntertwiningMap
      (rootTwistedRepresentation ρU (MonoidHom.id (Multiplicative K)) 1)
      (rootTwistedRepresentation (cellAction F ζ hζ w m hm τB) (upperRoot F ζ hζ w) 1) :=
    ⟨ext, by intro x; apply LinearMap.ext; intro φ
             simpa [rootTwistedRepresentation, ρV] using hext x φ⟩
  let I := Representation.Coinvariants.map _ _ ie'
  have hinj : Function.Injective I := by
    apply KPCoinvariants.TransversalAverages.coinvariants_map_injective_of_annihilating_averages
      _ _ ie' (KPJacquetOpenCell.ext_w_injective F ζ hζ w m hm τB hτB)
    intro v hv
    have htwV : KPCoinvariants.twistedRepresentation ρV 1 =
        rootTwistedRepresentation (cellAction F ζ hζ w m hm τB) (upperRoot F ζ hζ w) 1 := by
      apply MonoidHom.ext
      intro x
      apply LinearMap.ext
      intro f
      simp [KPCoinvariants.twistedRepresentation, rootTwistedRepresentation, ρV]
    have hv' : v ∈ Representation.Coinvariants.ker (KPCoinvariants.twistedRepresentation ρV 1) := by
      rw [htwV]
      exact hv
    obtain ⟨J, H, R, hJo, hJc, hHo, hHc, hJH, hR, hRne, hψ, hfix, hkill⟩ :=
      KPCoinvariants.killsRelation ρV hV 1 (by fun_prop) IsLocallyConstant.one v hv'
    refine ⟨R, hRne, ?_⟩
    simpa [KPCoinvariants.psiAverage, rootTwistedRepresentation, ρV] using hkill
  let L := KPJacquetOpenTestFunction.coinvariantsEquiv
    (K := K) (V := E) 1 (by fun_prop) μ
  have hI : ∀ a, I a = i (L a) := by
    intro a
    obtain ⟨φ, rfl⟩ := rootCoinvariantsMk_surjective ρU
      (MonoidHom.id (Multiplicative K)) 1 a
    exact (hi φ).symm
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hh : I (L.symm a) = I (L.symm b) := by simpa only [hI, L.apply_symm_apply] using hab
    exact L.symm.injective (hinj hh)
  · apply le_antisymm
    · rintro a ⟨e, rfl⟩
      obtain ⟨φ, hφ⟩ := KPJacquetOpenTestFunction.characterIntegral_surjective
        (K := K) (V := E) 1 (by fun_prop) μ e
      change p (i e) = 0
      rw [← hφ]
      change p (i (KPJacquetOpenTestFunction.ordinaryIntegral μ φ)) = 0
      rw [hi, hp]
      have hh : ext φ ∈ LinearMap.ker ev := by
        rw [← KPJacquetOpenCell.range_ext_w F ζ hζ w m hm τB hτB]
        exact LinearMap.mem_range_self ext φ
      exact hh
    · intro a ha
      obtain ⟨f, rfl⟩ := rootCoinvariantsMk_surjective
        (cellAction F ζ hζ w m hm τB) (upperRoot F ζ hζ w) 1 a
      have hf : ev f = 0 := (hp f).symm.trans ha
      have hr : f ∈ LinearMap.range ext := by
        rw [KPJacquetOpenCell.range_ext_w F ζ hζ w m hm τB hτB]
        exact hf
      obtain ⟨φ, hφ⟩ := hr
      exact ⟨KPJacquetOpenTestFunction.ordinaryIntegral μ φ, (hi φ).trans (congrArg _ hφ)⟩
  · intro e
    obtain ⟨f, hf⟩ := ev1_surjective F ζ hζ w m hm τB hm hτB e
    exact ⟨cellMk F ζ hζ w m hm τB f, (hp f).trans hf⟩

end DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.QuotientExactness

end

end

section
noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.OpenInjection

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain MeasureTheory
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
local instance : ValuativeRel (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w
local instance : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
local instance : MeasurableSpace (KPRankOneInduction.LocalField F w) := borel _
local instance : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  (τB : Representation ℂ (Borel F ζ hζ w) E)
  (hτB : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τB)
  (μ : Measure (KPRankOneInduction.LocalField F w)) [μ.IsAddHaarMeasure]

 abbrev cellAction := inducedRepresentation F ζ hζ w m hm τB
 abbrev cellQuotient := OrdinaryCoinvariants F ζ hζ w
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
 abbrev cellMk := rootCoinvariantsMk
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
  (upperRoot F ζ hζ w) 1

theorem open_injection_equivariant
    (σ : Representation ℂ (Torus F ζ hζ w) E)
    (ρJ : Representation ℂ (Torus F ζ hζ w)
      (cellQuotient F ζ hζ w m hm τB))
    (hρJ : ∀ h f,
      ρJ h (cellMk F ζ hζ w m hm τB f) =
      cellMk F ζ hζ w m hm τB
        (cellAction F ζ hζ w m hm τB h.val f))
    (i : E →ₗ[ℂ] cellQuotient F ζ hζ w m hm τB)
    (hi : ∀ φ : KPJacquetOpenCell.TestFunctions F w (E := E),
      i (KPJacquetOpenTestFunction.ordinaryIntegral μ φ) =
        cellMk F ζ hζ w m hm τB
          (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB φ))
    (hint : ∀ h φ,
      KPJacquetOpenTestFunction.ordinaryIntegral μ
        (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm τB hτB
          (torusInBorel F ζ hζ w m hm h) φ) =
      σ h (KPJacquetOpenTestFunction.ordinaryIntegral μ φ)) :
    ∀ h e, i (σ h e) = ρJ h (i e) := by
  intro h e
  obtain ⟨φ, hφ⟩ := KPJacquetOpenTestFunction.characterIntegral_surjective
    (K := KPRankOneInduction.LocalField F w) (V := E)
    (1 : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ)
    continuous_one μ e
  have hφ' : KPJacquetOpenTestFunction.ordinaryIntegral μ φ = e := by
    simpa only [KPJacquetOpenTestFunction.ordinaryIntegral] using hφ
  calc i (σ h e)
      = i (σ h (KPJacquetOpenTestFunction.ordinaryIntegral μ φ)) := by rw [hφ']
    _ = i (KPJacquetOpenTestFunction.ordinaryIntegral μ
          (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm τB hτB
            (torusInBorel F ζ hζ w m hm h) φ)) := by rw [hint h φ]
    _ = cellMk F ζ hζ w m hm τB
          (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB
            (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm τB hτB
              (torusInBorel F ζ hζ w m hm h) φ)) :=
          hi (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm τB hτB
              (torusInBorel F ζ hζ w m hm h) φ)
    _ = cellMk F ζ hζ w m hm τB
          (cellAction F ζ hζ w m hm τB h.val
            (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB φ)) := by
          rw [KPJacquetOpenCell.ext_w_borel F ζ hζ w m hm τB hτB
            (torusInBorel F ζ hζ w m hm h) φ]
          rfl
    _ = ρJ h (cellMk F ζ hζ w m hm τB
          (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB φ)) :=
          (hρJ h (KPJacquetOpenCell.ext_w F ζ hζ w m hm τB hτB φ)).symm
    _ = ρJ h (i e) := by rw [← hi φ, hφ']

end DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.OpenInjection

end

end

section
noncomputable section

set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.ClosedProjection

open scoped NumberField NNReal Classical
open NumberField IsDedekindDomain MeasureTheory
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)

local instance : ValuativeRel (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w

local instance : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w

local instance : MeasurableSpace (KPRankOneInduction.LocalField F w) := borel _

local instance : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  (τB : Representation ℂ (Borel F ζ hζ w) E)

 abbrev cellAction := inducedRepresentation F ζ hζ w m hm τB
 abbrev cellQuotient := OrdinaryCoinvariants F ζ hζ w
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
 abbrev cellMk := rootCoinvariantsMk
  (V := Induced F ζ hζ w m τB) (cellAction F ζ hζ w m hm τB)
  (upperRoot F ζ hζ w) 1

theorem closed_projection_equivariant
    (σ : Representation ℂ (Torus F ζ hζ w) E)
    (ρJ : Representation ℂ (Torus F ζ hζ w)
      (cellQuotient F ζ hζ w m hm τB))
    (hρJ : ∀ h f,
      ρJ h (cellMk F ζ hζ w m hm τB f) =
      cellMk F ζ hζ w m hm τB
        (cellAction F ζ hζ w m hm τB h.val f))
    (p : cellQuotient F ζ hζ w m hm τB →ₗ[ℂ] E)
    (hp : ∀ f : Induced F ζ hζ w m τB,
      p (cellMk F ζ hζ w m hm τB f) = ev1 F ζ hζ w m τB f)
    (hev : ∀ h f,
      ev1 F ζ hζ w m τB
        (cellAction F ζ hζ w m hm τB h.val f) =
      σ h (ev1 F ζ hζ w m τB f)) :
    ∀ h j, p (ρJ h j) = σ h (p j) := by
  have hsurj : ∀ j, ∃ f, cellMk F ζ hζ w m hm τB f = j := fun j =>
    rootCoinvariantsMk_surjective _ _ _ j
  intro h j
  obtain ⟨f, hf⟩ := hsurj j
  rw [← hf, hρJ h f, hp, hev h f, hp f]

end DedekindZetaZeroFree.KPJacquetOrdinaryCellExactness.ClosedProjection

end

end

section

noncomputable section

set_option maxHeartbeats 400000

namespace DedekindZetaZeroFree.KPJacquetOrdinaryCell

open scoped NumberField NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory
open KPLocalSmoothRepresentation KPJacquetClosedCellBump

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)
local instance : ValuativeRel (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F w
local instance : IsNonarchimedeanLocalField (KPRankOneInduction.LocalField F w) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F w
local instance : MeasurableSpace (KPRankOneInduction.LocalField F w) := borel _
local instance : BorelSpace (KPRankOneInduction.LocalField F w) := ⟨rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
  (τ : Representation ℂ (Torus F ζ hζ w) E)
  (hτ : letI := finiteCoverTopology F ζ hζ w m; SmoothRepresentation τ)

abbrev coefficientAction :=
  inflatedRepresentation F ζ hζ w
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ

include hm hτ in

theorem coefficientAction_smooth :
    letI := finiteCoverTopology F ζ hζ w m
    SmoothRepresentation (coefficientAction F ζ hζ w τ) := by
  exact inflatedRepresentation_smooth F ζ hζ w m hm
    (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ hm
    (KPLocalInductionJacquetReciprocity.borelRetraction_continuous F ζ hζ w m hm) hτ

abbrev principalAction :=
  inducedRepresentation F ζ hζ w m hm (coefficientAction F ζ hζ w τ)

abbrev Jacquet := OrdinaryCoinvariants F ζ hζ w
  (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ))
  (principalAction F ζ hζ w m hm τ)

abbrev jacquetMk := rootCoinvariantsMk
  (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ))
  (principalAction F ζ hζ w m hm τ) (upperRoot F ζ hζ w) 1

abbrev torusAction := KPLocalInductionJacquetReciprocity.jacquetAction F ζ hζ w
  (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ))
  (principalAction F ζ hζ w m hm τ)

 theorem sqrt_d_eq (h : Torus F ζ hζ w) :
    Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) =
      ((KPLocalInductionJacquetReciprocity.torusHalfModulus F ζ hζ w m hm h : ℝ≥0) : ℝ) := by
  symm
  exact KPRankOneInduction.halfModulus_eq _ _

def openWeight : Representation ℂ (Torus F ζ hζ w) E where
  toFun h := (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) •
    τ (KPJacquetOpenCell.alpha F ζ hζ w h)
  map_one' := by
    simp only [sqrt_d_eq, map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one, one_smul]
  map_mul' := by
    intro a b
    ext e
    simp only [sqrt_d_eq, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul,
      LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul, mul_comm]

def closedWeight : Representation ℂ (Torus F ζ hζ w) E where
  toFun h := (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) • τ h
  map_one' := by
    simp only [sqrt_d_eq, map_one, Units.val_one, NNReal.coe_one, Complex.ofReal_one, one_smul]
  map_mul' := by
    intro a b
    ext e
    simp only [sqrt_d_eq, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul,
      LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul, mul_comm]

 theorem ext_root (x : Multiplicative (KPRankOneInduction.LocalField F w))
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    KPJacquetOpenCell.ext_w F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
      (coefficientAction_smooth F ζ hζ w m hm τ hτ)
      (KPJacquetOpenTestFunction.translationRepresentation x φ) =
    principalAction F ζ hζ w m hm τ (upperRoot F ζ hζ w x)
      (KPJacquetOpenCell.ext_w F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
        (coefficientAction_smooth F ζ hζ w m hm τ hτ) φ) := by
  have hn : ∀ y, coefficientAction F ζ hζ w τ (rootInBorel F ζ hζ w y) = 1 := by
    intro y
    change τ (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
      (rootInBorel F ζ hζ w y)) = 1
    dsimp only [rootInBorel]
    rw [KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot]
    exact τ.map_one
  have he : KPJacquetOpenTestFunction.translationRepresentation x φ =
      KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
        (coefficientAction_smooth F ζ hζ w m hm τ hτ) (rootInBorel F ζ hζ w x) φ := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    exact (KPJacquetOpenCell.upperRoot_action F ζ hζ w m hm
      (coefficientAction F ζ hζ w τ) (coefficientAction_smooth F ζ hζ w m hm τ hτ)
      hn (Multiplicative.toAdd x) y φ).symm
  rw [he]
  exact KPJacquetOpenCell.ext_w_borel F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
    (coefficientAction_smooth F ζ hζ w m hm τ hτ) (rootInBorel F ζ hζ w x) φ

def openCoinvariantMap :
    KPJacquetOpenTestFunction.OrdinaryTranslationCoinvariants
      (KPRankOneInduction.LocalField F w) E →ₗ[ℂ] Jacquet F ζ hζ w m hm τ :=
  rootCoinvariantsLift
    (V := KPJacquetOpenCell.TestFunctions F w (E := E))
    (E := Jacquet F ζ hζ w m hm τ)
    KPJacquetOpenTestFunction.translationRepresentation
    (MonoidHom.id (Multiplicative (KPRankOneInduction.LocalField F w))) 1
    ⟨(jacquetMk F ζ hζ w m hm τ).comp
      (KPJacquetOpenCell.ext_w F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
        (coefficientAction_smooth F ζ hζ w m hm τ hτ)), by
        intro x φ
        change jacquetMk F ζ hζ w m hm τ
          (KPJacquetOpenCell.ext_w F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
            (coefficientAction_smooth F ζ hζ w m hm τ hτ)
            (KPJacquetOpenTestFunction.translationRepresentation x φ)) = (1 : ℂ) • _
        rw [ext_root F ζ hζ w m hm τ hτ x φ]
        with_reducible_and_instances
          exact rootCoinvariantsMk_equivariant
            (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ))
            (principalAction F ζ hζ w m hm τ) (upperRoot F ζ hζ w) 1 x _⟩

variable (μ : Measure (KPRankOneInduction.LocalField F w)) [μ.IsAddHaarMeasure]

def openInjection : E →ₗ[ℂ] Jacquet F ζ hζ w m hm τ :=
  (openCoinvariantMap F ζ hζ w m hm τ hτ).comp
    (KPJacquetOpenTestFunction.coinvariantsEquiv 1 (by fun_prop) μ).symm.toLinearMap

def closedProjection : Jacquet F ζ hζ w m hm τ →ₗ[ℂ] E := by
  let L : RootEquivariantMaps
      (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ))
      (principalAction F ζ hζ w m hm τ) (upperRoot F ζ hζ w) 1 E := by
    refine ⟨ev1 F ζ hζ w m (coefficientAction F ζ hζ w τ), ?_⟩
    intro x f
    change ev1 F ζ hζ w m (coefficientAction F ζ hζ w τ)
      (principalAction F ζ hζ w m hm τ (upperRoot F ζ hζ w x) f) = (1 : ℂ) • _
    rw [one_smul]
    exact ev1_upperRoot F ζ hζ w m hm
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ
      (fun x => KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot F ζ hζ w x) x f
  with_reducible_and_instances
    exact rootCoinvariantsLift
      (V := Induced F ζ hζ w m (coefficientAction F ζ hζ w τ)) (E := E)
      (principalAction F ζ hζ w m hm τ) (upperRoot F ζ hζ w) 1 L

theorem openInjection_integral (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    openInjection F ζ hζ w m hm τ hτ μ
      (KPJacquetOpenTestFunction.ordinaryIntegral μ φ) =
    jacquetMk F ζ hζ w m hm τ
      (KPJacquetOpenCell.ext_w F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
        (coefficientAction_smooth F ζ hζ w m hm τ hτ) φ) := by
  let e := KPJacquetOpenTestFunction.coinvariantsEquiv
    (V := E) (1 : Multiplicative (KPRankOneInduction.LocalField F w) →* ℂˣ) (by fun_prop) μ
  have he : e.symm (KPJacquetOpenTestFunction.ordinaryIntegral μ φ) =
      KPJacquetOpenTestFunction.coinvariantsMk 1 φ := by
    exact e.symm_apply_eq.mpr (KPJacquetOpenTestFunction.coinvariantsEquiv_mk 1 (by fun_prop) μ φ).symm
  change openCoinvariantMap F ζ hζ w m hm τ hτ (e.symm _) = _
  rw [he]
  rfl

private theorem intrinsicAbs_eq_norm (a : (KPRankOneInduction.LocalField F w)ˣ) :
    KPJacquetOpenTestFunction.localAbs a = ‖(a : KPRankOneInduction.LocalField F w)‖ := by
  let μ : Measure (KPRankOneInduction.LocalField F w) := Measure.addHaar
  have hmap : μ.map (ContinuousAddEquiv.mulLeft a) = ‖(a : KPRankOneInduction.LocalField F w)‖₊⁻¹ • μ := by
    have h := CompletionHaarModule.map_mul F w μ a
    have he : ENNReal.ofReal ‖(a : KPRankOneInduction.LocalField F w)‖ =
        (‖(a : KPRankOneInduction.LocalField F w)‖₊ : ℝ≥0∞) := by simp [enorm_eq_nnnorm]
    rw [he, ← ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr a.ne_zero)] at h
    exact h
  have hs := addEquivAddHaarChar_smul_map μ (ContinuousAddEquiv.mulLeft a)
  rw [hmap, smul_smul] at hs
  let c := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) * ‖(a : KPRankOneInduction.LocalField F w)‖₊⁻¹
  have he : c = 1 := by
    calc
      c = Measure.addHaarScalarFactor (c • μ) μ := by simp
      _ = 1 := by dsimp only [c]; simp only [hs, Measure.addHaarScalarFactor_self]
  have hn : ‖(a : KPRankOneInduction.LocalField F w)‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr a.ne_zero
  have hc : addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) = ‖(a : KPRankOneInduction.LocalField F w)‖₊ := by
    have he' := congrArg (fun x : ℝ≥0 => x * ‖(a : KPRankOneInduction.LocalField F w)‖₊) he
    simpa [c, mul_assoc, hn] using he'
  exact congrArg NNReal.toReal hc

theorem openIntegral_torus (h : Torus F ζ hζ w)
    (φ : KPJacquetOpenCell.TestFunctions F w (E := E)) :
    KPJacquetOpenTestFunction.ordinaryIntegral μ
      (KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm
        (coefficientAction F ζ hζ w τ)
        (coefficientAction_smooth F ζ hζ w m hm τ hτ)
        (torusInBorel F ζ hζ w m hm h) φ) =
    (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h) : ℂ) •
      τ (KPJacquetOpenCell.alpha F ζ hζ w h)
        (KPJacquetOpenTestFunction.ordinaryIntegral μ φ) := by
  let a := KPJacquetOpenCell.r F ζ hζ w m hm h
  let A : E →ₗ[ℂ] E := ((Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h))⁻¹ : ℂ) •
    τ (KPJacquetOpenCell.alpha F ζ hζ w h)
  have he : KPJacquetOpenCell.openCellRepresentation F ζ hζ w m hm
      (coefficientAction F ζ hζ w τ) (coefficientAction_smooth F ζ hζ w m hm τ hτ)
      (torusInBorel F ζ hζ w m hm h) φ = KPJacquetOpenTestFunction.dilateWith a A φ := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    have hh := KPJacquetOpenCell.torus_action F ζ hζ w m hm
      (coefficientAction F ζ hζ w τ) (coefficientAction_smooth F ζ hζ w m hm τ hτ) h x φ
    rw [KPJacquetOpenCell.tauW_inflation F ζ hζ w m hm
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ
      (fun h => KPLocalInductionJacquetReciprocity.borelRetraction_torus F ζ hζ w m hm h)] at hh
    exact hh
  rw [he, KPJacquetOpenTestFunction.ordinaryIntegral_dilateWith, intrinsicAbs_eq_norm]
  have hd : KPJacquetOpenCell.d F ζ hζ w m hm h = ‖(a : KPRankOneInduction.LocalField F w)‖ :=
    KPJacquetOpenCell.d_eq_abs_r F ζ hζ w m hm h
  have hp : 0 < KPJacquetOpenCell.d F ζ hζ w m hm h := by
    rw [hd]
    exact norm_pos_iff.mpr a.ne_zero
  change (‖(a : KPRankOneInduction.LocalField F w)‖ : ℂ) •
    (((Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h))⁻¹ : ℂ) •
      τ (KPJacquetOpenCell.alpha F ζ hζ w h) (KPJacquetOpenTestFunction.ordinaryIntegral μ φ)) = _
  rw [← hd, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 2
  calc
    KPJacquetOpenCell.d F ζ hζ w m hm h * (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h))⁻¹ =
        (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h)) ^ 2 *
          (Real.sqrt (KPJacquetOpenCell.d F ζ hζ w m hm h))⁻¹ := by rw [Real.sq_sqrt hp.le]
    _ = _ := by rw [sq, mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hp).ne', mul_one]

theorem ordinary_cell_short_exact :
    Function.Injective (openInjection F ζ hζ w m hm τ hτ μ) ∧
    LinearMap.range (openInjection F ζ hζ w m hm τ hτ μ) =
      LinearMap.ker (closedProjection F ζ hζ w m hm τ) ∧
    Function.Surjective (closedProjection F ζ hζ w m hm τ) ∧
    (∀ h e, openInjection F ζ hζ w m hm τ hτ μ (openWeight F ζ hζ w m hm τ h e) =
      torusAction F ζ hζ w m hm τ h (openInjection F ζ hζ w m hm τ hτ μ e)) ∧
    (∀ h j, closedProjection F ζ hζ w m hm τ (torusAction F ζ hζ w m hm τ h j) =
      closedWeight F ζ hζ w m hm τ h (closedProjection F ζ hζ w m hm τ j)) := by
  have hn : ∀ x, coefficientAction F ζ hζ w τ (rootInBorel F ζ hζ w x) = 1 := by
    intro x
    change τ (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w
      (rootInBorel F ζ hζ w x)) = 1
    dsimp only [rootInBorel]
    rw [KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot]
    exact τ.map_one
  obtain ⟨hi, hex, hp⟩ := KPJacquetOrdinaryCellExactness.QuotientExactness.ordinary_cell_quotient_exact
    F ζ hζ w m hm (coefficientAction F ζ hζ w τ)
    (coefficientAction_smooth F ζ hζ w m hm τ hτ) μ hn
    (openInjection F ζ hζ w m hm τ hτ μ) (closedProjection F ζ hζ w m hm τ)
    (openInjection_integral F ζ hζ w m hm τ hτ μ) (fun f => rfl)
  have hmk : ∀ h f,
      torusAction F ζ hζ w m hm τ h (jacquetMk F ζ hζ w m hm τ f) =
      jacquetMk F ζ hζ w m hm τ (principalAction F ζ hζ w m hm τ h.val f) := by
    intro h f
    rfl
  refine ⟨hi, hex, hp, ?_, ?_⟩
  · exact KPJacquetOrdinaryCellExactness.OpenInjection.open_injection_equivariant F ζ hζ w m hm
      (coefficientAction F ζ hζ w τ) (coefficientAction_smooth F ζ hζ w m hm τ hτ) μ
      (openWeight F ζ hζ w m hm τ) (torusAction F ζ hζ w m hm τ) hmk
      (openInjection F ζ hζ w m hm τ hτ μ)
      (openInjection_integral F ζ hζ w m hm τ hτ μ)
      (openIntegral_torus F ζ hζ w m hm τ hτ μ)
  · apply KPJacquetOrdinaryCellExactness.ClosedProjection.closed_projection_equivariant F ζ hζ w m hm
      (coefficientAction F ζ hζ w τ)
      (closedWeight F ζ hζ w m hm τ) (torusAction F ζ hζ w m hm τ) hmk
      (closedProjection F ζ hζ w m hm τ) (fun f => rfl)
    intro h f
    exact ev1_torus F ζ hζ w m hm
      (KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ w) τ
      (fun h => KPLocalInductionJacquetReciprocity.borelRetraction_torus F ζ hζ w m hm h) h f

end DedekindZetaZeroFree.KPJacquetOrdinaryCell

end

end
