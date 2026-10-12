module

public import DedekindZetaZeroFree.Adeles.Lattices.TraceIdealDuality

@[expose] public section

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/

/-
Extracted from `LeanPool/Odlyzko/CompletedZeta/FractionalShapeTheta.lean`,
https://github.com/LeanPool/lean-pool, pinned commit
`68aa6ee63d20ad76bcc15f595adfc72949991f06` (Lean 4.35.0-rc3), ported to rc2.
The original copyright and Apache-2.0 license are retained above, and the full
license is included in the repository root `LICENSE`.
-/

noncomputable section

section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def traceToEuclidean :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  (traceToMixed K).trans (mixedEmbedding.euclidean.toMixed K).symm

open Classical in
theorem traceIdealLattice_eq_comap_euclideanIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceIdealLattice K I =
      ZLattice.comap ℝ (euclideanIdealLattice K I)
        (traceToEuclidean K).toLinearMap := by
  rfl

open Classical in
private theorem divideBySqrtTwo_toLinearMap :
    (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap =
      (Real.sqrt 2)⁻¹ • LinearMap.id := by
  rfl

open Classical in
private theorem det_divideBySqrtTwo :
    LinearMap.det (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap = 2⁻¹ := by
  rw [divideBySqrtTwo_toLinearMap, LinearMap.det_smul]
  simp

omit [NumberField K] in
open Classical in
private theorem unscaleComplexCoordinates_toLinearMap :
    (unscaleComplexCoordinates K).toLinearMap =
      LinearMap.pi (fun w ↦
        (divideBySqrtTwo : ℂ ≃L[ℝ] ℂ).toLinearMap.comp
          (LinearMap.proj w)) := by
  apply LinearMap.ext
  intro z
  funext w
  simp [unscaleComplexCoordinates]

open Classical in
private theorem det_unscaleComplexCoordinates :
    LinearMap.det (unscaleComplexCoordinates K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  rw [unscaleComplexCoordinates_toLinearMap, LinearMap.det_pi]
  simp [det_divideBySqrtTwo]

open Classical in
private theorem det_traceToEuclidean :
    LinearMap.det (traceToEuclidean K).toLinearMap =
      (2⁻¹) ^ nrComplexPlaces K := by
  let u :=
    (ContinuousLinearEquiv.refl ℝ
      ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
        (unscaleComplexCoordinates K)
  have hmap :
      (traceToEuclidean K).toLinearMap =
        (mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
          (u.toLinearMap.comp
            (mixedEmbedding.euclidean.toMixed K).toLinearMap) := by
    rfl
  rw [hmap]
  rw [show LinearMap.det
      ((mixedEmbedding.euclidean.toMixed K).symm.toLinearMap.comp
        (u.toLinearMap.comp
          (mixedEmbedding.euclidean.toMixed K).toLinearMap)) =
      LinearMap.det u.toLinearMap by
        exact LinearMap.det_conj u.toLinearMap
          (mixedEmbedding.euclidean.toMixed K).symm.toLinearEquiv]
  change LinearMap.det
      (LinearMap.prodMap
        (LinearMap.id (R := ℝ)
          (M := {w : InfinitePlace K // IsReal w} → ℝ))
        (unscaleComplexCoordinates K).toLinearMap) = _
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    det_unscaleComplexCoordinates]

open Classical in
theorem covolume_comap_continuousLinearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : MeasureTheory.Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (e : E ≃L[ℝ] E) :
    ZLattice.covolume
        (ZLattice.comap ℝ L e.toLinearMap) μ =
      |LinearMap.det e.toLinearMap|⁻¹ *
        ZLattice.covolume L μ := by
  let b := Free.chooseBasis ℤ L
  have hfund :
      ZSpan.fundamentalDomain
          ((b.ofZLatticeComap ℝ L e.toLinearEquiv).ofZLatticeBasis
            ℝ (ZLattice.comap ℝ L e.toLinearMap)) =
        e ⁻¹'
          ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [← e.image_symm_eq_preimage, ← e.symm.coe_toLinearEquiv,
      ZSpan.map_fundamentalDomain]
    congr 1
    ext
    simp
  have hmeasure :
      μ (e ⁻¹' ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) =
        ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| *
          μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) := by
    exact MeasureTheory.Measure.addHaar_preimage_linearMap
      μ (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _
      μ
      (ZLattice.isAddFundamentalDomain
        (b.ofZLatticeComap ℝ L e.toLinearEquiv)
        μ),
    ZLattice.covolume_eq_measure_fundamentalDomain L
      μ (ZLattice.isAddFundamentalDomain b μ),
    hfund, MeasureTheory.measureReal_def,
    MeasureTheory.measureReal_def,
    hmeasure,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  simp

open Classical in
theorem covolume_traceIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceIdealLattice K I) =
      FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) *
        √|discr K| := by
  rw [traceIdealLattice_eq_comap_euclideanIdealLattice K I,
    covolume_comap_continuousLinearEquiv
      (euclideanIdealLattice K I) MeasureTheory.volume
      (traceToEuclidean K),
    det_traceToEuclidean,
    covolume_euclideanIdealLattice]
  have hpos : 0 < (2⁻¹ : ℝ) ^ nrComplexPlaces K := by positivity
  grind

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (mixedSpace K)ˣ where
  val := mixedSpaceOfRealSpace q
  inv := mixedSpaceOfRealSpace fun w ↦ (q w)⁻¹
  val_inv := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all
  inv_val := by
    rw [mixedSpaceOfRealSpace_apply, mixedSpaceOfRealSpace_apply]
    apply Prod.ext
    · funext w
      simp [hq w.1]
    · funext w
      simp_all

omit [NumberField K] in
open Classical in
@[simp]
theorem radialMixedSpaceUnit_val
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    (radialMixedSpaceUnit K q hq : mixedSpace K) =
      mixedSpaceOfRealSpace q :=
  rfl

open Classical in

noncomputable def traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  ((traceToMixed K).toLinearEquiv.trans
      ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ (mixedSpace K))).trans
    (traceToMixed K).symm.toLinearEquiv |>.toContinuousLinearEquiv

open Classical in
theorem traceToMixed_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceToMixed K (traceRadialScale K q hq v) =
      mixedSpaceOfRealSpace q * traceToMixed K v := by
  rw [traceRadialScale]
  simp

open Classical in
theorem inner_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v z : mixedEmbedding.euclidean.mixedSpace K) :
    inner ℝ (traceRadialScale K q hq v) z =
      inner ℝ v (traceRadialScale K q hq z) := by
  suffices
    (∑ w : {w : InfinitePlace K // IsReal w},
        (WithLp.fst z).ofLp w * (q w.1 * (WithLp.fst v).ofLp w)) +
      ∑ w : {w : InfinitePlace K // IsComplex w},
        (((WithLp.snd z).ofLp w).re *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).re) +
          ((WithLp.snd z).ofLp w).im *
            (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd v).ofLp w)).im)) =
      (∑ w : {w : InfinitePlace K // IsReal w},
          q w.1 * (WithLp.fst z).ofLp w * (WithLp.fst v).ofLp w) +
        ∑ w : {w : InfinitePlace K // IsComplex w},
          (Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).re *
              ((WithLp.snd v).ofLp w).re +
            Real.sqrt 2 *
              (q w.1 * divideBySqrtTwo ((WithLp.snd z).ofLp w)).im *
              ((WithLp.snd v).ofLp w).im) by
    simpa [traceRadialScale, traceToMixed, unscaleComplexCoordinates,
      mixedEmbedding.euclidean.toMixed, mixedSpaceOfRealSpace_apply,
      radialMixedSpaceUnit, WithLp.prod_inner_apply, PiLp.inner_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  apply congrArg₂ (· + ·)
  · grind
  · apply Finset.sum_congr rfl
    intro w _
    simp [divideBySqrtTwo]
    ring

open Classical in
theorem traceRadialScale_symm_apply
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    (traceRadialScale K q hq).symm v =
      traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w)) v := by
  apply (traceToMixed K).injective
  rw [traceToMixed_traceRadialScale]
  have h := traceToMixed_traceRadialScale K q hq
    ((traceRadialScale K q hq).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [mixedSpaceOfRealSpace_apply]
  apply Prod.ext
  · funext w
    have hw := congrFun (congrArg Prod.fst h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w =
      (q w.1)⁻¹ * (traceToMixed K v).1 w
    change (traceToMixed K v).1 w =
      q w.1 * (traceToMixed K ((traceRadialScale K q hq).symm v)).1 w at hw
    rw [hw]
    simp_all
  · funext w
    have hw := congrFun (congrArg Prod.snd h) w
    change (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w =
      ((↑((q w.1)⁻¹) : ℂ) * (traceToMixed K v).2 w)
    change (traceToMixed K v).2 w =
      (q w.1 : ℂ) *
        (traceToMixed K ((traceRadialScale K q hq).symm v)).2 w at hw
    rw [hw]
    simp_all

open Classical in
theorem traceConjugation_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    traceConjugation K (traceRadialScale K q hq v) =
      traceRadialScale K q hq (traceConjugation K v) := by
  suffices
    (fun w ↦ (Real.sqrt 2 : ℂ) *
        ((q w.1 : ℂ) *
          starRingEnd ℂ (divideBySqrtTwo ((WithLp.snd v).ofLp w)))) =
      (ContinuousLinearEquiv.piCongrRight
        (fun _ ↦ divideBySqrtTwo)).symm
          ((fun w ↦ (q w.1 : ℂ)) *
            (ContinuousLinearEquiv.piCongrRight
              (fun _ ↦ divideBySqrtTwo))
                (fun w ↦ starRingEnd ℂ ((WithLp.snd v).ofLp w))) by
    simpa [traceConjugation, traceRadialScale, traceToMixed,
      unscaleComplexCoordinates, mixedEmbedding.euclidean.toMixed,
      mixedSpaceOfRealSpace_apply, radialMixedSpaceUnit,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.prodCongr_symm, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.piCongrRight_symm_apply]
  funext w
  rw [ContinuousLinearEquiv.piCongrRight_symm_apply,
    divideBySqrtTwo_symm_apply]
  simp [divideBySqrtTwo]

open Classical in

noncomputable def shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (traceIdealLattice K I)
    (traceRadialScale K q hq).symm.toLinearMap

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    DiscreteTopology (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in
instance
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    IsZLattice ℝ (shapeIdealLattice K I q hq) := by
  unfold shapeIdealLattice
  infer_instance

open Classical in

noncomputable def conjugateShapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Submodule ℤ (mixedEmbedding.euclidean.mixedSpace K) :=
  (shapeIdealLattice K I q hq).map
    ((traceConjugation K).toLinearEquiv.restrictScalars ℤ).toLinearMap

open Classical in
theorem mem_conjugateShapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateShapeIdealLattice K I q hq ↔
      traceConjugation K v ∈ shapeIdealLattice K I q hq := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_conjugateTraceIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ conjugateTraceIdealLattice K I ↔
      traceConjugation K v ∈ traceIdealLattice K I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hv
    refine ⟨traceConjugation K v, hv, ?_⟩
    simp

open Classical in
theorem mem_dualLattice_shapeIdealLattice_iff
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    v ∈ dualLattice (shapeIdealLattice K I q hq) ↔
      traceRadialScale K q hq v ∈ dualLattice (traceIdealLattice K I) := by
  rw [mem_dualLattice_iff, mem_dualLattice_iff]
  constructor
  · intro hv x
    have hx :
        traceRadialScale K q hq (x : mixedEmbedding.euclidean.mixedSpace K) ∈
          shapeIdealLattice K I q hq := by
      change
        (traceRadialScale K q hq).symm
            (traceRadialScale K q hq
              (x : mixedEmbedding.euclidean.mixedSpace K)) ∈
          traceIdealLattice K I
      simp
    obtain ⟨n, hn⟩ := hv
      ⟨traceRadialScale K q hq
        (x : mixedEmbedding.euclidean.mixedSpace K), hx⟩
    exact ⟨n, (inner_traceRadialScale K q hq v x).trans hn⟩
  · intro hv z
    have hz :
        (traceRadialScale K q hq).symm
            (z : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      z.prop
    obtain ⟨n, hn⟩ := hv
      ⟨(traceRadialScale K q hq).symm
        (z : mixedEmbedding.euclidean.mixedSpace K), hz⟩
    refine ⟨n, ?_⟩
    rw [inner_traceRadialScale K q hq,
      ContinuousLinearEquiv.apply_symm_apply] at hn
    simp_all

open Classical in
theorem dualLattice_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLattice (shapeIdealLattice K I q hq) =
      conjugateShapeIdealLattice K (traceDualIdealUnit K I)
        (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  ext v
  rw [mem_dualLattice_shapeIdealLattice_iff,
    dualLattice_traceIdealLattice,
    mem_conjugateTraceIdealLattice_iff,
    mem_conjugateShapeIdealLattice_iff]
  change
    traceConjugation K (traceRadialScale K q hq v) ∈
        traceIdealLattice K (traceDualIdealUnit K I) ↔
      (traceRadialScale K (fun w ↦ (q w)⁻¹)
        (fun w ↦ inv_ne_zero (hq w))).symm (traceConjugation K v) ∈
        traceIdealLattice K (traceDualIdealUnit K I)
  rw [traceRadialScale_symm_apply,
    traceConjugation_traceRadialScale]
  simp

open Classical in
theorem traceRadialScale_traceEmbedding_mem_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) (x : K) :
    traceRadialScale K q hq (traceEmbedding K x) ∈
        shapeIdealLattice K I q hq ↔
      x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  change
    (traceRadialScale K q hq).symm
        (traceRadialScale K q hq (traceEmbedding K x)) ∈
          traceIdealLattice K I ↔ _
  rw [ContinuousLinearEquiv.symm_apply_apply,
    traceEmbedding_mem_traceIdealLattice]

open Classical in
theorem dualLatticeTheta_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    dualLatticeTheta (shapeIdealLattice K I q hq) Real.pi =
      latticeTheta
        (shapeIdealLattice K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w))) Real.pi := by
  rw [dualLatticeTheta, dualLattice_shapeIdealLattice,
    conjugateShapeIdealLattice]
  exact latticeTheta_map_linearIsometryEquiv
    (shapeIdealLattice K (traceDualIdealUnit K I)
      (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)))
    (traceConjugation K) Real.pi

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex Module NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

open mixedEmbedding

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
open Classical in
private theorem radialMixedSpaceUnit_toLinearMap
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
        (mixedSpace K)).toLinearMap =
      LinearMap.prodMap
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w)))
        (LinearMap.pi (fun w ↦
          (q w.1 • LinearMap.id).comp (LinearMap.proj w))) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]
  · funext w
    simp [radialMixedSpaceUnit, mixedSpaceOfRealSpace_apply]

open Classical in
theorem det_radialMixedSpaceUnit
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det
        ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
          (mixedSpace K)).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  rw [radialMixedSpaceUnit_toLinearMap,
    LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp [LinearMap.det_smul]

open Classical in
theorem det_traceRadialScale
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    LinearMap.det (traceRadialScale K q hq).toLinearMap =
      (∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2 := by
  let r :=
    ((radialMixedSpaceUnit K q hq).mulLeftLinearEquiv ℝ
      (mixedSpace K)).toLinearMap
  have hdet :
      LinearMap.det (traceRadialScale K q hq).toLinearMap =
        LinearMap.det r := by
    exact LinearMap.det_conj r (traceToMixed K).symm.toLinearEquiv
  rw [hdet]
  exact det_radialMixedSpaceUnit K q hq

open Classical in
theorem covolume_shapeIdealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ZLattice.covolume (shapeIdealLattice K I q hq) =
      |(∏ w : {w : InfinitePlace K // IsReal w}, q w.1) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, (q w.1) ^ 2| *
        (FractionalIdeal.absNorm
          (I : FractionalIdeal (𝓞 K)⁰ K) * √|discr K|) := by
  have hsymm :
      LinearMap.det (traceRadialScale K q hq).symm.toLinearMap =
        (LinearMap.det (traceRadialScale K q hq).toLinearMap)⁻¹ :=
    LinearEquiv.det_coe_symm (traceRadialScale K q hq).toLinearEquiv
  rw [shapeIdealLattice,
    covolume_comap_continuousLinearEquiv
      (traceIdealLattice K I) MeasureTheory.volume
      (traceRadialScale K q hq).symm,
    hsymm,
    det_traceRadialScale, abs_inv, inv_inv,
    covolume_traceIdealLattice]

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

section

open Complex NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

open Classical in

noncomputable def fractionalIdealElementShapeMap
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    shapeIdealLattice K I q hq :=
  ⟨traceRadialScale K q hq (traceEmbedding K (x : K)),
    (traceRadialScale_traceEmbedding_mem_shapeIdealLattice
      K I q hq _).2 x.prop⟩

open Classical in
theorem fractionalIdealElementShapeMap_bijective
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    Function.Bijective (fractionalIdealElementShapeMap K I q hq) := by
  constructor
  · intro x y hxy
    have htrace :
        traceEmbedding K (x : K) = traceEmbedding K (y : K) :=
      (traceRadialScale K q hq).injective (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply mixedEmbedding_injective K
    simpa [traceEmbedding] using congrArg (traceToMixed K) htrace
  · intro v
    have hv :
        (traceRadialScale K q hq).symm
            (v : mixedEmbedding.euclidean.mixedSpace K) ∈
          traceIdealLattice K I :=
      v.prop
    obtain ⟨x, hx, hxv⟩ :=
      exists_traceEmbedding_eq_of_mem_traceIdealLattice K I hv
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change traceRadialScale K q hq (traceEmbedding K x) = v
    simp_all

open Classical in

noncomputable def fractionalIdealElementShapeEquiv
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) ≃ shapeIdealLattice K I q hq :=
  Equiv.ofBijective (fractionalIdealElementShapeMap K I q hq)
    (fractionalIdealElementShapeMap_bijective K I q hq)

open Classical in
@[simp]
theorem fractionalIdealElementShapeEquiv_coe
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0)
    (x : ↥((I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)) :
    ((fractionalIdealElementShapeEquiv K I q hq x :
        shapeIdealLattice K I q hq) :
      mixedEmbedding.euclidean.mixedSpace K) =
      traceRadialScale K q hq (traceEmbedding K (x : K)) :=
  rfl

open Classical in

noncomputable def fractionalShapeIdealTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) : ℂ :=
  latticeTheta (shapeIdealLattice K I q hq) Real.pi

open Classical in
theorem fractionalShapeIdealTheta_poissonSummation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ w, q w ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      (Real.toNNReal
        (ZLattice.covolume (shapeIdealLattice K I q hq)))⁻¹ •
        fractionalShapeIdealTheta K (traceDualIdealUnit K I)
          (fun w ↦ (q w)⁻¹) (fun w ↦ inv_ne_zero (hq w)) := by
  rw [fractionalShapeIdealTheta,
    latticeGaussian_poissonSummation
      (shapeIdealLattice K I q hq) Real.pi_pos]
  have hpi : ((Real.pi : ℂ) / Real.pi) = 1 := by simp
  have hparam : Real.pi ^ 2 / Real.pi = Real.pi := by grind
  rw [hpi, one_cpow, one_mul, hparam,
    dualLatticeTheta_shapeIdealLattice]
  rfl

end DedekindZetaZeroFree.AbelianQuotient.Theta

end

end
