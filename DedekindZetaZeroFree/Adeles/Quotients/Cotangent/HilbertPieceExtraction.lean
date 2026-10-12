module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.EquivariantHilbertSum

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal BigOperators
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentPieceExtraction

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualCotangentCountableShrinking
open KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum
open KPContActualCotangentBorelRefinement
open KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (cover : CountableCover F ζ hζ U R P H)

def localCoefficient (v : Family (U := U) (H := H)) (n : ℕ)
    (y : (cover.chart n).domain) : E F :=
  coefficient v (cover.chart n) (coordinates (cover.chart n) y)

def e (v : Family (U := U) (H := H)) (n : ℕ) : (cover.chart n).domain → E F :=
  (liftedPiece cover n).indicator (localCoefficient cover v n)

theorem measurable_e (v : Family (U := U) (H := H)) (n : ℕ) :
    Measurable (e cover v n) := by
  have hs : MeasurableSet (liftedPiece cover n) :=
    (kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).lifted_measurable n
  have hlc : Measurable (localCoefficient cover v n) :=
    (v.property.1 (cover.chart n)).comp (coordinates_continuous (cover.chart n)).measurable
  exact hlc.indicator hs

theorem e_equivariant (v : Family (U := U) (H := H)) (n : ℕ)
    (γ : Gamma (cover.chart n)) (y : (cover.chart n).domain) :
    e cover v n (actualActionEquiv (cover.chart n) γ y) =
      actualTensor (cover.chart n) γ y (e cover v n y) := by
  show e cover v n ((cover.chart n).action γ.val.1 y) =
    actualTensor (cover.chart n) γ y (e cover v n y)
  have hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hmem : (cover.chart n).action γ.val.1 y ∈ liftedPiece cover n ↔
      y ∈ liftedPiece cover n := by
    have hinv := hp.lifted_invariant n γ.val.1
    constructor
    · intro h
      have h' : (cover.chart n).action γ.val.1 y ∈
          (cover.chart n).action γ.val.1 '' liftedPiece cover n := by rw [hinv]; exact h
      obtain ⟨z, hz, hzy⟩ := h'
      rw [(actualActionEquiv (cover.chart n) γ).injective hzy] at hz
      exact hz
    · intro h
      have h' : (cover.chart n).action γ.val.1 y ∈
          (cover.chart n).action γ.val.1 '' liftedPiece cover n := ⟨y, h, rfl⟩
      rwa [hinv] at h'
  by_cases hy : y ∈ liftedPiece cover n
  · have h2 : (cover.chart n).action γ.val.1 y ∈ liftedPiece cover n := hmem.mpr hy
    rw [show e cover v n ((cover.chart n).action γ.val.1 y) =
        localCoefficient cover v n ((cover.chart n).action γ.val.1 y) from
      Set.indicator_of_mem h2 _,
      show e cover v n y = localCoefficient cover v n y from Set.indicator_of_mem hy _]
    have hsub : coordinates (cover.chart n) ((cover.chart n).action γ.val.1 y) =
        ⟨(isotropyArrow (cover.chart n) γ).psi (coordinates (cover.chart n) y).val,
          isotropy_mem (cover.chart n) γ (coordinates (cover.chart n) y).val
            (coordinates (cover.chart n) y).property⟩ :=
      Subtype.ext (coordinates_action (cover.chart n) γ y)
    have hcov := v.property.2.1 (cover.chart n) γ (coordinates (cover.chart n) y).val
      (coordinates (cover.chart n) y).property
    simp only [localCoefficient, coefficient, actualTensor]
    rw [hsub, hcov]
  · have h2 : (cover.chart n).action γ.val.1 y ∉ liftedPiece cover n :=
      fun h => hy (hmem.mp h)
    rw [show e cover v n ((cover.chart n).action γ.val.1 y) = 0 from
        Set.indicator_of_notMem h2 _,
      show e cover v n y = 0 from Set.indicator_of_notMem hy _,
      map_zero]

theorem e_supported (v : Family (U := U) (H := H)) (n : ℕ)
    (y : (cover.chart n).domain) (hy : y ∉ liftedPiece cover n) :
    e cover v n y = 0 := by
  exact Set.indicator_of_notMem hy _

theorem enorm_eq_ofReal_norm (z : E F) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  rfl

theorem enorm_rpow_two (z : E F) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [enorm_eq_ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_two]

theorem toBase_eq_q (n : ℕ) (y : (cover.chart n).domain) :
    (cover.chart n).toBase y =
      KPContCotangentOverlapRationalBranches.q (cover.chart n)
        (coordinates (cover.chart n) y).val := by
  have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
      KPContCotangentActualOverlap.labeledA (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
        (KPContCotangentActualOverlap.labeledAInv (KPContCotangentActualOverlap.placeEquiv F ζ hζ)
          z) = z := by
    intro z; funext k; simp [KPContCotangentActualOverlap.labeledA,
      KPContCotangentActualOverlap.labeledAInv]
  simp only [ShrunkChart.toBase, KPContCotangentOverlapRationalBranches.q,
    coordinates, hi]

theorem memLp_e (v : Family (U := U) (H := H)) (hv : squareFinite v) (n : ℕ) :
    MemLp (e cover v n) 2 (cover.chart n).liftedMeasure := by
  have hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hs : MeasurableSet (liftedPiece cover n) := hp.lifted_measurable n
  have hf : Measurable (localCoefficient cover v n) :=
    (v.property.1 (cover.chart n)).comp (coordinates_continuous (cover.chart n)).measurable
  have hpt : ∀ y : (cover.chart n).domain,
      ENNReal.ofReal (normSquare v ((cover.chart n).toBase y) : ℝ) =
        ENNReal.ofReal (‖localCoefficient cover v n y‖ ^ 2) := by
    intro y
    rw [toBase_eq_q cover n y, normSquare_chart]
    simp only [localCoefficient, coefficient]
    norm_num
  have hfin_tsum : (∑' k, ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare v ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) < ⊤ := by
    have hbase : Measurable (fun x => ENNReal.ofReal (normSquare v x : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_normSquare v).coe_nnreal_real
    rw [← hp.lintegral_eq_tsum (fun x => ENNReal.ofReal (normSquare v x : ℝ)) hbase]
    exact hv
  have hterm : (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (normSquare v ((cover.chart n).toBase y) : ℝ)
        ∂(cover.chart n).liftedMeasure) < ⊤ :=
    lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare v ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) n) hfin_tsum
  have hfin : (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (‖localCoefficient cover v n y‖ ^ 2)
        ∂(cover.chart n).liftedMeasure) < ⊤ := by
    simpa only [hpt] using hterm
  refine memLp_iff.mpr ?_
  rw [show e cover v n = (liftedPiece cover n).indicator (localCoefficient cover v n) from rfl,
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      hf.stronglyMeasurable.aestronglyMeasurable]
  simpa only [enorm_rpow_two, ENNReal.toReal_ofNat] using hfin

def pieceLp (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    Lp (E F) 2 (cover.chart n).liftedMeasure :=
  (memLp_e cover v.val v.property n).toLp (e cover v.val n)

theorem pieceLp_mem_Q (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    pieceLp cover v n ∈ Q cover n := by
  have hcoe : ⇑(pieceLp cover v n) =ᵐ[(localData (cover.chart n)).measure] e cover v.val n :=
    MemLp.coeFn_toLp _
  refine ⟨?_, ?_⟩
  · intro γ
    have h1 : (fun x : (cover.chart n).domain =>
          pieceLp cover v n ((localData (cover.chart n)).action γ x))
        =ᵐ[(localData (cover.chart n)).measure]
        (fun x => e cover v.val n ((localData (cover.chart n)).action γ x)) :=
      (((localData (cover.chart n)).invariant_measure γ).quasiMeasurePreserving).ae_eq_comp hcoe
    have h2 : (fun x => e cover v.val n (actualActionEquiv (cover.chart n) γ x))
        =ᵐ[(localData (cover.chart n)).measure]
        (fun x => actualTensor (cover.chart n) γ x (e cover v.val n x)) :=
      Filter.Eventually.of_forall fun x => e_equivariant cover v.val n γ x
    have h3 : (fun x => actualTensor (cover.chart n) γ x (e cover v.val n x))
        =ᵐ[(localData (cover.chart n)).measure]
        (fun x => actualTensor (cover.chart n) γ x (pieceLp cover v n x)) :=
      hcoe.mono fun x hx => congrArg (actualTensor (cover.chart n) γ x) hx.symm
    exact h1.trans (h2.trans h3)
  · filter_upwards [hcoe] with x hx
    intro hy
    exact hx.trans (e_supported cover v.val n x hy)

def component (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) : Q cover n :=
  ⟨pieceLp cover v n, pieceLp_mem_Q cover v n⟩

private theorem local_lintegral_lt_top (v : Family (U := U) (H := H)) (hv : squareFinite v)
    (n : ℕ) :
    (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (‖localCoefficient cover v n y‖ ^ 2)
        ∂(cover.chart n).liftedMeasure) < ⊤ := by
  have hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hpt : ∀ y : (cover.chart n).domain,
      ENNReal.ofReal (normSquare v ((cover.chart n).toBase y) : ℝ) =
        ENNReal.ofReal (‖localCoefficient cover v n y‖ ^ 2) := by
    intro y
    rw [toBase_eq_q cover n y, normSquare_chart]
    simp only [localCoefficient, coefficient]
    norm_num
  have hfin_tsum : (∑' k, ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare v ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) < ⊤ := by
    have hbase : Measurable (fun x => ENNReal.ofReal (normSquare v x : ℝ)) :=
      ENNReal.measurable_ofReal.comp (measurable_normSquare v).coe_nnreal_real
    rw [← hp.lintegral_eq_tsum (fun x => ENNReal.ofReal (normSquare v x : ℝ)) hbase]
    exact hv
  have hterm : (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (normSquare v ((cover.chart n).toBase y) : ℝ)
        ∂(cover.chart n).liftedMeasure) < ⊤ :=
    lt_of_le_of_lt (ENNReal.le_tsum (f := fun k => ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare v ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) n) hfin_tsum
  simpa only [hpt] using hterm

theorem component_normSquare (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (‖localCoefficient cover v.val n y‖ ^ 2)
        ∂(cover.chart n).liftedMeasure) =
      ENNReal.ofReal (‖component cover v n‖ ^ 2) := by
  have hs : MeasurableSet (liftedPiece cover n) :=
    (kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).lifted_measurable n
  have hf : Measurable (localCoefficient cover v.val n) :=
    (v.val.property.1 (cover.chart n)).comp (coordinates_continuous (cover.chart n)).measurable
  have hfin := local_lintegral_lt_top cover v.val v.property n
  have hB_eq : (∫⁻ y in liftedPiece cover n,
        ENNReal.ofReal (‖localCoefficient cover v.val n y‖ ^ 2)
          ∂(cover.chart n).liftedMeasure)
      = ∫⁻ y in liftedPiece cover n, ‖localCoefficient cover v.val n y‖ₑ ^ (2 : ℝ)
          ∂(cover.chart n).liftedMeasure :=
    lintegral_congr fun y => (enorm_rpow_two (localCoefficient cover v.val n y)).symm
  have hE : eLpNorm (localCoefficient cover v.val n) 2
        ((cover.chart n).liftedMeasure.restrict (liftedPiece cover n))
      = (∫⁻ y in liftedPiece cover n,
          ENNReal.ofReal (‖localCoefficient cover v.val n y‖ ^ 2)
            ∂(cover.chart n).liftedMeasure) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        hf.stronglyMeasurable.aestronglyMeasurable,
      ENNReal.toReal_ofNat, ← hB_eq]
  have hEe : eLpNorm (e cover v.val n) 2 (cover.chart n).liftedMeasure
      = eLpNorm (localCoefficient cover v.val n) 2
          ((cover.chart n).liftedMeasure.restrict (liftedPiece cover n)) :=
    eLpNorm_indicator_eq_eLpNorm_restrict (p := 2) (f := localCoefficient cover v.val n) hs.nullMeasurableSet
  have hnorm : ‖component cover v n‖
      = (eLpNorm (e cover v.val n) 2 (cover.chart n).liftedMeasure).toReal := by
    change ‖pieceLp cover v n‖ = _
    exact Lp.norm_toLp _ _
  have hmain : ENNReal.ofReal (‖component cover v n‖ ^ 2)
      = ∫⁻ y in liftedPiece cover n,
          ENNReal.ofReal (‖localCoefficient cover v.val n y‖ ^ 2)
            ∂(cover.chart n).liftedMeasure := by
    rw [hnorm, hEe, hE, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
  exact hmain.symm

theorem tsum_component_normSquare (v : SquareFiniteFamily (U := U) (H := H)) :
    (∑' n, ENNReal.ofReal (‖component cover v n‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (normSquare v.val x : ℝ)
        ∂(baseMeasure (R := R) (P := P) (U := U)) := by
  have hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hbase : Measurable (fun x => ENNReal.ofReal (normSquare v.val x : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_normSquare v.val).coe_nnreal_real
  rw [hp.lintegral_eq_tsum (fun x => ENNReal.ofReal (normSquare v.val x : ℝ)) hbase]
  refine tsum_congr fun n => ?_
  rw [← component_normSquare cover v n]
  refine lintegral_congr fun y => ?_
  rw [toBase_eq_q cover n y, normSquare_chart]
  simp only [localCoefficient, coefficient]
  norm_num

theorem tsum_component_normSquare_lt_top (v : SquareFiniteFamily (U := U) (H := H)) :
    (∑' n, ENNReal.ofReal (‖component cover v n‖ ^ 2)) < ⊤ := by
  rw [tsum_component_normSquare cover v]
  exact v.property

theorem memℓp_component (v : SquareFiniteFamily (U := U) (H := H)) :
    Memℓp (component cover v) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hlt := tsum_component_normSquare_lt_top cover v
  have hne : (∑' n, ((‖component cover v n‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
    have heq : (∑' n, ((‖component cover v n‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞))
        = ∑' n, ENNReal.ofReal (‖component cover v n‖ ^ 2) :=
      tsum_congr fun n => by
        rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow]
        rfl
    rw [heq]
    exact hlt.ne
  have hsum : Summable fun n => ‖component cover v n‖ ^ 2 :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hne
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum

theorem component_eq_of_aeEquivalent
    (v w : SquareFiniteFamily (U := U) (H := H)) (hvw : AeEquivalent v.val w.val)
    (n : ℕ) : component cover v n = component cover w n := by
  apply Subtype.ext
  apply Lp.ext
  have hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
  have hs : MeasurableSet (liftedPiece cover n) := hp.lifted_measurable n
  have hmeas : Measurable (fun x => ENNReal.ofReal (normSquare (v.val - w.val) x : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_normSquare (v.val - w.val)).coe_nnreal_real
  have hzero : (∫⁻ x, ENNReal.ofReal (normSquare (v.val - w.val) x : ℝ)
      ∂(baseMeasure (R := R) (P := P) (U := U))) = 0 := by
    rw [lintegral_eq_zero_iff hmeas]
    filter_upwards [hvw] with x hx
    simp [hx]
  have hsum0 : (∑' k, ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare (v.val - w.val) ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) = 0 := by
    rw [← hp.lintegral_eq_tsum _ hmeas]
    exact hzero
  have hterm0 : (∫⁻ y in liftedPiece cover n,
      ENNReal.ofReal (normSquare (v.val - w.val) ((cover.chart n).toBase y) : ℝ)
        ∂(cover.chart n).liftedMeasure) = 0 :=
    le_antisymm (hsum0 ▸ ENNReal.le_tsum (f := fun k => ∫⁻ y in liftedPiece cover k,
      ENNReal.ofReal (normSquare (v.val - w.val) ((cover.chart k).toBase y) : ℝ)
        ∂(cover.chart k).liftedMeasure) n) (bot_le)
  have hm2 : Measurable (fun y : (cover.chart n).domain =>
      ENNReal.ofReal (normSquare (v.val - w.val) ((cover.chart n).toBase y) : ℝ)) :=
    hmeas.comp (cover.properties n).measurable
  have hae : ∀ᵐ y ∂(cover.chart n).liftedMeasure, y ∈ liftedPiece cover n →
      ENNReal.ofReal (normSquare (v.val - w.val) ((cover.chart n).toBase y) : ℝ) = 0 := by
    rw [← setLIntegral_eq_zero_iff hs hm2]
    exact hterm0
  have hcoe_v : ⇑(pieceLp cover v n) =ᵐ[(cover.chart n).liftedMeasure] e cover v.val n :=
    MemLp.coeFn_toLp _
  have hcoe_w : ⇑(pieceLp cover w n) =ᵐ[(cover.chart n).liftedMeasure] e cover w.val n :=
    MemLp.coeFn_toLp _
  have hee : e cover v.val n =ᵐ[(cover.chart n).liftedMeasure] e cover w.val n := by
    filter_upwards [hae] with y hy
    by_cases hyy : y ∈ liftedPiece cover n
    · change (liftedPiece cover n).indicator (localCoefficient cover v.val n) y =
        (liftedPiece cover n).indicator (localCoefficient cover w.val n) y
      rw [Set.indicator_of_mem hyy _, Set.indicator_of_mem hyy _]
      have hns : normSquare (v.val - w.val) ((cover.chart n).toBase y) = 0 := by
        have h1 := hy hyy
        rw [ENNReal.ofReal_eq_zero] at h1
        exact NNReal.coe_eq_zero.mp (le_antisymm h1 (by positivity))
      have hsq : ‖coefficient (v.val - w.val) (cover.chart n)
          (coordinates (cover.chart n) y)‖₊ ^ 2 = 0 := by
        rw [← normSquare_chart (v.val - w.val) (cover.chart n)
            (coordinates (cover.chart n) y), ← toBase_eq_q cover n y]
        exact hns
      have hz : coefficient (v.val - w.val) (cover.chart n)
          (coordinates (cover.chart n) y) = 0 :=
        nnnorm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      have hcoeff : coefficient v.val (cover.chart n) (coordinates (cover.chart n) y)
          = coefficient w.val (cover.chart n) (coordinates (cover.chart n) y) := by
        have hsub : coefficient v.val (cover.chart n) (coordinates (cover.chart n) y)
            - coefficient w.val (cover.chart n) (coordinates (cover.chart n) y) = 0 := by
          simpa only [coefficient, Submodule.coe_sub, Pi.sub_apply] using hz
        exact sub_eq_zero.mp hsub
      simpa only [localCoefficient] using hcoeff
    · change (liftedPiece cover n).indicator (localCoefficient cover v.val n) y =
        (liftedPiece cover n).indicator (localCoefficient cover w.val n) y
      rw [Set.indicator_of_notMem hyy _, Set.indicator_of_notMem hyy _]
  exact hcoe_v.trans (hee.trans hcoe_w.symm)

theorem localCoefficient_add (v w : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    localCoefficient cover (v + w).val n
      = localCoefficient cover v.val n + localCoefficient cover w.val n := by
  funext y
  simp only [localCoefficient, coefficient, Submodule.coe_add, Pi.add_apply]

theorem component_add (v w : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    component cover (v + w) n = component cover v n + component cover w n := by
  apply Subtype.ext
  show pieceLp cover (v + w) n = pieceLp cover v n + pieceLp cover w n
  apply Lp.ext
  have hcoe_vw : ⇑(pieceLp cover (v + w) n)
      =ᵐ[(cover.chart n).liftedMeasure] e cover (v + w).val n := MemLp.coeFn_toLp _
  have hcoe_v : ⇑(pieceLp cover v n)
      =ᵐ[(cover.chart n).liftedMeasure] e cover v.val n := MemLp.coeFn_toLp _
  have hcoe_w : ⇑(pieceLp cover w n)
      =ᵐ[(cover.chart n).liftedMeasure] e cover w.val n := MemLp.coeFn_toLp _
  have hfun : e cover (v + w).val n = e cover v.val n + e cover w.val n := by
    funext y
    by_cases hyy : y ∈ liftedPiece cover n
    · change (liftedPiece cover n).indicator (localCoefficient cover (v + w).val n) y =
        (liftedPiece cover n).indicator (localCoefficient cover v.val n) y
          + (liftedPiece cover n).indicator (localCoefficient cover w.val n) y
      rw [Set.indicator_of_mem hyy _, Set.indicator_of_mem hyy _, Set.indicator_of_mem hyy _,
        localCoefficient_add cover v w n, Pi.add_apply]
    · change (liftedPiece cover n).indicator (localCoefficient cover (v + w).val n) y =
        (liftedPiece cover n).indicator (localCoefficient cover v.val n) y
          + (liftedPiece cover n).indicator (localCoefficient cover w.val n) y
      rw [Set.indicator_of_notMem hyy _, Set.indicator_of_notMem hyy _,
        Set.indicator_of_notMem hyy _, zero_add]
  have hptE : e cover (v + w).val n =ᵐ[(cover.chart n).liftedMeasure]
      (e cover v.val n + e cover w.val n) :=
    Filter.Eventually.of_forall fun y => congrFun hfun y
  exact hcoe_vw.trans (hptE.trans
    ((hcoe_v.symm.add hcoe_w.symm).trans (Lp.coeFn_add _ _).symm))

theorem localCoefficient_smul (c : ℂ) (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    localCoefficient cover (c • v).val n = c • localCoefficient cover v.val n := by
  funext y
  simp only [localCoefficient, coefficient, Submodule.coe_smul, Pi.smul_apply]

theorem component_smul (c : ℂ) (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    component cover (c • v) n = c • component cover v n := by
  apply Subtype.ext
  show pieceLp cover (c • v) n = c • pieceLp cover v n
  apply Lp.ext
  have hcoe_cv : ⇑(pieceLp cover (c • v) n)
      =ᵐ[(cover.chart n).liftedMeasure] e cover (c • v).val n := MemLp.coeFn_toLp _
  have hcoe_v : ⇑(pieceLp cover v n)
      =ᵐ[(cover.chart n).liftedMeasure] e cover v.val n := MemLp.coeFn_toLp _
  have hfun : e cover (c • v).val n = c • e cover v.val n := by
    funext y
    by_cases hyy : y ∈ liftedPiece cover n
    · change (liftedPiece cover n).indicator (localCoefficient cover (c • v).val n) y =
        c • (liftedPiece cover n).indicator (localCoefficient cover v.val n) y
      rw [Set.indicator_of_mem hyy _, Set.indicator_of_mem hyy _,
        localCoefficient_smul cover c v n, Pi.smul_apply]
    · change (liftedPiece cover n).indicator (localCoefficient cover (c • v).val n) y =
        c • (liftedPiece cover n).indicator (localCoefficient cover v.val n) y
      rw [Set.indicator_of_notMem hyy _, Set.indicator_of_notMem hyy _, smul_zero]
  have hptE : e cover (c • v).val n =ᵐ[(cover.chart n).liftedMeasure]
      (c • e cover v.val n) :=
    Filter.Eventually.of_forall fun y => congrFun hfun y
  exact hcoe_cv.trans (hptE.trans
    ((hcoe_v.symm.const_smul c).trans (Lp.coeFn_smul c _).symm))

def extractFamily (v : SquareFiniteFamily (U := U) (H := H)) : PieceHilbert cover :=
  ⟨component cover v, memℓp_component cover v⟩

theorem extractFamily_eq_of_aeEquivalent (v w : SquareFiniteFamily (U := U) (H := H))
    (hvw : AeEquivalent v.val w.val) : extractFamily cover v = extractFamily cover w := by
  apply lp.ext
  funext n
  exact component_eq_of_aeEquivalent cover v w hvw n

theorem Quotient_lift_toAeQuotient
    (h : ∀ a b, Submodule.quotientRel (R := ℂ)
      (M := SquareFiniteFamily (U := U) (H := H))
      (nullSubmodule (U := U) (H := H)) a b →
      extractFamily cover a = extractFamily cover b)
    (v : SquareFiniteFamily (U := U) (H := H)) :
    Quotient.lift (extractFamily cover) h (toAeQuotient v) = extractFamily cover v := by
  show Quotient.lift (extractFamily cover) h (Quotient.mk'' v) = extractFamily cover v
  rw [Quotient.mk''_eq_mk]
  exact Quotient.lift_mk _ _ v

def extractionLinear : SquareFiniteFamily (U := U) (H := H) →ₗ[ℂ] PieceHilbert cover where
  toFun := extractFamily cover
  map_add' := by
    intro x y
    apply lp.ext
    funext n
    exact component_add cover x y n
  map_smul' := by
    intro c x
    apply lp.ext
    funext n
    exact component_smul cover c x n

theorem ext_welldef (a b : SquareFiniteFamily (U := U) (H := H))
    (hab : Submodule.quotientRel (R := ℂ) (M := SquareFiniteFamily (U := U) (H := H))
      (nullSubmodule (U := U) (H := H)) a b) :
    extractFamily cover a = extractFamily cover b := by
  refine extractFamily_eq_of_aeEquivalent cover a b
    ((toAeQuotient_eq_iff (U := U) (H := H) a b).mp ?_)
  exact Quotient.sound hab

set_option maxHeartbeats 1000000 in

def Ext : CotangentAeQuotient (U := U) (H := H) →ₗ[ℂ] PieceHilbert cover where
  toFun := Quotient.lift (extractFamily cover) (ext_welldef cover)
  map_add' := by
    intro a b
    obtain ⟨v, rfl⟩ := toAeQuotient_surjective (U := U) (H := H) a
    obtain ⟨w, rfl⟩ := toAeQuotient_surjective (U := U) (H := H) b
    rw [← toAeQuotient_add (U := U) (H := H)]
    rw [Quotient_lift_toAeQuotient cover (ext_welldef cover) (v + w),
      Quotient_lift_toAeQuotient cover (ext_welldef cover) v,
      Quotient_lift_toAeQuotient cover (ext_welldef cover) w]
    exact map_add (extractionLinear cover) v w
  map_smul' := by
    intro c a
    obtain ⟨v, rfl⟩ := toAeQuotient_surjective (U := U) (H := H) a
    rw [← toAeQuotient_smul (U := U) (H := H)]
    rw [Quotient_lift_toAeQuotient cover (ext_welldef cover) (c • v),
      Quotient_lift_toAeQuotient cover (ext_welldef cover) v]
    exact map_smul (extractionLinear cover) c v

theorem Ext_toAeQuotient (v : SquareFiniteFamily (U := U) (H := H)) :
    Ext cover (toAeQuotient v) = extractFamily cover v :=
  Quotient_lift_toAeQuotient cover (ext_welldef cover) v

theorem Ext_component (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ) :
    Ext cover (toAeQuotient v) n = component cover v n := by
  rw [Ext_toAeQuotient cover v]
  rfl

end DedekindZetaZeroFree.KPContActualCotangentPieceExtraction

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking KPContActualCotangentMeasurableFamilies
open KPContActualCotangentPieceHilbertSum KPContActualCotangentPieceExtraction
open KPContActualCotangentBorelRefinement KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

theorem kp_cont_actual_cotangent_piece_extraction
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : CountableCover F ζ hζ U R P H) :
    (∀ v : Family (U := U) (H := H), squareFinite v → ∀ n : ℕ,
      Measurable (e cover v n) ∧
      (∀ (γ : Gamma (cover.chart n)) (y : (cover.chart n).domain),
        e cover v n (actualActionEquiv (cover.chart n) γ y) =
          actualTensor (cover.chart n) γ y (e cover v n y)) ∧
      (∀ y : (cover.chart n).domain, y ∉ liftedPiece cover n → e cover v n y = 0) ∧
      MemLp (e cover v n) 2 (cover.chart n).liftedMeasure) ∧
    (∀ (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ),
      (∫⁻ y in liftedPiece cover n,
        ENNReal.ofReal (‖localCoefficient cover v.val n y‖ ^ 2)
          ∂(cover.chart n).liftedMeasure) = ENNReal.ofReal (‖component cover v n‖ ^ 2)) ∧
    (∀ v : SquareFiniteFamily (U := U) (H := H),
      (∑' n, ENNReal.ofReal (‖component cover v n‖ ^ 2)) =
        (∫⁻ x, ENNReal.ofReal (normSquare v.val x : ℝ)
          ∂(baseMeasure (R := R) (P := P) (U := U))) ∧
      (∑' n, ENNReal.ofReal (‖component cover v n‖ ^ 2)) < ⊤ ∧
      Memℓp (component cover v) 2) ∧
    (∀ v w : SquareFiniteFamily (U := U) (H := H), AeEquivalent v.val w.val →
      ∀ n, component cover v n = component cover w n) ∧
    (∀ (v w : SquareFiniteFamily (U := U) (H := H)) (n : ℕ),
      component cover (v + w) n = component cover v n + component cover w n) ∧
    (∀ (c : ℂ) (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ),
      component cover (c • v) n = c • component cover v n) ∧
    (∀ (v : SquareFiniteFamily (U := U) (H := H)) (n : ℕ),
      Ext cover (toAeQuotient v) n = component cover v n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv n
    exact ⟨measurable_e cover v n, fun γ y => e_equivariant cover v n γ y,
      fun y hy => e_supported cover v n y hy, memLp_e cover v hv n⟩
  · intro v n
    exact component_normSquare cover v n
  · intro v
    exact ⟨tsum_component_normSquare cover v, tsum_component_normSquare_lt_top cover v,
      memℓp_component cover v⟩
  · intro v w hvw n
    exact component_eq_of_aeEquivalent cover v w hvw n
  · intro v w n
    exact component_add cover v w n
  · intro c v n
    exact component_smul cover c v n
  · intro v n
    exact Ext_component cover v n

end DedekindZetaZeroFree

end
