module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology NNReal
namespace DedekindZetaZeroFree.KPActualReflectionData.AffineCompactConjugation
open KPGlobalResidualConstruction KPLiteralChamber
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem archChart_domain_injective (x y : ArchCoordinates F)
    (hx : x ∈ archDomain F) (hy : y ∈ archDomain F)
    (he : archChart F ζ hζ x = archChart F ζ hζ y) : x = y := by
  rw [right_insertion, right_insertion] at he
  have hinj := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.1
  have hp := hinj he
  funext w
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (congrFun hp w)
  have hmat := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 2) ℂ => M.val) hc
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    rightMatrix_val _ (hx w), rightMatrix_val _ (hy w)] at hmat
  have hc1 : (c : ℂ) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar] using congrArg (fun M => M 1 1) hmat
  have he0 : x w 0 = y w 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hc1] using congrArg (fun M => M 0 1) hmat
  have he2 : x w 2 = y w 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hc1] using congrArg (fun M => M 1 0) hmat
  have he1 : x w 1 = y w 1 := by
    have hh := congrArg (fun M => M 0 0) hmat
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hc1, he0, he2] at hh
    exact hh
  funext i
  fin_cases i
  · exact he0
  · exact he1
  · exact he2

private theorem base_domain : archBase F ∈ archDomain F := by
  intro w
  simp [archBase]

theorem rightChart_conjugation_local (k : G F ζ hζ) :
    ∃ (O : Set (ArchCoordinates F)) (c : ArchCoordinates F → ArchCoordinates F),
      IsOpen O ∧ archBase F ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) c O ∧
      Set.MapsTo c O (archDomain F) ∧ c (archBase F) = archBase F ∧
      ∀ x ∈ O, archChart F ζ hζ (c x) = k * archChart F ζ hζ x * k⁻¹ := by
  obtain ⟨O₁,q,hO₁,hb₁,hq,hqD,he₁⟩ :=
    literal_right_to_left_chart_local_transition F ζ hζ k (archBase F) (base_domain F)
  have hqbase : KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (q (archBase F)) = 1 := by
    have he := he₁ (archBase F) hb₁
    rw [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] at he
    apply mul_right_cancel (b := k)
    simpa only [one_mul] using he.symm
  obtain ⟨O₂,r,hO₂,hb₂,hr,hrD,he₂⟩ :=
    literal_group_chart_local_transition F ζ hζ (1 : G F ζ hζ) (q (archBase F)) (hqD hb₁)
  have hb : r (q (archBase F)) = archBase F := by
    apply archChart_domain_injective F ζ hζ _ _ (hrD hb₂) (base_domain F)
    have he := he₂ (q (archBase F)) hb₂
    simpa only [hqbase, one_mul, mul_one, KPInterface.ResidueConstruction.Raw.archChart_base] using he.symm
  let O := O₁ ∩ q ⁻¹' O₂
  refine ⟨O,r ∘ q,hq.continuousOn.isOpen_inter_preimage hO₁ hO₂,⟨hb₁,hb₂⟩,
    hr.comp (hq.mono Set.inter_subset_left) (fun x hx => hx.2),
    (fun x hx => hrD hx.2),hb,?_⟩
  intro x hx
  have ha := he₁ x hx.1
  rw [KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] at ha
  have hh := he₂ (q x) hx.2
  simp only [hqbase, one_mul, mul_one] at hh
  change archChart F ζ hζ (r (q x)) = _
  rw [← hh, ha]
  group

theorem right_derivative_conjugation
    (k : G F ζ hζ) :
    ∃ L : ArchCoordinates F →L[ℝ] ArchCoordinates F,
      ∀ (f : G F ζ hζ → ℂ)
        (hf : ∀ g, DifferentiableAt ℝ (fun x => f (g*archChart F ζ hζ x)) (archBase F))
        (X : ArchCoordinates F) (g : G F ζ hζ),
      fderiv ℝ (fun x => f ((g*k)*archChart F ζ hζ x)) (archBase F) X =
        fderiv ℝ (fun x => f ((g*archChart F ζ hζ x)*k)) (archBase F) (L X) := by
  obtain ⟨O,c,hO,hb,hc,hcD,hcb,he⟩ := rightChart_conjugation_local F ζ hζ k
  have hcd : DifferentiableAt ℝ c (archBase F) :=
    (hc.contDiffAt (hO.mem_nhds hb)).differentiableAt (by simp)
  refine ⟨fderiv ℝ c (archBase F),?_⟩
  intro f hf X g
  have hh : DifferentiableAt ℝ (fun x => f ((g*archChart F ζ hζ x)*k)) (archBase F) := by
    obtain ⟨O',d,hO',hb',hd,hdD,hdb,hed⟩ := rightChart_conjugation_local F ζ hζ k⁻¹
    have hdd : DifferentiableAt ℝ d (archBase F) :=
      (hd.contDiffAt (hO'.mem_nhds hb')).differentiableAt (by simp)
    have houter := (hf (g*k)).hasFDerivAt
    rw [← hdb] at houter
    have hcomp := houter.comp (archBase F) hdd.hasFDerivAt
    have heq : (fun x => f ((g*k)*archChart F ζ hζ (d x))) =ᶠ[nhds (archBase F)]
        (fun x => f ((g*archChart F ζ hζ x)*k)) := by
      filter_upwards [hO'.mem_nhds hb'] with x hx
      rw [hed x hx]
      congr 1
      group
    exact (hcomp.congr_of_eventuallyEq heq.symm).differentiableAt
  have houter := hh.hasFDerivAt
  rw [← hcb] at houter
  have hcomp := houter.comp (archBase F) hcd.hasFDerivAt
  rw [hcb] at hcomp
  have heq : (fun x => f ((g*archChart F ζ hζ (c x))*k)) =ᶠ[nhds (archBase F)]
      (fun x => f ((g*k)*archChart F ζ hζ x)) := by
    filter_upwards [hO.mem_nhds hb] with x hx
    rw [he x hx]
    congr 1
    group
  exact congrArg (fun D => D X) (hcomp.congr_of_eventuallyEq heq.symm).fderiv

end DedekindZetaZeroFree.KPActualReflectionData.AffineCompactConjugation

end
