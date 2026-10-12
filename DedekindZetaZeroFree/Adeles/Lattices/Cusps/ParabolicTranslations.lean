module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RootGroups.ConjugatedFiniteLevel

@[expose] public section

noncomputable section
open scoped NumberField MatrixGroups
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false

theorem mem_parabolicL_of_rationalUnipotent_mem {F : Type} [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : KPCuspCharts.ParabolicData F S)
    (r : F) (hr : KPChamberBruhatTwoCells.rationalUnipotent F r ∈ S) : r ∈ D.L := by
  let A : Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, r; 0, 1] (by simp [Matrix.det_fin_two])
  let g : S := ⟨KPChamberBruhatTwoCells.rationalUnipotent F r, hr⟩
  have hA : Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) := rfl
  have hratio := D.ratioFormula g A hA (by simp [A])
  have h1 : D.ratio g = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [A] using hratio.symm
  have hker : g ∈ D.ratio.ker := h1
  rw [← D.exact] at hker
  obtain ⟨x, hx⟩ := hker
  let y : D.L := Multiplicative.toAdd x
  have hi : Matrix.ProjGenLinGroup.mk A =
      (D.inclusion (Multiplicative.ofAdd y) : KPCuspArithmetic.PGL2 F) := by
    simpa [y, hx] using hA
  have hparam := (D.unipotentFormula y A hi).2.2
  have hy : r = (y : F) := by simpa [A] using hparam
  rw [hy]
  exact y.property

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
