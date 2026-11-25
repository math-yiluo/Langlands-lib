/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalkPointwise
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GermComp

/-!
# Sections of lisse sheaves are determined by their germs

Let `F` be a lisse `ℓ`-adic sheaf on a scheme `Y` and `σ` a section of `F` over an object `W` of
the small pro-étale site of `Y`. If the germ of `σ` at every geometric point of `W` vanishes, then
`σ = 0` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_germ_eq_zero`). Indeed `σ` is
determined by its germ along the diagonal of `W ⟶ Y`, a global section of the lisse pullback of `F`
to `W`, whose restrictions to the geometric points of `W` are the germs of `σ`
(`AlgebraicGeometry.ProEtale.germ_comp`), and global sections of lisse sheaves are detected at
geometric points
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero'`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-- **A section of a lisse sheaf with vanishing germs vanishes.** A section `σ` over `W` of a
lisse sheaf whose germs at all geometric points of `W` vanish is zero. -/
theorem IsAdicLisseSheaf.eq_zero_of_germ_eq_zero {Y : Scheme.{u}} {F : AdicSheaf l Y}
    (hF : IsAdicLisseSheaf F) {W : Y.ProEt} (σ : ToType (F.X.obj.obj (op W)))
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (w : Spec (.of K) ⟶ W.left)
      (t : ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (w ≫ W.hom)).obj W),
      germ _ (w ≫ W.hom) F.X t σ = 0) :
    σ = 0 := by
  apply eq_zero_of_germ_diagLift_eq_zero W F.X σ
  obtain ⟨β, hβ⟩ := (bijective_globalSectionOfModHom ((W.hom)^*ᵃ[l].obj F)).2
    (germ _ W.hom F.X (diagLift W) σ)
  have hβ0 : β = 0 := by
    refine (hF.upperStar W.hom).eq_zero_of_globalSectionsToUpperStar_eq_zero' β fun y ↦ ?_
    let K := AlgebraicClosure (W.left.residueField y)
    let s : Spec (.of K) ⟶ W.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (W.left.residueField y) K)) ≫
        W.left.fromSpecResidueField y
    have hs : s.base (IsLocalRing.closedPoint K) = y :=
      W.left.fromSpecResidueField_apply y _
    refine ⟨y, K, inferInstance, inferInstance, s, specializes_rfl, specializes_of_eq hs.symm, ?_⟩
    have hc := congrArg (fun f ↦ f.hom σ) (germ_comp (WeilCoefficients.{u} l) s W.hom F.X
      (diagLift W) ((overPullbackObjMkIdIso s).inv ≫
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).map (diagLift W) ≫
        (MorphismProperty.Over.pullbackComp s W.hom).inv.app W)
      (by simp only [Category.assoc, Iso.inv_hom_id_app]; erw [Category.comp_id]))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    rw [h K s, map_zero] at hc
    rw [hβ]
    exact hc.symm
  rw [← hβ, hβ0, globalSectionOfModHom_eq]
  simp

end AlgebraicGeometry.ProEtale
