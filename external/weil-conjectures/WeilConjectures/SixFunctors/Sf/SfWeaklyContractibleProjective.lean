/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Exact evaluation and projective finite free module sheaves

Source: Stacks Project, Tag 0946.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Exact evaluation at the terminal object makes every finite free module sheaf
projective, with an independent coefficient universe.

Source: Stacks Project, Tag 0946
(blueprint: lem-sf-weakly-contractible-projective).
Proof: forgetting the module structure sends an epimorphism to a locally surjective
map of abelian sheaves, then to an epimorphism of set sheaves. The evaluation hypothesis
makes its map on terminal sections surjective. Evaluation preserves kernels sectionwise,
so it preserves homology. A map from the unit module is a global section. A section at
the terminal object extends to a compatible family by restriction along the unique
arrows to that object. Lift that terminal section along the epimorphism; its restrictions
then lift the given map. Finite products are finite biproducts of these projectives,
including the empty product, which is zero. -/
theorem sf_weakly_contractible_projective (X : Scheme.{t})
    (hX : ∀ (F G : Sheaf (ProEt.topology X) (Type (max w (t + 1))))
      (f : F ⟶ G), Epi f →
        Function.Surjective (f.hom.app (op (ProEt.mk (𝟙 X)))))
    (C : Sheaf (ProEt.topology X) CommRingCat.{max w (t + 1)}) :
    (SheafOfModules.evaluation.{max w (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max w (t + 1)} RingCat.{max w (t + 1)})).obj C)
      (op (ProEt.mk (𝟙 X)))).PreservesHomology ∧
    ∀ r : ℕ, Projective (∏ᶜ fun _ : Fin r ↦ SheafOfModules.unit
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max w (t + 1)} RingCat.{max w (t + 1)})).obj C)) := by
  let := integralCoefficientAbSheafify.{t, w} X
  let := integralCoefficientAbLocallyBijective.{t, w} X
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{max w (t + 1)} RingCat.{max w (t + 1)})).obj C
  let W := ProEt.mk (𝟙 X)
  let ev := SheafOfModules.evaluation.{max w (t + 1)} A (op W)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf A).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat g).mpr inferInstance
    let g' := (sheafCompose (ProEt.topology X) (forget AddCommGrpCat)).map g
    have : Epi g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hX _ _ g' inferInstance)
  refine ⟨Functor.preservesHomology_of_preservesEpis_and_kernels ev, ?_⟩
  let a (V : X.ProEt) : V ⟶ W :=
    MorphismProperty.Over.homMk V.hom (Category.comp_id _)
  have ha {V Z : X.ProEt} (f : V ⟶ Z) : f ≫ a Z = a V :=
    MorphismProperty.Over.Hom.ext (MorphismProperty.Over.w f)
  have : Projective (SheafOfModules.unit A) := by
    constructor
    intro M N f e he
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (ev.map e)).mp inferInstance
      ((N.unitHomEquiv f).val (op W))
    change e.val.app (op W) x = _ at hx
    let s : M.sections := M.val.sectionsMk
      (fun V ↦ M.val.map (a V.unop).op x) (by
        intro V Z g
        rw [← M.val.map_comp_apply]
        have h : (a V.unop).op ≫ g = (a Z.unop).op := by
          exact congrArg Quiver.Hom.op (ha g.unop)
        rw [h])
    refine ⟨M.unitHomEquiv.symm s, ?_⟩
    apply N.unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    change e.val.app V (M.val.map (a V.unop).op x) = (N.unitHomEquiv f).val V
    rw [PresheafOfModules.naturality_apply, hx]
    exact PresheafOfModules.sections_property _ _
  let : HasFiniteBiproducts (SheafOfModules.{max w (t + 1)} A) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  intro r
  refine Projective.of_iso (biproduct.isoProduct
    (fun _ : Fin r ↦ SheafOfModules.unit A)) ⟨?_⟩
  intro M N f e he
  refine ⟨biproduct.desc (fun i ↦ Projective.factorThru
    (biproduct.ι (fun _ : Fin r ↦ SheafOfModules.unit A) i ≫ f) e), ?_⟩
  apply biproduct.hom_ext'
  intro i
  simp

end WeilConjectures
