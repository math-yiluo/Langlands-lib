/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-! # Detecting tensor-to-Hom maps by local evaluation

Source: Stacks Tags 03EK and 03EO
(blueprint: lem-sf-tensor-hom-evaluation-ext).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory

namespace WeilConjectures.IntegralHom

attribute [local irreducible] SheafOfModules.monoidalCategory

section TensorExt

variable {C : Type c} [Category.{v} C] {R₀ : Cᵒᵖ ⥤ CommRingCat.{max c v r}}

-- Naturality recovers every slice from identity-slice evaluation.
private theorem hom_eval_ext
    {A B X : PresheafOfModules.{max c v r} (R₀ ⋙ forget₂ CommRingCat RingCat)}
    (f g : X ⟶ PresheafOfModules.homObj (R := R₀) A B)
    (h : ∀ U (s : X.obj U) (x : A.obj U),
      (f.app U s).app (op (Over.mk (𝟙 U.unop))) x =
        (g.app U s).app (op (Over.mk (𝟙 U.unop))) x) : f = g := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hf := congrArg (fun ξ ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) x)
    (PresheafOfModules.naturality_apply f W.unop.hom.op s)
  have hg := congrArg (fun ξ ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) x)
    (PresheafOfModules.naturality_apply g W.unop.hom.op s)
  have hfi := PresheafOfModules.restrictOver_hom_app_congr (f.app U s)
    (Category.id_comp W.unop.hom) x
  have hgi := PresheafOfModules.restrictOver_hom_app_congr (g.app U s)
    (Category.id_comp W.unop.hom) x
  exact hfi.symm.trans (hf.symm.trans ((h _ _ x).trans (hg.trans hgi)))

variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasWeakSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R₁ : Sheaf J CommRingCat.{max c v r})
  [(J.W.inverseImage (PresheafOfModules.toPresheaf.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj)).IsMonoidal]

/-- Maps from a sheaf tensor into an internal Hom are determined by evaluation
on pure tensors at every identity slice.
Source: Stacks Tags 03EK and 03EO; the uniqueness argument in blueprint
`lem-coef-integral-hom-reduction.proof.md`, paragraph 1
(blueprint: lem-sf-tensor-hom-evaluation-ext).

Proof: cancel the inverse tensor/sheafification comparison and apply the
sheafification Hom adjunction. For presheaf maps into internal Hom, naturality
recovers every slice component from evaluation at the identity of that slice.
Induction on presheaf tensors now reduces equality to the given pure-tensor
formula. The zero and sum cases follow from additivity. The argument works for
zero modules and the zero coefficient ring, and on an empty site. -/
theorem tensorHomEvaluation_ext
    (A B P N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁))
    (f g : (SheafOfModules.monoidalCategory R₁).tensorObj A B ⟶
      SheafOfModules.homObj (R := R₁) P N)
    (h : ∀ U (v : A.val.obj U) (z : B.val.obj U) (x : P.val.obj U),
      (f.val.app U ((SheafOfModules.tensorObjIsoSheafification A B).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj)).unit.app
            (A.val ⊗ B.val)).app U (v ⊗ₜ[R₁.obj.obj U] z)))).app
              (op (Over.mk (𝟙 U.unop))) x =
      (g.val.app U ((SheafOfModules.tensorObjIsoSheafification A B).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction.{max c v r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj)).unit.app
            (A.val ⊗ B.val)).app U (v ⊗ₜ[R₁.obj.obj U] z)))).app
              (op (Over.mk (𝟙 U.unop))) x) : f = g := by
  let e := SheafOfModules.tensorObjIsoSheafification (R := R₁) A B
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁).obj)
  apply (cancel_epi e.inv).1
  apply (adj.homEquiv (A.val ⊗ B.val) (SheafOfModules.homObj (R := R₁) P N)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply hom_eval_ext.{c, v, r}
  intro U s x
  induction s using TensorProduct.inductionOn with
  | tmul v z => exact h U v z x
  | add v z hv hz =>
    simp only [map_add]
    exact congrArg₂ (· + ·) hv hz

end TensorExt

end WeilConjectures.IntegralHom
