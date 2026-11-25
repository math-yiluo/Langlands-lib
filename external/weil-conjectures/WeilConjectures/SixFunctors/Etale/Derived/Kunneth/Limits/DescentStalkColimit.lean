/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentStalk
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentGeometry
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.DescentColimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The system `pᵢ^* pᵢ_* F` on geometric stalks

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps and `F` an étale sheaf of `Λ`-modules on `X`. At every geometric point `x̄` of
`X`, the stalks of the counits `pᵢ^* pᵢ_* F ⟶ F` exhibit the stalk `F_x̄` as the colimit of the
stalks `(pᵢ^* pᵢ_* F)_x̄` (`AlgebraicGeometry.Etale.isColimitSheafFiberMapCoconeDescentCocone`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

section LowerStarComp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The components of the inverse of the composition isomorphism `(h₁)_* ⋙ (h₂)_* ≅ (h₁₂)_*`
of étale pushforwards are the restriction maps along the inverse pullback pasting
isomorphisms. -/
lemma lowerStarComp_inv_app_hom_app_of_eq (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (G : Sheaf T.smallEtaleTopology A) (V : R.Etaleᵒᵖ) :
    ((Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h₁ h₂ h₁₂
        hh₁₂).inv.app V.unop).op := by
  simp only [Etale.lowerStarComp, Functor.sheafPushforwardContinuousComp']
  exact Category.comp_id _

end LowerStarComp

/-- The inverse of the pullback pasting isomorphism `V ×_Z X ≅ (V ×_Z Y) ×_Y X`, followed by
the projection to `V`, is the composite of the two projections. -/
lemma pullbackComp_inv_app_left_fst {X Y Z : Scheme.{u}} (q : X ⟶ Y) (g : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = q ≫ g) (V : Z.Etale) :
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g r hr).inv.app V).left ≫
        pullback.fst V.hom r =
      pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V).hom q ≫
        pullback.fst V.hom g := by
  subst hr
  have h := MorphismProperty.Over.pullbackComp_left_fst_fst (P := @Etale) (Q := ⊤) q g V
  have h' := congrArg (fun φ ↦ φ.left)
    ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g).inv_hom_id_app V)
  calc _ = ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g).inv.app V).left ≫
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q g).hom.app V).left ≫
          pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V).hom q ≫
            pullback.fst V.hom g := (congrArg (_ ≫ ·) h).symm
    _ = _ := by
      rw [← Category.assoc]
      exact (congrArg (· ≫ _) h').trans (Category.id_comp _)

variable {Λ : Type (u + 1)}
 [CommRing Λ] {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ Scheme.{u}} {c : Cone D}

variable (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ c.pt)

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- Every element of the stalk `F_x̄` comes from the stalk of some `pᵢ^* pᵢ_* F`. -/
lemma exists_sheafFiber_map_counit_eq
    (y : (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj F) :
    ∃ (i : I) (z : (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
        ((c.π.app i)^*[ModuleCat.{u + 1} Λ].obj ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F))),
      (pointSmallEtale x).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app i)).counit.app F) z = y := by
  obtain ⟨W, w, s, rfl⟩ := (pointSmallEtale x).toPresheafFiber_jointly_surjective y
  obtain ⟨i, V, b, hb, v, hv, φ, hφa, hφw⟩ :=
    exists_etale_descent_of_isLimit hc x W.hom w.left (CategoryTheory.Over.w w)
  let Vε : (D.obj i).Etale := MorphismProperty.Over.mk ⊤ b hb
  let vε : (pointSmallEtale (x ≫ c.π.app i)).fiber.obj Vε := CategoryTheory.Over.homMk v hv
  let φε : (c.π.app i).Etale.obj Vε ⟶ W := MorphismProperty.Over.homMk φ hφa
  have hpt : (pointSmallEtale x).fiber.map φε
      ((pointSmallEtaleFiberEtaleIso (c.π.app i) x).inv.app Vε vε) = w := by
    apply CategoryTheory.Over.OverMorphism.ext
    erw [pointSmallEtale_fiber_map_left]
    rw [pointSmallEtaleFiberEtaleIso_inv_app_left]
    exact hφw
  refine ⟨i, ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (c.π.app i) x).app
    ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F)).inv
    ((pointSmallEtale (x ≫ c.π.app i)).toPresheafFiber Vε vε
      ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F).obj (F.obj.map φε.op s)), ?_⟩
  have h := ConcreteCategory.congr_hom (toPresheafFiber_comp_sheafFiber_map_counit
    (ModuleCat.{u + 1} Λ) (c.π.app i) x F Vε vε) (F.obj.map φε.op s)
  simp only [ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  rw [← hpt]
  exact GrothendieckTopology.Point.toPresheafFiber_w_apply _ _ _ _ _

include hc in
/-- An element of the stalk of `pᵢ^* pᵢ_* F` which vanishes in `F_x̄` already vanishes in the
stalk of some `pₖ^* pₖ_* F`, `k ⟶ i`. -/
lemma exists_sheafFiber_map_descentTransition_eq_zero (i : I)
    (y : (pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((c.π.app i)^*[ModuleCat.{u + 1} Λ].obj ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F)))
    (hy : (pointSmallEtale x).sheafFiber.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app i)).counit.app F) y = 0) :
    ∃ (k : I) (g : k ⟶ i), (pointSmallEtale x).sheafFiber.map
      (descentTransition (ModuleCat.{u + 1} Λ) (c.π.app k) (D.map g) (c.π.app i)
        (c.w g).symm F) y = 0 := by
  set e := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (c.π.app i) x).app
    ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F)
  obtain ⟨Vε, vε, t, ht⟩ := (pointSmallEtale (x ≫ c.π.app i)).toPresheafFiber_jointly_surjective
    (e.hom y)
  obtain rfl : y = e.inv ((pointSmallEtale (x ≫ c.π.app i)).toPresheafFiber Vε vε
      ((c.π.app i)_*[ModuleCat.{u + 1} Λ].obj F).obj t) := by
    erw [ht]
    exact (e.hom_inv_id_apply y).symm
  have h1 := ConcreteCategory.congr_hom (toPresheafFiber_comp_sheafFiber_map_counit
    (ModuleCat.{u + 1} Λ) (c.π.app i) x F Vε vε) t
  simp only [ConcreteCategory.comp_apply] at h1
  have hy' : (pointSmallEtale x).toPresheafFiber _
      ((pointSmallEtaleFiberEtaleIso (c.π.app i) x).inv.app Vε vε) F.obj t =
      (pointSmallEtale x).toPresheafFiber _
        ((pointSmallEtaleFiberEtaleIso (c.π.app i) x).inv.app Vε vε) F.obj 0 := by
    rw [map_zero]
    exact h1.symm.trans hy
  obtain ⟨W, f, w, hfw, hft⟩ :=
    ((pointSmallEtale x).toPresheafFiber_eq_iff' _ _ _ _).1 hy'
  rw [map_zero] at hft
  have : Etale Vε.hom := Vε.prop
  obtain ⟨k, g, V', b', hb', v', hv', ψ, χ, hψ, hv'ψ, hχa, hχw, hχψ⟩ :=
    exists_etale_hom_descent_of_isLimit hc x Vε.hom W.hom f.left (MorphismProperty.Over.w f)
      w.left (CategoryTheory.Over.w w)
  refine ⟨k, g, ?_⟩
  have : Etale b' := hb'
  let V'ε : (D.obj k).Etale := MorphismProperty.Over.mk ⊤ b' hb'
  let v'ε : (pointSmallEtale (x ≫ c.π.app k)).fiber.obj V'ε := CategoryTheory.Over.homMk v' hv'
  let ψε : V'ε ⟶ (D.map g).Etale.obj Vε := MorphismProperty.Over.homMk ψ hψ
  let χε : (c.π.app k).Etale.obj V'ε ⟶ W := MorphismProperty.Over.homMk χ hχa
  have hfw' : w.left ≫ f.left =
      ((pointSmallEtaleFiberEtaleIso (c.π.app i) x).inv.app Vε vε).left :=
    congrArg CommaMorphism.left hfw
  have hv'' : ((pointSmallEtale (x ≫ c.π.app k)).fiber.map ψε v'ε).left ≫
      pullback.fst Vε.hom (D.map g) = vε.left := by
    calc _ = v' ≫ ψ ≫ pullback.fst Vε.hom (D.map g) := Category.assoc _ _ _
      _ = w.left ≫ f.left ≫ pullback.fst Vε.hom (c.π.app i) := hv'ψ
      _ = vε.left := by
        rw [← Category.assoc, hfw']
        exact pointSmallEtaleFiberEtaleIso_inv_app_left_fst _ _ _ _
  have h2 := ConcreteCategory.congr_hom
    (toPresheafFiber_comp_sheafFiber_map_descentTransition (ModuleCat.{u + 1} Λ) (c.π.app k) x
      (D.map g) (c.π.app i) (c.w g).symm F Vε vε _ hv'') t
  simp only [ConcreteCategory.comp_apply] at h2
  refine h2.trans ?_
  have hθ : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map ψε ≫
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (c.π.app k) (D.map g)
        (c.π.app i) (c.w g).symm).inv.app Vε = χε ≫ f := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · have ha : ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map ψε).left ≫
          pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).obj Vε).hom
            (c.π.app k) = pullback.fst b' (c.π.app k) ≫ ψ := by
        rw [MorphismProperty.Over.pullback_map_left]
        exact pullback.lift_fst _ _ _
      calc _ = ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map ψε).left ≫
            ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (c.π.app k) (D.map g)
              (c.π.app i) (c.w g).symm).inv.app Vε).left ≫
              pullback.fst Vε.hom (c.π.app i) := Category.assoc _ _ _
        _ = pullback.fst b' (c.π.app k) ≫ ψ ≫ pullback.fst Vε.hom (D.map g) := by
          rw [pullbackComp_inv_app_left_fst, reassoc_of% ha]
        _ = χ ≫ f.left ≫ pullback.fst Vε.hom (c.π.app i) := hχψ.symm
        _ = _ := (Category.assoc _ _ _).symm
    · have h₁ := MorphismProperty.Over.w
        ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map ψε ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) (c.π.app k) (D.map g)
            (c.π.app i) (c.w g).symm).inv.app Vε)
      have h₂ := MorphismProperty.Over.w (χε ≫ f)
      exact h₁.trans h₂.symm
  have hz : ((c.π.app k)_*[ModuleCat.{u + 1} Λ].obj F).obj.map ψε.op
      (((lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app k) (D.map g) (c.π.app i)
        (c.w g).symm).inv.app F).hom.app (op Vε) t) = 0 := by
    rw [lowerStarComp_inv_app_hom_app_of_eq, lowerStar_obj_val_map]
    erw [← ConcreteCategory.comp_apply]
    rw [← Functor.map_comp, ← op_comp, hθ, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [hft]
    rw [map_zero]
  have hg : (pointSmallEtale (x ≫ c.π.app k)).toPresheafFiber ((D.map g).Etale.obj Vε)
      ((pointSmallEtale (x ≫ c.π.app k)).fiber.map ψε v'ε)
      ((c.π.app k)_*[ModuleCat.{u + 1} Λ].obj F).obj
      (((lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app k) (D.map g) (c.π.app i)
        (c.w g).symm).inv.app F).hom.app (op Vε) t) = 0 := by
    rw [← GrothendieckTopology.Point.toPresheafFiber_w_apply, hz, map_zero]
  erw [hg]
  exact map_zero _

include hc in
/-- At a geometric point `x̄` of `X = lim Xᵢ`, the stalks of the counits `pᵢ^* pᵢ_* F ⟶ F`
exhibit the stalk `F_x̄` as the colimit of the stalks `(pᵢ^* pᵢ_* F)_x̄`. -/
noncomputable def isColimitSheafFiberMapCoconeDescentCocone :
    IsColimit ((pointSmallEtale x).sheafFiber.mapCocone
      (descentCocone (ModuleCat.{u + 1} Λ) c F)) :=
  ModuleCat.isColimitOfFiltered _
    (fun y ↦ by
      obtain ⟨i, z, hz⟩ := exists_sheafFiber_map_counit_eq hc F x y
      exact ⟨op i, z, hz⟩)
    (fun j y hy ↦ by
      obtain ⟨k, g, hg⟩ := exists_sheafFiber_map_descentTransition_eq_zero hc F x j.unop y hy
      exact ⟨op k, g.op, hg⟩)

end AlgebraicGeometry.Etale
