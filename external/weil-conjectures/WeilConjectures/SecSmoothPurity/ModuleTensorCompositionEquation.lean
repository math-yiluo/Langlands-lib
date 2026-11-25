/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # The ordinary tensor square for composite pullback

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-composition-equation)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

variable {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
  {H : GrothendieckTopology E}
  [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {T : Sheaf H CommRingCat.{w}}

private noncomputable def compositeComparison
    (f : RingedPullback R S) (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h)
    (a : CompositePresentation f g h kf kg kh) : Comparison h where
  q := kh.q
  q_one := kh.q_one
  mu M N :=
    (compositionModule f g h a.rightModules).app (M ⊗ N) ≪≫
      g.L.mapIso (kf.mu M N) ≪≫ kg.mu (f.L.obj M) (f.L.obj N) ≪≫
        ((compositionModule f g h a.rightModules).app M ⊗ᵢ
          (compositionModule f g h a.rightModules).app N).symm
  naturality := by
    intro M M' N N' b c
    let e := compositionModule f g h a.rightModules
    change h.L.map (b ⊗ₘ c) ≫ e.hom.app (M' ⊗ N') ≫
        g.L.map (kf.mu M' N').hom ≫ (kg.mu (f.L.obj M') (f.L.obj N')).hom ≫
          (e.inv.app M' ⊗ₘ e.inv.app N') =
      e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
        (kg.mu (f.L.obj M) (f.L.obj N)).hom ≫
          (e.inv.app M ⊗ₘ e.inv.app N) ≫ (h.L.map b ⊗ₘ h.L.map c)
    rw [e.hom.naturality_assoc]
    change _ ≫ g.L.map (f.L.map (b ⊗ₘ c)) ≫ _ = _
    rw [← g.L.map_comp_assoc, kf.naturality, g.L.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (g.L.map (f.L.map b ⊗ₘ f.L.map c))
      (kg.mu (f.L.obj M') (f.L.obj N')).hom, kg.naturality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    rw [← e.inv.naturality b, ← e.inv.naturality c]
    rfl
  pure := by
    intro M N Z x y z hz W t
    let e := compositionModule f g h a.rightModules
    let v := ((conjugateIsoEquiv (f.adj.comp g.adj) h.adj).symm
      a.rightSets.symm).hom.app Z
    have hfp : generator f kf z ≫ (underlying S).map (kf.mu M N).hom =
        moduleTensorPair (generator f kf x) (generator f kf y) := by
      apply Sheaf.hom_ext
      ext U s
      exact kf.pure M N Z x y z hz U s
    have hgp := generator_tensorPair g kg (generator f kf x) (generator f kf y)
    have hs (A : Modules R) (z : Z ⟶ (underlying R).obj A) :
        generator h kh z ≫ (underlying T).map (e.hom.app A) =
          v ≫ generator g kg (generator f kf z) := a.scalarAssociation A Z z
    have he : generator h kh z ≫ (underlying T).map
        (e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
          (kg.mu (f.L.obj M) (f.L.obj N)).hom) =
        v ≫ moduleTensorPair (generator g kg (generator f kf x))
          (generator g kg (generator f kf y)) := by
      simp only [Functor.map_comp]
      rw [← Category.assoc (generator h kh z) ((underlying T).map (e.hom.app _)), hs]
      simp only [Category.assoc]
      have hn := generator_naturality g kg (kf.mu M N).hom (generator f kf z)
      have hn' := congrArg (fun s ↦ s ≫
        (underlying T).map (kg.mu (f.L.obj M) (f.L.obj N)).hom) hn.symm
      rw [hfp] at hn'
      exact congrArg (fun s ↦ v ≫ s) (hn'.trans hgp)
    have hh := congrArg (fun s ↦ s.hom.app W t) he
    have hx := congrArg (fun s ↦ s.hom.app W t) (hs M x)
    have hy := congrArg (fun s ↦ s.hom.app W t) (hs N y)
    change (e.hom.app M).val.app W ((generator h kh x).hom.app W t) =
      (generator g kg (generator f kf x)).hom.app W (v.hom.app W t) at hx
    change (e.hom.app N).val.app W ((generator h kh y).hom.app W t) =
      (generator g kg (generator f kf y)).hom.app W (v.hom.app W t) at hy
    change _ = moduleTmul (g.L.obj (f.L.obj M)) (g.L.obj (f.L.obj N)) W
      ((generator g kg (generator f kf x)).hom.app W (v.hom.app W t))
      ((generator g kg (generator f kf y)).hom.app W (v.hom.app W t)) at hh
    have hh' := congrArg (fun s ↦ (e.inv.app M ⊗ₘ e.inv.app N).val.app W s) hh
    have ht := moduleTmul_map (e.inv.app M) (e.inv.app N) W
      ((generator g kg (generator f kf x)).hom.app W (v.hom.app W t))
      ((generator g kg (generator f kf y)).hom.app W (v.hom.app W t))
    have hh'' := hh'.trans ht
    rw [← hx, ← hy] at hh''
    have hm (A : Modules R) (s : (h.L.obj A).val.obj W) :
        (e.inv.app A).val.app W ((e.hom.app A).val.app W s) = s :=
      congrArg (fun z ↦ z.val.app W s) (e.hom_inv_id_app A)
    rw [hm, hm] at hh''
    change ((generator h kh z ≫ (underlying T).map
      (e.hom.app (M ⊗ N) ≫ g.L.map (kf.mu M N).hom ≫
        (kg.mu (f.L.obj M) (f.L.obj N)).hom) ≫
      (underlying T).map (e.inv.app M ⊗ₘ e.inv.app N)).hom.app W) t =
      moduleTmul (h.L.obj M) (h.L.obj N) W
        ((generator h kh x).hom.app W t) ((generator h kh y).hom.app W t)
    exact hh''

end CategoryTheory.CochainPullback
