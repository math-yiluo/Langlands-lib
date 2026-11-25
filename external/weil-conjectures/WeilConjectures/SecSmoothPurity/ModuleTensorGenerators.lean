/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrows
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrows

/-! # Generalized generators of the ordinary module comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] Adjunction.rightAdjointLaxMonoidal
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

open SheafOfModules
attribute [local instance] monoidalCategory symmetricCategory
open scoped ChangeOfRings

private theorem tensor_iso_inv (M N : Modules R) :
    (tensorObjIsoSheafification M N).inv =
      (Functor.Monoidal.μIso (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj))
          M.val N.val).inv ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit.app M ⊗ₘ
          (PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit.app N) := by
  rfl

attribute [local irreducible] tensorObjIsoSheafification

private theorem tensor_braiding_iso (M N : Modules R) :
    (tensorObjIsoSheafification M N).inv ≫ (β_ M N).hom =
      (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (β_ M.val N.val).hom ≫ (tensorObjIsoSheafification N M).inv := by
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eM : F.obj M.val ⟶ M :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit.app M
  let eN : F.obj N.val ⟶ N :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit.app N
  rw [tensor_iso_inv, tensor_iso_inv]
  change (Functor.Monoidal.μIso F M.val N.val).inv ≫
      (eM ⊗ₘ eN) ≫ (β_ M N).hom =
    F.map (β_ M.val N.val).hom ≫ (Functor.Monoidal.μIso F N.val M.val).inv ≫
      (eN ⊗ₘ eM)
  rw [BraidedCategory.braiding_naturality]
  have hb : Functor.OplaxMonoidal.δ F M.val N.val ≫
      (β_ (F.obj M.val) (F.obj N.val)).hom =
      F.map (β_ M.val N.val).hom ≫ Functor.OplaxMonoidal.δ F N.val M.val := by
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  simpa only [Functor.Monoidal.μIso_inv, Category.assoc] using
    congrArg (fun z ↦ z ≫ (eN ⊗ₘ eM)) hb

/-- The canonical pure tensor in the sheafified module tensor product.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def moduleTmul (M N : Modules R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- The sheaf tensor braiding exchanges pure tensor factors.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem moduleTmul_braiding (M N : Modules R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (β_ M N).hom.val.app U (moduleTmul M N U x y) = moduleTmul N M U y x := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have h := congrArg
    (fun z ↦ z.val.app U ((adj.unit.app (M.val ⊗ N.val)).app U
      (x ⊗ₜ[R.obj.obj U] y))) (tensor_braiding_iso M N)
  change _ = (tensorObjIsoSheafification N M).inv.val.app U
    (((PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
        (β_ M.val N.val).hom).val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))) at h
  have hn := congrArg (fun z ↦ z.app U (x ⊗ₜ[R.obj.obj U] y))
    (adj.unit.naturality (β_ M.val N.val).hom)
  change (adj.unit.app (N.val ⊗ M.val)).app U
      ((β_ M.val N.val).hom.app U (x ⊗ₜ[R.obj.obj U] y)) =
    ((PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
        (β_ M.val N.val).hom).val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y)) at hn
  rw [← hn] at h
  exact h

/-- The sheaf tensor associator acts on pure triples by reassociation.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem moduleTmul_associator (M N H : Modules R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) :
    (α_ M N H).hom.val.app U
      (moduleTmul (M ⊗ N) H U (moduleTmul M N U x y) z) =
        moduleTmul M (N ⊗ H) U x (moduleTmul N H U y z) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let V := SheafOfModules.forget
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let : V.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have hm (A B : Modules R) (a : A.val.obj U) (b : B.val.obj U) :
      (Functor.LaxMonoidal.μ V A B).app U (a ⊗ₜ[R.obj.obj U] b) =
        moduleTmul A B U a b := by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ,
      Adjunction.homEquiv_unit]
    simp only [moduleTmul, tensor_iso_inv, Functor.Monoidal.μIso_inv]
    rfl
  have ha := congrArg (fun q ↦ q.app U
    ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z))
      (Functor.LaxMonoidal.associativity V M N H)
  change (α_ M N H).hom.val.app U
      ((Functor.LaxMonoidal.μ V (M ⊗ N) H).app U
        ((Functor.LaxMonoidal.μ V M N).app U
          (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) =
    (Functor.LaxMonoidal.μ V M (N ⊗ H)).app U
      (x ⊗ₜ[R.obj.obj U]
        (Functor.LaxMonoidal.μ V N H).app U (y ⊗ₜ[R.obj.obj U] z)) at ha
  simpa only [hm] using ha

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Unit insertion is natural for the actual module pullback.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
theorem comparison_q_naturality (f : RingedPullback R S) (k : Comparison f)
    {M N : Modules R} (b : M ⟶ N) :
    (underlying f.RI).map (f.I.modules.map b) ≫ k.q N =
      k.q M ≫ (underlying S).map (f.L.map b) := by
  exact q_naturality f k b

/-- Tensor maps act componentwise on the ordinary sheaf pure tensors.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem moduleTmul_map {M M' N N' : Modules R} (a : M ⟶ M') (b : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (a ⊗ₘ b).val.app U (moduleTmul M N U x y) =
      moduleTmul M' N' U (a.val.app U x) (b.val.app U y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let V := SheafOfModules.forget
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      PresheafOfModules.restrictScalars
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let : V.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have hm (A B : Modules R) (a : A.val.obj U) (b : B.val.obj U) :
      (Functor.LaxMonoidal.μ V A B).app U (a ⊗ₜ[R.obj.obj U] b) =
        moduleTmul A B U a b := by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit,
      moduleTmul, tensor_iso_inv, Functor.Monoidal.μIso_inv]
    rfl
  have hn := congrArg (fun v ↦ v.app U (x ⊗ₜ[R.obj.obj U] y))
    (Functor.LaxMonoidal.μ_natural V a b)
  change (Functor.LaxMonoidal.μ V M' N').app U
      (a.val.app U x ⊗ₜ[R.obj.obj U] b.val.app U y) =
    (a ⊗ₘ b).val.app U ((Functor.LaxMonoidal.μ V M N).app U
      (x ⊗ₜ[R.obj.obj U] y)) at hn
  simpa only [hm] using hn.symm

/-- Naturality of the normalized generalized inverse-image insertion.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
@[reassoc]
theorem generator_naturality (f : RingedPullback R S) (k : Comparison f)
    {M N : Modules R} (b : M ⟶ N) {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying R).obj M) :
    generator f k (x ≫ (underlying R).map b) =
      generator f k x ≫ (underlying S).map (f.L.map b) := by
  dsimp only [generator]
  rw [Functor.map_comp]
  have hi := f.I.moduleUnderlying.inv.naturality b
  change f.uInv.map ((underlying R).map b) ≫ f.I.moduleUnderlying.inv.app N =
    f.I.moduleUnderlying.inv.app M ≫ (underlying f.RI).map (f.I.modules.map b) at hi
  simp only [Category.assoc]
  rw [← Category.assoc (f.uInv.map ((underlying R).map b))
    (f.I.moduleUnderlying.inv.app N), hi]
  simp only [Category.assoc]
  rw [comparison_q_naturality]

private theorem moduleTmul_restrict (M N : Modules R)
    {W V : Cᵒᵖ} (i : W ⟶ V) (x : M.val.obj W) (y : N.val.obj W) :
    (M ⊗ N).val.map i (moduleTmul M N W x y) =
      moduleTmul M N V (M.val.map i x) (N.val.map i y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let v := x ⊗ₜ[R.obj.obj W] y
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

/-- The pure pairing on any two generalized module sections.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def moduleTensorPair {M N : Modules R} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N) :
    Z ⟶ (underlying R).obj (M ⊗ N) :=
  ⟨{ app := fun W ↦ ↾fun t ↦ moduleTmul M N W (x.hom.app W t) (y.hom.app W t)
     naturality := by
       intro W V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change moduleTmul M N V (x.hom.app V (Z.obj.map i t))
           (y.hom.app V (Z.obj.map i t)) =
         (M ⊗ N).val.map i (moduleTmul M N W (x.hom.app W t) (y.hom.app W t))
       rw [hx, hy]
       exact (moduleTmul_restrict M N i _ _).symm }⟩

/-- The generalized pure formula as an equality of sheaf morphisms.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
theorem generator_tensorPair (f : RingedPullback R S) (k : Comparison f)
    {M N : Modules R} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N) :
    generator f k (moduleTensorPair x y) ≫ (underlying S).map (k.mu M N).hom =
      moduleTensorPair (generator f k x) (generator f k y) := by
  apply Sheaf.hom_ext
  ext W t
  exact k.pure M N Z x y (moduleTensorPair x y) (fun _ _ ↦ rfl) W t

open scoped TensorProduct

-- Repeated sheafification and scalar-extension identifications require extra elaboration.
/-- Three scalar-extension unit insertions generate the triple sheaf tensor.
Source: Stacks 03EK and 03EL (auxiliary; not a blueprint node).
Proof: cancel the sheafified tensor of the three sheafification units, which is an
isomorphism by compatibility of tensor with local equivalences. Apply the
sheafification adjunction and curry the sectionwise linear maps three times.
Scalar-extension hom extensionality in each argument reduces to unit insertions. -/
theorem scalarTensor_hom_ext₃
    {A B : Sheaf J CommRingCat.{w}} (c : A ⟶ B)
    (M N P : Modules A) (H : Modules B)
    {f g : ((monoidalCategory B).tensorObj (changeOfRings c M)
      (changeOfRings c N)) ⊗ (changeOfRings c P) ⟶ H}
    (h : ∀ W m n p, f.val.app W (moduleTmul _ _ W
        (moduleTmul _ _ W (extensionTmul c M W 1 m) (extensionTmul c N W 1 n))
          (extensionTmul c P W 1 p)) =
      g.val.app W (moduleTmul _ _ W
        (moduleTmul _ _ W (extensionTmul c M W 1 m) (extensionTmul c N W 1 n))
          (extensionTmul c P W 1 p))) : f = g := by
  let RB := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 RB.obj)
  let S := PresheafOfModules.sheafification (𝟙 RB.obj)
  let E := changeOfRingsPresheaf c M
  let F := changeOfRingsPresheaf c N
  let G := changeOfRingsPresheaf c P
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  let ηG := adj.unit.app G
  let E2 := (S.obj E).val ⊗ (S.obj F).val
  have hη (V : PresheafOfModules.{w} RB.obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)) (adj.unit.app V) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 RB.obj)]
    change IsIso (S.map (adj.unit.app V))
    dsimp only [S, adj]
    infer_instance
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).tensorHom_mem
    ((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ηG
    ((J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).comp_mem _ _
      ((J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).tensorHom_mem
        ηE ηF (hη E) (hη F)) (hη E2)) (hη G)
  have hi : IsIso (S.map (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)] at hηη
    exact hηη
  let q := S.map (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG) ≫
    (tensorObjIsoSheafification (S.obj E2) (S.obj G)).inv ≫
      ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv ⊗ₘ 𝟙 (S.obj G))
  have : IsIso q := by
    dsimp only [q]
    infer_instance
  apply ((asIso q).symm.homFromEquiv).injective
  apply (adj.homEquiv ((E ⊗ F) ⊗ G) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing (RB.obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : ((E.obj W) ⊗[RB.obj.obj W] (F.obj W)) ⊗[RB.obj.obj W]
      (G.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app ((E ⊗ F) ⊗ G) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ f)).app W).hom
  let b : ((E.obj W) ⊗[RB.obj.obj W] (F.obj W)) ⊗[RB.obj.obj W]
      (G.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app ((E ⊗ F) ⊗ G) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ g)).app W).hom
  apply ModuleCat.hom_ext
  change a = b
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of (RB.obj.obj W)
        ((F.obj W) →ₗ[RB.obj.obj W] (G.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
        (TensorProduct.curry (TensorProduct.curry a)) =
      ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of (RB.obj.obj W)
          ((F.obj W) →ₗ[RB.obj.obj W] (G.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
          (TensorProduct.curry (TensorProduct.curry b)) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry (TensorProduct.curry a) _ =
      TensorProduct.curry (TensorProduct.curry b) _
    have hm : ModuleCat.ofHom (X := F.obj W)
        (Y := ModuleCat.of (RB.obj.obj W) ((G.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
          (TensorProduct.curry (TensorProduct.curry a)
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W)
          (Y := ModuleCat.of (RB.obj.obj W) ((G.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
            (TensorProduct.curry (TensorProduct.curry b)
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      change TensorProduct.curry (TensorProduct.curry a) _ _ =
        TensorProduct.curry (TensorProduct.curry b) _ _
      have hn : ModuleCat.ofHom (X := G.obj W) (Y := H.val.obj W)
          (TensorProduct.curry (TensorProduct.curry a)
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) =
          ModuleCat.ofHom (X := G.obj W) (Y := H.val.obj W)
            (TensorProduct.curry (TensorProduct.curry b)
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)
              ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n)) := by
        apply ModuleCat.ExtendScalars.hom_ext
        intro p
        let m' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m
        let n' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n
        let p' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] p
        have he := congrArg (fun k ↦ k.app W ((m' ⊗ₜ[B.obj.obj W] n') ⊗ₜ[B.obj.obj W] p'))
          (adj.unit.naturality (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG))
        change (adj.unit.app ((S.obj E2).val ⊗ (S.obj G).val)).app W
            ((adj.unit.app E2).app W
              (ηE.app W m' ⊗ₜ[B.obj.obj W] ηF.app W n') ⊗ₜ[B.obj.obj W] ηG.app W p') =
          (S.map (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG)).val.app W
            ((adj.unit.app ((E ⊗ F) ⊗ G)).app W
              ((m' ⊗ₜ[B.obj.obj W] n') ⊗ₜ[B.obj.obj W] p')) at he
        change f.val.app W
            (((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv ⊗ₘ
              𝟙 (S.obj G)).val.app W
              ((tensorObjIsoSheafification (S.obj E2) (S.obj G)).inv.val.app W
                ((S.map (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG)).val.app W
                  ((adj.unit.app ((E ⊗ F) ⊗ G)).app W
                    ((m' ⊗ₜ[B.obj.obj W] n') ⊗ₜ[B.obj.obj W] p'))))) =
          g.val.app W
            (((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv ⊗ₘ
              𝟙 (S.obj G)).val.app W
              ((tensorObjIsoSheafification (S.obj E2) (S.obj G)).inv.val.app W
                ((S.map (((ηE ⊗ₘ ηF) ≫ adj.unit.app E2) ⊗ₘ ηG)).val.app W
                  ((adj.unit.app ((E ⊗ F) ⊗ G)).app W
                    ((m' ⊗ₜ[B.obj.obj W] n') ⊗ₜ[B.obj.obj W] p')))))
        rw [← he]
        change f.val.app W
            (((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv ⊗ₘ
              𝟙 (S.obj G)).val.app W
              (moduleTmul (S.obj E2) (S.obj G) W
                ((adj.unit.app E2).app W
                  (ηE.app W m' ⊗ₜ[B.obj.obj W] ηF.app W n')) (ηG.app W p'))) =
          g.val.app W
            (((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv ⊗ₘ
              𝟙 (S.obj G)).val.app W
              (moduleTmul (S.obj E2) (S.obj G) W
                ((adj.unit.app E2).app W
                  (ηE.app W m' ⊗ₜ[B.obj.obj W] ηF.app W n')) (ηG.app W p')))
        rw [moduleTmul_map]
        dsimp only [S, E, F, G, E2, ηE, ηF, ηG, adj, RB, m', n', p']
        simpa only [moduleTmul, extensionTmul, extensionFunctor, SheafOfModules.id_val,
          PresheafOfModules.id_app, ModuleCat.id_apply, changeOfRings] using h W m n p
      exact congrArg ModuleCat.Hom.hom hn
    exact congrArg ModuleCat.Hom.hom hm
  exact TensorProduct.curry_injective
    (TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh))

end CategoryTheory.CochainPullback
