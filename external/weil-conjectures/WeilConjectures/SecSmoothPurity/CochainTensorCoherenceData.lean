/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainCompositeHom
import WeilConjectures.SecSmoothPurity.CochainModuleAdjunction

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (auxiliary; not a blueprint node).

The tensor, associator, Koszul symmetry and action unitors below are the existing
homological-complex constructions. Coefficient arrows are characterized on
scalar-extension generators, and composition uses the adjunction conjugate.

The landed side comparison has shared source/target site sizes. The fresh
`SheafOfModules.CochainTensorComparison` namespace generalizes its identical
normalizations to independent site sizes. `ofLanded` retains each of its fields
on the existing range. The published generic signed total maps are reused.
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false

-- Keep the localized monoidal structure behind its explicit tensor/unitor API.
attribute [local irreducible] SheafOfModules.monoidalCategory

namespace SheafOfModules.CochainTensorComparison

set_option backward.isDefEq.respectTransparency false

universe u

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

/-- Bilinearity of the existing sheaf tensor, assembled from its additive tensor functors.
Source: Stacks 03EK (auxiliary; not a blueprint node).
Proof: the additive tensorLeft and tensorRight functors of MonoidalFree give the
four zero and addition laws of MonoidalPreadditive. Assemble those four laws. -/
noncomputable abbrev ringedTensorPreadditive :
    @MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ _ (monoidalCategory R) :=
  cochainModulesPreadditive R

/-- The ordinary tensor comparison with its pure-tensor characterization.
The maps q insert 1 in scalar extension; the generalized-element equation fixes
mu on the inverse images of all pure tensors, hence on their sheafification.
Source: Stacks, Modules on Sites, 03EL
(auxiliary; not a blueprint node). -/
structure CanonicalRingedTensorComparison where
  /-- Scalar-extension insertion, as a map of underlying sheaves of sets. -/
  q : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI) ⋙ sheafCompose JD
    (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.modules.obj M)) ⟶
      ((toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (L.obj M))
  /-- Insertion is specifically m mapped to 1 tensor m. -/
  q_one : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W),
    (q M).hom.app W m = (eqToHom (hobj M).symm).val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
        (changeOfRingsPresheaf c (I.modules.obj M))).app W
          ((1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] m))
  /-- Tensor preservation with the orientation of 07A4. -/
  mu : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
    L.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (L.obj M) (L.obj N)
  /-- Naturality in both variables. -/
  naturality : ∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
    L.map ((monoidalCategory R).tensorHom f g) ≫ (mu M' N').hom =
      (mu M N).hom ≫ (monoidalCategory S).tensorHom (L.map f) (L.map g)
  /-- Canonical generalized pure-tensor formula, rather than an arbitrary tensor iso. -/
  pure : ∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
    (x : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N))
    (z : Z ⟶ ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((monoidalCategory R).tensorObj M N))),
    (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
      (tensorObjIsoSheafification M N).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app W (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
    ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
      (uInv.map z ≫ I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
        q ((monoidalCategory R).tensorObj M N) ≫
          (toSheaf ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose JD
            (CategoryTheory.forget AddCommGrpCat.{u})).map (mu M N).hom).hom.app W t =
      (tensorObjIsoSheafification (L.obj M) (L.obj N)).inv.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S).obj)).unit.app
          ((L.obj M).val ⊗ (L.obj N).val)).app W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M ≫ q M).hom.app W t
              ⊗ₜ[S.obj.obj W]
              (uInv.map y ≫ I.moduleUnderlying.inv.app N ≫ q N).hom.app W t))

section TensorSections

attribute [local irreducible] scalarInsertion

open scoped ChangeOfRings TensorProduct
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

@[no_expose] private noncomputable def ts (M N : SheafOfModules.{u} (𝓡 B))
    (W : Dᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.obj W :=
  CochainScalarConstruction.pure B M N W m n
private theorem ts_naturality (M N : SheafOfModules.{u} (𝓡 B))
    {W V : Dᵒᵖ} (i : W ⟶ V) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.map i (ts B M N W m n) =
      ts B M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)
  let v := m ⊗ₜ[B.obj.obj W] n
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val i ((adj.unit.app (M.val ⊗ N.val)).app W v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)
@[no_expose] private noncomputable def tensorPair (M N : SheafOfModules.{u} (𝓡 B))
    (Z : Sheaf J (Type u))
    (x : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj N)) :
    Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((monoidalCategory B).tensorObj M N)) :=
  ⟨{ app := fun W ↦ ↾fun t ↦ ts B M N W (x.hom.app W t) (y.hom.app W t)
     naturality := by
       intro W V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change ts B M N V (x.hom.app V (Z.obj.map i t))
           (y.hom.app V (Z.obj.map i t)) =
         ((monoidalCategory B).tensorObj M N).val.map i
           (ts B M N W (x.hom.app W t) (y.hom.app W t))
       rw [hx, hy]
       exact (ts_naturality B M N i _ _).symm }⟩

private theorem productElements {E : Type*} [Category* E] [HasBinaryProducts E]
    (F : E ⥤ Type u) (X Y : E) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

variable (c : A ⟶ B)

@[no_expose] private noncomputable def ins (M : SheafOfModules.{u} (𝓡 A))
    (W : Dᵒᵖ) (m : M.val.obj W) : (changeOfRings.{vD, uD, u} c M).val.obj W :=
  CochainScalarConstruction.ins c M W m
-- Expand the two scalar extensions through the sheafification adjunction.
private theorem scalar_tensor_ext
    (M N : SheafOfModules.{u} (𝓡 A)) (H : SheafOfModules.{u} (𝓡 B))
    {f g : (monoidalCategory B).tensorObj (changeOfRings.{vD, uD, u} c M)
      (changeOfRings.{vD, uD, u} c N) ⟶ H}
    (h : ∀ W m n, f.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n)) =
      g.val.app W (ts B _ _ W (ins A B c M W m) (ins A B c N W n))) : f = g := by
  apply CochainScalarConstruction.scalar_tensor_ext c M N H
  intro W m n
  exact h W m n

private theorem ts_cast
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{vD, uD, u} c M)
    (hy : Y = changeOfRings.{vD, uD, u} c N)
    (W : Dᵒᵖ) (m : (changeOfRings.{vD, uD, u} c M).val.obj W)
    (n : (changeOfRings.{vD, uD, u} c N).val.obj W) :
    (eqToHom (congrArg₂ (monoidalCategory B).tensorObj hx.symm hy.symm)).val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W m n) =
    ts B X Y W ((eqToHom hx.symm).val.app W m)
      ((eqToHom hy.symm).val.app W n) := by
  subst X
  subst Y
  rfl

private theorem scalarTensorSections_hom_ext
    (M N : SheafOfModules.{u} (𝓡 A))
    (X Y H : SheafOfModules.{u} (𝓡 B))
    (hx : X = changeOfRings.{vD, uD, u} c M)
    (hy : Y = changeOfRings.{vD, uD, u} c N)
    {f g : (monoidalCategory B).tensorObj X Y ⟶ H}
    (h : ∀ W m n, f.val.app W (ts B X Y W
      ((eqToHom hx.symm).val.app W (ins A B c M W m))
      ((eqToHom hy.symm).val.app W (ins A B c N W n))) =
      g.val.app W (ts B X Y W
        ((eqToHom hx.symm).val.app W (ins A B c M W m))
        ((eqToHom hy.symm).val.app W (ins A B c N W n)))) : f = g := by
  let e := eqToHom (congrArg₂ (monoidalCategory B).tensorObj hx.symm hy.symm)
  apply (cancel_epi e).mp
  apply scalar_tensor_ext A B c M N H
  intro W m n
  change f.val.app W (e.val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W
        (ins A B c M W m) (ins A B c N W n))) =
    g.val.app W (e.val.app W
      (ts B (changeOfRings.{vD, uD, u} c M) (changeOfRings.{vD, uD, u} c N) W
        (ins A B c M W m) (ins A B c N W n)))
  dsimp only [e]
  rw [ts_cast A B c M N X Y hx hy]
  exact h W m n

end TensorSections

section TensorUniqueness

set_option backward.isDefEq.respectTransparency.types false

-- Detect inverse tensorators on scalar-extension generators and universal products.
private theorem comparison_subsingleton [PreservesFiniteLimits uInv] :
    Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by
  refine ⟨fun a b ↦ ?_⟩
  rcases a with ⟨qa, hqa, ma, hna, hpa⟩
  rcases b with ⟨qb, hqb, mb, hnb, hpb⟩
  have hqq : qa = qb := by
    funext M
    ext W m
    exact (hqa M W m).trans (hqb M W m).symm
  subst qb
  have hmm : ma = mb := by
    funext M N
    apply Iso.ext_inv
    apply scalarTensorSections_hom_ext RI S c (I.modules.obj M) (I.modules.obj N)
      (L.obj M) (L.obj N) _ (hobj M) (hobj N)
    intro W m n
    let UR := toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})
    let Z := UR.obj M ⨯ UR.obj N
    let x : Z ⟶ UR.obj M := prod.fst
    let y : Z ⟶ UR.obj N := prod.snd
    let z := tensorPair R M N Z x y
    let ev := sheafToPresheaf JD (Type u) ⋙ (CategoryTheory.evaluation Dᵒᵖ (Type u)).obj W
    obtain ⟨t, htx, hty⟩ := productElements (uInv ⋙ ev) (UR.obj M) (UR.obj N)
      ((I.moduleUnderlying.hom.app M).hom.app W m)
      ((I.moduleUnderlying.hom.app N).hom.app W n)
    have hm : (uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t = m := by
      change (I.moduleUnderlying.inv.app M).hom.app W ((uInv.map x).hom.app W t) = m
      change (uInv.map x).hom.app W t = _ at htx
      rw [htx]
      exact congrArg (fun f ↦ f.hom.app W m) (I.moduleUnderlying.app M).hom_inv_id
    have hn : (uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t = n := by
      change (I.moduleUnderlying.inv.app N).hom.app W ((uInv.map y).hom.app W t) = n
      change (uInv.map y).hom.app W t = _ at hty
      rw [hty]
      exact congrArg (fun f ↦ f.hom.app W n) (I.moduleUnderlying.app N).hom_inv_id
    have hz : ∀ V s, z.hom.app V s = ts R M N V (x.hom.app V s) (y.hom.app V s) := by
      intros
      rfl
    have ha := hpa M N Z x y z hz W t
    have hb := hpb M N Z x y z hz W t
    let v := (uInv.map z ≫ I.moduleUnderlying.inv.app
      ((monoidalCategory R).tensorObj M N) ≫ qa
        ((monoidalCategory R).tensorObj M N)).hom.app W t
    change (ma M N).hom.val.app W v = ts S (L.obj M) (L.obj N) W
      ((qa M).hom.app W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t))
      ((qa N).hom.app W ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) at ha
    rw [hm, hn] at ha
    change (mb M N).hom.val.app W v = ts S (L.obj M) (L.obj N) W
      ((qa M).hom.app W ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t))
      ((qa N).hom.app W ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) at hb
    rw [hm, hn] at hb
    have hai := congrArg (fun w ↦ (ma M N).inv.val.app W w) ha
    have hbi := congrArg (fun w ↦ (mb M N).inv.val.app W w) hb
    have hai' : (ma M N).inv.val.app W ((ma M N).hom.val.app W v) = v :=
      congrArg (fun f ↦ f.val.app W v) (ma M N).hom_inv_id
    have hbi' : (mb M N).inv.val.app W ((mb M N).hom.val.app W v) = v :=
      congrArg (fun f ↦ f.val.app W v) (mb M N).hom_inv_id
    rw [hai'] at hai
    rw [hbi'] at hbi
    have hi := hai.symm.trans hbi
    rw [hqa M W m, hqa N W n] at hi
    exact hi
  cases hmm
  rfl

/-- The pure-tensor conditions determine the ordinary comparison uniquely and are attainable.
Source: Stacks 03EL (auxiliary; not a blueprint node).
Proof: apply the ordinary comparison theorem to the given inverse-image lift.
Its generalized-element normalization gives q and mu. Scalar-extension pure tensors
generate after sheafification, giving uniqueness of q. Bilinear generalized pure tensors
generate the sheaf tensor, giving uniqueness of mu; proof irrelevance handles the laws.
Unlike SheafOfModules.canonicalRingedTensorComparison_existsUnique, the explicit
binders below allow five independent universes uC, vC, uD, vD and u. The published
statement requires C,D : Type u with Category.{u} on both sites. -/
theorem canonicalRingedTensorComparison_existsUnique
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm) :
    Nonempty (CanonicalRingedTensorComparison R S RI uInv I c L hobj) ∧
      Subsingleton (CanonicalRingedTensorComparison R S RI uInv I c L hobj) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨mu, hn, hp⟩ := normalizedTensorator_exists R S RI uInv I c L hobj
      uPush adj hmap
    exact ⟨{ q := scalarInsertion R S RI uInv I c L hobj
             q_one := by intros; rfl
             mu := mu
             naturality := hn
             pure := hp }⟩
  · exact comparison_subsingleton R S RI uInv I c L hobj

end TensorUniqueness

namespace UnitConstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (I : AlgebraicInverseImage F R A)
@[no_expose]
private noncomputable abbrev base (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
@[no_expose]
private noncomputable abbrev rset (R : Sheaf J CommRingCat.{u}) : Sheaf J (Type u) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R
@[no_expose]
private noncomputable abbrev mset (R : Sheaf J CommRingCat.{u}) :
    SheafOfModules.{u} (base R) ⥤ Sheaf J (Type u) :=
  toSheaf (base R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
@[no_expose]
private noncomputable def oneMap : rset R ⟶ rset R :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
     naturality := by intro X Y f; ext; exact (map_one (R.obj.map f).hom).symm }⟩
@[no_expose]
private noncomputable def unitSetIso :
    (mset A).obj (I.modules.obj (unit (base R))) ≅ rset A :=
  I.moduleUnderlying.app (unit (base R)) ≪≫ I.ringUnderlying
private theorem basis (W : Dᵒᵖ) (a : A.obj.obj W) :
    (show (I.modules.obj (unit (base R))).val.obj W from
      (unitSetIso R A F I).inv.hom.app W a) = a •
        (show (I.modules.obj (unit (base R))).val.obj W from
          (unitSetIso R A F I).inv.hom.app W (1 : A.obj.obj W)) := by
  change (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W a)) = a •
    (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W)))
  let T := rset R
  let t := I.ringUnderlying.inv.hom.app W a
  have ho := I.ringOne T (oneMap R) (fun _ _ ↦ rfl) W t
  have he : (F.map (oneMap R)).hom.app W t =
      I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W) := by
    have hh := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc := congrArg (fun k ↦ k.hom.app W ((F.map (oneMap R)).hom.app W t))
      I.ringUnderlying.hom_inv_id
    exact hc.symm.trans hh
  have hs := I.moduleSMul (unit (base R)) T (𝟙 T) (oneMap R) (𝟙 T)
    (fun U x ↦ (mul_one (show R.obj.obj U from x)).symm) W t
  have hid : (F.map (𝟙 T)).hom.app W t = t :=
    congrArg (fun f ↦ f.hom.app W t) (F.map_id T)
  have ht := congrArg ((I.moduleUnderlying.inv.app (unit (base R))).hom.app W) hid
  have hr := congrArg (fun v : (F.obj T).obj.obj W ↦
    (show A.obj.obj W from I.ringUnderlying.hom.hom.app W v) •
      (show (I.modules.obj (unit (base R))).val.obj W from
        (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
          ((F.map (oneMap R)).hom.app W t))) hid
  have hs' := ht.symm.trans (hs.trans hr)
  have he' := congrArg ((I.moduleUnderlying.inv.app (unit (base R))).hom.app W) he
  have hs'' := hs'.trans (congrArg (fun v : (I.modules.obj (unit (base R))).val.obj W ↦
    (show A.obj.obj W from I.ringUnderlying.hom.hom.app W t) • v) he')
  have hc := congrArg (fun k ↦ k.hom.app W a) I.ringUnderlying.inv_hom_id
  change I.ringUnderlying.hom.hom.app W t = a at hc
  exact hs''.trans (congrArg (fun r : A.obj.obj W ↦
    r • (show (I.modules.obj (unit (base R))).val.obj W from
      (I.moduleUnderlying.inv.app (unit (base R))).hom.app W
        (I.ringUnderlying.inv.hom.app W (1 : A.obj.obj W)))) hc)
@[no_expose]
private noncomputable def unitIso : I.modules.obj (unit (base R)) ≅ unit (base A) := by
  let eW (W : Dᵒᵖ) : A.obj.obj W ≃ₗ[A.obj.obj W]
      (I.modules.obj (unit (base R))).val.obj W :=
    { toEquiv := (((sheafToPresheaf K (Type u)).mapIso
        (unitSetIso R A F I)).app W).toEquiv.symm
      map_add' := by
        intro a b
        change (show (I.modules.obj (unit (base R))).val.obj W from
          (unitSetIso R A F I).inv.hom.app W (a + b)) =
            (show (I.modules.obj (unit (base R))).val.obj W from
              (unitSetIso R A F I).inv.hom.app W a) +
                (show (I.modules.obj (unit (base R))).val.obj W from
                  (unitSetIso R A F I).inv.hom.app W b)
        let v : (I.modules.obj (unit (base R))).val.obj W :=
          (unitSetIso R A F I).inv.hom.app W (1 : A.obj.obj W)
        have he := @Module.add_smul ((base A).obj.obj W)
          ((I.modules.obj (unit (base R))).val.obj W) _ _
          (ModuleCat.isModule ((I.modules.obj (unit (base R))).val.obj W)) a b v
        exact (basis R A F I W (a + b)).trans (he.trans
          (congrArg₂ (fun x y : (I.modules.obj (unit (base R))).val.obj W ↦ x + y)
            (basis R A F I W a).symm (basis R A F I W b).symm))
      map_smul' := by
        intro a b
        change (unitSetIso R A F I).inv.hom.app W (a * b) =
          a • (show (I.modules.obj (unit (base R))).val.obj W from
            (unitSetIso R A F I).inv.hom.app W b)
        let v : (I.modules.obj (unit (base R))).val.obj W :=
          (unitSetIso R A F I).inv.hom.app W (1 : A.obj.obj W)
        let md := ModuleCat.isModule ((I.modules.obj (unit (base R))).val.obj W)
        have he := @mul_smul ((base A).obj.obj W)
          ((I.modules.obj (unit (base R))).val.obj W) _
          md.toDistribMulAction.toMulAction.toSemigroupAction a b v
        exact (basis R A F I W (a * b)).trans (he.trans
          (congrArg (fun x : (I.modules.obj (unit (base R))).val.obj W ↦ a • x)
            (basis R A F I W b).symm)) }
  let ep : (unit (base A)).val ≅ (I.modules.obj (unit (base R))).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun k ↦ k a) ((unitSetIso R A F I).inv.hom.naturality f))
  exact ((fullyFaithfulForget (base A)).preimageIso (X := unit (base A))
    (Y := I.modules.obj (unit (base R))) ep).symm
@[no_expose]
private noncomputable def isoOfHomEquiv
    {E : Type*} [Category E] (X Y : E) (e : ∀ H, (X ⟶ H) ≃ (Y ⟶ H))
    (hn : ∀ H H' (f : X ⟶ H) (b : H ⟶ H'), e H' (f ≫ b) = e H f ≫ b) : X ≅ Y where
  hom := (e Y).symm (𝟙 Y)
  inv := e X (𝟙 X)
  hom_inv_id := by
    apply (e X).injective
    rw [hn, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := hn X Y (𝟙 X) ((e Y).symm (𝟙 Y))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm
@[no_expose]
private noncomputable def scalarUnitIso
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) :
    (CochainScalarConstruction.tensorFunctor c).obj (unit (base A)) ≅ unit (base S) := by
  let e := fun H : SheafOfModules.{u} (base S) ↦
    (CochainScalarConstruction.tensorHomEquiv c (unit (base A)) H).trans
      (((CochainScalarConstruction.restriction c).obj H).unitHomEquiv.trans
        H.unitHomEquiv.symm)
  refine isoOfHomEquiv _ _ e ?_
  intro H H' f b
  apply H'.unitHomEquiv.injective
  change H'.unitHomEquiv (H'.unitHomEquiv.symm _) =
    H'.unitHomEquiv (H.unitHomEquiv.symm _ ≫ b)
  erw [Equiv.apply_symm_apply, unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
  rw [CochainScalarConstruction.tensorHomEquiv_naturality_right]
  apply Subtype.ext
  funext W
  rfl

set_option maxHeartbeats 80000 in
-- Limit unfolding of scalar-extension Hom equivalences.
private theorem scalarUnitIso_insertion
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) (W : Dᵒᵖ) (a : A.obj.obj W) :
    (scalarUnitIso A S c).hom.val.app W
      ((CochainScalarConstruction.tensorUnit c (unit (base A))).hom.app W a) =
        (c.hom.app W).hom a := by
  let H := unit (base S)
  have he : CochainScalarConstruction.tensorHomEquiv c (unit (base A)) H
      (scalarUnitIso A S c).hom =
      ((CochainScalarConstruction.restriction c).obj H).unitHomEquiv.symm
        (H.unitHomEquiv (𝟙 H)) := by
    change CochainScalarConstruction.tensorHomEquiv c (unit (base A)) H
      ((CochainScalarConstruction.tensorHomEquiv c (unit (base A)) H).symm
        (((CochainScalarConstruction.restriction c).obj H).unitHomEquiv.symm
          (H.unitHomEquiv (𝟙 H)))) = _
    exact Equiv.apply_symm_apply _ _
  have ht := CochainScalarConstruction.tensorAdjunction_underlying c (unit (base A)) H
    (scalarUnitIso A S c).hom
  change (CochainScalarConstruction.underlying A).map
    (CochainScalarConstruction.tensorHomEquiv c (unit (base A)) H
      (scalarUnitIso A S c).hom) = _ at ht
  have hv := (congrArg (fun f ↦ f.hom.app W a) ht).symm.trans
    (congrArg (fun f ↦ f.val.app W a) he)
  change ((scalarUnitIso A S c).hom.val.app W
      ((CochainScalarConstruction.tensorUnit c (unit (base A))).hom.app W a)) =
    @HSMul.hSMul (A.obj.obj W)
      (((CochainScalarConstruction.restriction c).obj H).val.obj W)
      (((CochainScalarConstruction.restriction c).obj H).val.obj W) _ a
        (1 : S.obj.obj W) at hv
  have hs : @HSMul.hSMul (A.obj.obj W)
      (((CochainScalarConstruction.restriction c).obj H).val.obj W)
      (((CochainScalarConstruction.restriction c).obj H).val.obj W) _ a
        (1 : S.obj.obj W) = (c.hom.app W).hom a := by
    change (c.hom.app W).hom a * 1 = _
    exact mul_one _
  exact hv.trans hs

open MonoidalCategory
set_option maxHeartbeats 30000 in
-- Use the abstract unitor coherence before specializing sheafification.
private theorem unitor_transport
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (L : A ⥤ B) [L.Monoidal] (X : A) (Y : B) (e : L.obj X ≅ Y)
    (eU : L.obj (𝟙_ A) ≅ 𝟙_ B) (hu : eU.inv = Functor.LaxMonoidal.ε L) :
    (Functor.Monoidal.μIso L X (𝟙_ A)).inv ≫ (e ⊗ᵢ eU).hom ≫ (ρ_ Y).hom =
      L.map (ρ_ X).hom ≫ e.hom := by
  have he : (e ⊗ᵢ eU).hom ≫ (ρ_ Y).hom =
      (𝟙 _ ⊗ₘ eU.hom) ≫ (ρ_ (L.obj X)).hom ≫ e.hom := by
    simp only [tensorIso_hom, tensorHom_def', Category.assoc,
      rightUnitor_naturality, id_whiskerRight, Category.id_comp]
  rw [he, Functor.LaxMonoidal.right_unitality L]
  have hw : (𝟙 (L.obj X) ⊗ₘ eU.hom) ≫
      L.obj X ◁ Functor.LaxMonoidal.ε L = 𝟙 _ := by
    rw [← hu, tensorHom_def, id_whiskerRight, Category.id_comp,
      ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id]
  simp only [← Category.assoc]
  rw [Category.assoc (Functor.Monoidal.μIso L X (𝟙_ A)).inv, hw, Category.comp_id]
  change (((Functor.Monoidal.μIso L X (𝟙_ A)).inv ≫
    (Functor.Monoidal.μIso L X (𝟙_ A)).hom) ≫ _) ≫ _ = _
  rw [Iso.inv_hom_id, Category.id_comp]

attribute [local semireducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option maxHeartbeats 180000 in
-- Specialize the abstract formula using the explicit counit components.
private theorem unitor_formula
    (M : SheafOfModules.{u} (base R)) :
    (tensorObjIsoSheafification M (unit (base R))).inv ≫
      ((monoidalCategory R).rightUnitor M).hom =
    (PresheafOfModules.sheafification (𝟙 (base R).obj)).map
      ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).counit.app M := by
  let L := PresheafOfModules.sheafification (𝟙 (base R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)
  let eM : L.obj M.val ≅ M := (asIso adj.counit).app M
  let eU : L.obj (unit (base R)).val ≅ unit (base R) :=
    (asIso adj.counit).app (unit (base R))
  dsimp only [tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc]
  apply unitor_transport L M.val M eM eU
  rfl

set_option maxHeartbeats 80000 in
-- Use the sheafification API without unfolding its monoidal structure.
private theorem unitor_pure
    (M : SheafOfModules.{u} (base R)) (W : Cᵒᵖ)
    (m : M.val.obj W) (r : R.obj.obj W) :
    ((monoidalCategory R).rightUnitor M).hom.val.app W
      (CochainScalarConstruction.pure R M (unit (base R)) W m r) = r • m := by
  have h := unitor_formula R M
  have he := congrArg (fun f ↦ f.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
      (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r))) h
  change ((monoidalCategory R).rightUnitor M).hom.val.app W
    (CochainScalarConstruction.pure R M (unit (base R)) W m r) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).counit.app M).val.app W
      (((PresheafOfModules.sheafification (𝟙 (base R).obj)).map
        ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom).val.app W
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
            (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r))) at he
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.naturality
    ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom
  have hn' := congrArg (fun f ↦ f.app W (m ⊗ₜ[R.obj.obj W] r)) hn
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
      M.val).app W (r • m) =
    ((PresheafOfModules.sheafification (𝟙 (base R).obj)).map
      ((PresheafOfModules.monoidalCategory (R := R.obj)).rightUnitor M.val).hom).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).unit.app
          (M.val ⊗ (unit (base R)).val)).app W (m ⊗ₜ[R.obj.obj W] r)) at hn'
  rw [← hn'] at he
  have hc := (PresheafOfModules.sheafificationAdjunction (𝟙 (base R).obj)).right_triangle_components
    M
  have hh := congrArg (fun f ↦ f.app W (r • m)) hc
  exact he.trans hh
private theorem unitIso_hom_apply (W : Dᵒᵖ)
    (m : (I.modules.obj (unit (base R))).val.obj W) :
    (unitIso R A F I).hom.val.app W m = (unitSetIso R A F I).hom.hom.app W m := by
  rfl

@[no_expose]
private noncomputable def pullbackUnitIso
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) :
    (CochainScalarConstruction.tensorFunctor c).obj (I.modules.obj (unit (base R))) ≅
      unit (base S) :=
  (CochainScalarConstruction.tensorFunctor c).mapIso (unitIso R A F I) ≪≫
    scalarUnitIso A S c

private theorem pullbackUnitIso_insertion
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S) (W : Dᵒᵖ)
    (m : (I.modules.obj (unit (base R))).val.obj W) :
    (pullbackUnitIso R A F I S c).hom.val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m) =
        (c.hom.app W).hom ((unitSetIso R A F I).hom.hom.app W m) := by
  have hu := congrArg (fun k ↦ k.val.app W m)
    ((CochainScalarConstruction.tensorAdjunction c).unit.naturality (unitIso R A F I).hom)
  change (CochainScalarConstruction.tensorUnit c (unit (base A))).hom.app W
      ((unitIso R A F I).hom.val.app W m) =
    ((CochainScalarConstruction.tensorFunctor c).map (unitIso R A F I).hom).val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m)
    at hu
  change (scalarUnitIso A S c).hom.val.app W
    (((CochainScalarConstruction.tensorFunctor c).map (unitIso R A F I).hom).val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj (unit (base R)))).hom.app W m)) = _
  rw [← hu, scalarUnitIso_insertion, unitIso_hom_apply]

set_option maxHeartbeats 60000 in
-- Bound the Hom-equivalence computation by its explicit underlying formula.
private theorem scalarHom_ext
    (S : Sheaf K CommRingCat.{u}) (c : A ⟶ S)
    (M : SheafOfModules.{u} (base A)) (H : SheafOfModules.{u} (base S))
    {f g : (CochainScalarConstruction.tensorFunctor c).obj M ⟶ H}
    (h : ∀ W m, f.val.app W
      ((CochainScalarConstruction.tensorUnit c M).hom.app W m) =
      g.val.app W ((CochainScalarConstruction.tensorUnit c M).hom.app W m)) : f = g := by
  apply (CochainScalarConstruction.tensorHomEquiv c M H).injective
  apply (CochainScalarConstruction.underlying A).map_injective
  have hf := CochainScalarConstruction.tensorAdjunction_underlying c M H f
  have hg := CochainScalarConstruction.tensorAdjunction_underlying c M H g
  change (CochainScalarConstruction.underlying A).map
    (CochainScalarConstruction.tensorHomEquiv c M H f) = _ at hf
  change (CochainScalarConstruction.underlying A).map
    (CochainScalarConstruction.tensorHomEquiv c M H g) = _ at hg
  rw [hf, hg]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro m
  exact h W m

private theorem unitMap_unique
    {A B : Type*} [Category A] [Category B] [MonoidalCategory A] [MonoidalCategory B]
    (F : A ⥤ B) (mu : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (j j' : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hj : ∀ X, (mu X (𝟙_ A)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom)
    (hj' : ∀ X, (mu X (𝟙_ A)).hom ≫ (𝟙 (F.obj X) ⊗ₘ j'.hom) ≫
      (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom) : j = j' := by
  have h := (hj (𝟙_ A)).trans (hj' (𝟙_ A)).symm
  have ht : (𝟙 (F.obj (𝟙_ A)) ⊗ₘ j.hom) =
      (𝟙 (F.obj (𝟙_ A)) ⊗ₘ j'.hom) := by
    apply (cancel_mono (ρ_ (F.obj (𝟙_ A))).hom).mp
    apply (cancel_epi (mu (𝟙_ A) (𝟙_ A)).hom).mp
    simpa only [Category.assoc] using h
  have ht' := congrArg (fun f ↦ (j.inv ⊗ₘ 𝟙 (F.obj (𝟙_ A))) ≫ f ≫
    (j.hom ⊗ₘ 𝟙 (𝟙_ B))) ht
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht'
  have he := congrArg (fun f ↦ f ≫ (λ_ (𝟙_ B)).hom) ht'
  simp only [id_tensorHom, leftUnitor_naturality] at he
  apply Iso.ext
  exact (cancel_epi (λ_ (F.obj (𝟙_ A))).hom).mp he

end UnitConstruction

-- The explicit coefficient unit in this statement needs the unit projection to reduce.
attribute [local semireducible] monoidalCategory

set_option backward.isDefEq.respectTransparency true in
/-- The ordinary unit normalization of the canonical tensor comparison.
Source: Stacks 03EL, pure tensors with the second factor the coefficient ring
(auxiliary; not a blueprint node).
Proof: scalar multiplication gives L(R) = S. On a generalized pure tensor m tensor r,
both composites multiply by the image of r in S. Sheafification extends equality.
The equation at M=R, together with the tensor unitors, uniquely determines j.
Unlike SheafOfModules.canonicalRingedTensorComparison_unit, the explicit binders
below retain independent uC, vC, uD, vD and coefficient/module universe u. -/
theorem canonicalRingedTensorComparison_unit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃! j : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom) := by
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let T := CochainScalarConstruction.tensorFunctor c
  let ε : L ≅ I.modules ⋙ T := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  have hq (M) (W : Dᵒᵖ) (m : (I.modules.obj M).val.obj W) :
      (k.q M).hom.app W m = (ε.inv.app M).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m) := by
    rw [k.q_one, CochainScalarConstruction.tensorUnit_apply]
    rfl
  have hqmap {M N} (f : M ⟶ N) (W : Dᵒᵖ)
      (m : (I.modules.obj M).val.obj W) :
      (L.map f).val.app W ((k.q M).hom.app W m) =
        (k.q N).hom.app W ((I.modules.map f).val.app W m) := by
    rw [hq, hq]
    have hn := congrArg (fun a ↦ a.val.app W
      ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m))
        (ε.inv.naturality f)
    have hu := congrArg (fun a ↦ a.val.app W m)
      ((CochainScalarConstruction.tensorAdjunction c).unit.naturality (I.modules.map f))
    change (CochainScalarConstruction.tensorUnit c (I.modules.obj N)).hom.app W
        ((I.modules.map f).val.app W m) =
      (T.map (I.modules.map f)).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj M)).hom.app W m) at hu
    exact hn.symm.trans (congrArg ((ε.inv.app N).val.app W) hu.symm)
  let U := unit (UnitConstruction.base R)
  let j : L.obj U ≅ unit (UnitConstruction.base S) :=
    ε.app U ≪≫ UnitConstruction.pullbackUnitIso R RI uInv I S c
  have hj : ∀ M, (k.mu M U).hom ≫ (𝟙 (L.obj M) ⊗ₘ j.hom) ≫
      (ρ_ (L.obj M)).hom = L.map (ρ_ M).hom := by
    intro M
    let P := (monoidalCategory R).tensorObj M U
    let Z := (UnitConstruction.mset R).obj P
    let x : Z ⟶ (UnitConstruction.mset R).obj M :=
      (UnitConstruction.mset R).map (ρ_ M).hom
    let y : Z ⟶ (UnitConstruction.mset R).obj U :=
      ⟨{ app := fun V ↦ ↾(fun _ ↦ (1 : R.obj.obj V))
         naturality := by
           intro V V' f
           ext z
           exact (map_one (R.obj.map f).hom).symm }⟩
    have hz (V : Cᵒᵖ) (z : Z.obj.obj V) :
        (𝟙 Z : Z ⟶ Z).hom.app V z = CochainScalarConstruction.pure R M U V
          (x.hom.app V z) (y.hom.app V z) := by
      have he := UnitConstruction.unitor_pure R M V ((ρ_ M).hom.val.app V z) 1
      rw [one_smul] at he
      have ht := congrArg ((ρ_ M).inv.val.app V) he
      have hc (v : P.val.obj V) := congrArg (fun f ↦ f.val.app V v) (ρ_ M).hom_inv_id
      exact ((hc _).symm.trans (ht.trans (hc z))).symm
    apply (cancel_epi (ε.inv.app P)).mp
    apply UnitConstruction.scalarHom_ext RI S c (I.modules.obj P) (L.obj M)
    intro W m
    change (ρ_ (L.obj M)).hom.val.app W
        ((𝟙 (L.obj M) ⊗ₘ j.hom).val.app W
          ((k.mu M U).hom.val.app W
            ((ε.inv.app P).val.app W
              ((CochainScalarConstruction.tensorUnit c (I.modules.obj P)).hom.app W m)))) =
      (L.map (ρ_ M).hom).val.app W ((ε.inv.app P).val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj P)).hom.app W m))
    rw [← hq P W m]
    let t := (I.moduleUnderlying.hom.app P).hom.app W m
    let a := (uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t
    let b := (uInv.map y ≫ I.moduleUnderlying.inv.app U).hom.app W t
    have hc : (I.moduleUnderlying.inv.app P).hom.app W t = m :=
      congrArg (fun f ↦ f.hom.app W m) (I.moduleUnderlying.app P).hom_inv_id
    have hp := k.pure M U Z x y (𝟙 Z) hz W t
    rw [uInv.map_id] at hp
    change (k.mu M U).hom.val.app W
        ((k.q P).hom.app W ((I.moduleUnderlying.inv.app P).hom.app W t)) =
      CochainScalarConstruction.pure S (L.obj M) (L.obj U) W
        ((k.q M).hom.app W a) ((k.q U).hom.app W b) at hp
    rw [hc] at hp
    have hb : (UnitConstruction.unitSetIso R RI uInv I).hom.hom.app W b =
        (1 : RI.obj.obj W) := by
      have hi := congrArg (fun f ↦ f.hom.app W ((uInv.map y).hom.app W t))
        (I.moduleUnderlying.app U).inv_hom_id
      change (I.moduleUnderlying.hom.app U).hom.app W b =
        (uInv.map y).hom.app W t at hi
      change I.ringUnderlying.hom.hom.app W
        ((I.moduleUnderlying.hom.app U).hom.app W b) = (1 : RI.obj.obj W)
      rw [hi]
      exact I.ringOne Z y (fun _ _ ↦ rfl) W t
    have hu : j.hom.val.app W ((k.q U).hom.app W b) = (1 : S.obj.obj W) := by
      have hqj := congrArg (fun v : (L.obj U).val.obj W ↦ j.hom.val.app W v) (hq U W b)
      refine hqj.trans ?_
      change (UnitConstruction.pullbackUnitIso R RI uInv I S c).hom.val.app W
        ((ε.hom.app U).val.app W ((ε.inv.app U).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b))) =
          (1 : S.obj.obj W)
      have hi := congrArg (fun f ↦ f.val.app W
        ((CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b))
          (ε.app U).inv_hom_id
      have hi' : (ε.hom.app U).val.app W ((ε.inv.app U).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b)) =
          (CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b := by
        change (ε.hom.app U).val.app W ((ε.inv.app U).val.app W
          ((CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b)) =
            (CochainScalarConstruction.tensorUnit c (I.modules.obj U)).hom.app W b at hi
        exact hi
      refine (congrArg ((UnitConstruction.pullbackUnitIso R RI uInv I S c).hom.val.app W)
        hi').trans ?_
      exact (UnitConstruction.pullbackUnitIso_insertion R RI uInv I S c W b).trans
        ((congrArg ((c.hom.app W).hom) hb).trans (map_one _))
    have ha : a = (I.modules.map (ρ_ M).hom).val.app W m := by
      have hi := congrArg (fun f ↦ f.hom.app W t)
        (I.moduleUnderlying.inv.naturality (ρ_ M).hom)
      change a = (I.modules.map (ρ_ M).hom).val.app W
        ((I.moduleUnderlying.inv.app P).hom.app W t) at hi
      exact hi.trans (congrArg ((I.modules.map (ρ_ M).hom).val.app W) hc)
    have ht := CochainScalarConstruction.pure_map S (𝟙 (L.obj M)) j.hom W
      ((k.q M).hom.app W a) ((k.q U).hom.app W b)
    have ht' : (𝟙 (L.obj M) ⊗ₘ j.hom).val.app W
        (CochainScalarConstruction.pure S (L.obj M) (L.obj U) W
          ((k.q M).hom.app W a) ((k.q U).hom.app W b)) =
      CochainScalarConstruction.pure S (L.obj M) (unit (UnitConstruction.base S)) W
        ((k.q M).hom.app W a) (j.hom.val.app W ((k.q U).hom.app W b)) := ht
    have he := UnitConstruction.unitor_pure S (L.obj M) W
      ((k.q M).hom.app W a)
      (show S.obj.obj W from j.hom.val.app W ((k.q U).hom.app W b))
    have hs : (show (UnitConstruction.base S).obj.obj W from
        j.hom.val.app W ((k.q U).hom.app W b)) •
        (show (L.obj M).val.obj W from (k.q M).hom.app W a) =
        (k.q M).hom.app W a := by
      exact (congrArg (fun r : (UnitConstruction.base S).obj.obj W ↦
        r • (show (L.obj M).val.obj W from (k.q M).hom.app W a)) hu).trans
          (@MulAction.one_smul _ _ _
            (ModuleCat.isModule ((L.obj M).val.obj W)).toDistribMulAction.toMulAction _)
    exact (congrArg (fun z ↦ (ρ_ (L.obj M)).hom.val.app W
      ((𝟙 (L.obj M) ⊗ₘ j.hom).val.app W z)) hp).trans
        ((congrArg ((ρ_ (L.obj M)).hom.val.app W) ht').trans
          (he.trans (hs.trans ((congrArg ((k.q M).hom.app W) ha).trans
            (hqmap (ρ_ M).hom W m).symm))))
  refine ⟨j, hj, ?_⟩
  intro j' hj'
  exact UnitConstruction.unitMap_unique L k.mu j' j hj' hj

attribute [local irreducible] monoidalCategory

set_option backward.isDefEq.respectTransparency true

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC
      (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  exact tensorPullbackTotal L k.mu k.naturality P Q

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :=
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (tensorPullbackTotal_isIso L k.mu k.naturality V am P Q)

end SheafOfModules.CochainTensorComparison

universe s h
namespace SheafOfModules.CochainTensorComparison

end SheafOfModules.CochainTensorComparison

namespace CategoryTheory.CochainPullback
set_option autoImplicit false

/-- Module sheaves, using Mathlib's category verbatim.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
abbrev Modules {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- Integer-indexed cochain sheaves; there is no boundedness restriction.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
abbrev Complex {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) := CochainComplex (Modules R) ℤ

/-- Underlying sheaves of sets of module sheaves.
Source: Stacks 03DA (auxiliary; not a blueprint node). -/
noncomputable abbrev underlying {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) : Modules R ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The inverse-image adjunction and its actual scalar-extension presentation.
The equalities `hobj` and `hmap` specify the pullback functor on objects and maps;
they are presentation data rather than an arbitrary additive functor.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
structure RingedPullback (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w}) where
  uInv : Sheaf J (Type w) ⥤ Sheaf K (Type w)
  uPush : Sheaf K (Type w) ⥤ Sheaf J (Type w)
  adj : uInv ⊣ uPush
  finiteLimits : PreservesFiniteLimits uInv
  RI : Sheaf K CommRingCat.{w}
  I : SheafOfModules.AlgebraicInverseImage uInv R RI
  coefficient : RI ⟶ S
  L : Modules R ⥤ Modules S
  hobj : ∀ M, L.obj M = SheafOfModules.changeOfRings coefficient (I.modules.obj M)
  hmap : ∀ {M N} (f : M ⟶ N), L.map f = eqToHom (hobj M) ≫
    SheafOfModules.changeOfRingsHom coefficient (I.modules.obj M) (I.modules.map f) ≫
      eqToHom (hobj N).symm
  V : Modules S ⥤ Modules R
  moduleAdj : L ⊣ V
  [additive : L.Additive]

attribute [instance] RingedPullback.additive

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- The normalized module comparison, generalized to independently sized sites.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
abbrev Comparison (f : RingedPullback R S) :=
  SheafOfModules.CochainTensorComparison.CanonicalRingedTensorComparison
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj

/-- Termwise pullback on all cochain complexes.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable abbrev pull (f : RingedPullback R S) :=
  f.L.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The direct-sum total comparison, with insertion of 1 and contraction as inverse.
Its constituent maps are exactly the normalized module comparison in the dependency.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
noncomputable def comparison (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) : (pull f).obj (P ⊗ Q) ≅ (pull f).obj P ⊗ (pull f).obj Q :=
  (k.totalIso R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.V f.moduleAdj P Q).symm

attribute [local semireducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- The unit isomorphism uniquely fixed by the module pure-tensor formula.
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
noncomputable def moduleUnit (f : RingedPullback R S) (k : Comparison f) :
    f.L.obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules S) :=
  Classical.choose (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
    R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The termwise lift of the normalized unit map, from R[0] to S[0].
Source: Stacks 03EL (auxiliary; not a blueprint node). -/
noncomputable def unit (f : RingedPullback R S) (k : Comparison f) :
    (pull f).obj (𝟙_ (Complex R)) ≅ 𝟙_ (Complex S) :=
  (HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).app (𝟙_ (Modules R)) ≪≫
    (HomologicalComplex.single (Modules S) (.up ℤ) 0).mapIso (moduleUnit f k)

end CategoryTheory.CochainPullback
