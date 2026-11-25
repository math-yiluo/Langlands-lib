/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Types.Products
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import WeilConjectures.SecSmoothPurity.CochainCompositeHom
import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Signed tensor comparison and coherence on cochain sheaves

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, and sites-modules.tex,
Tag 03EL (blueprint: def-pur-cochain-tensor-coherence-data).

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
attribute [local irreducible] monoidalCategory

set_option backward.isDefEq.respectTransparency true

end SheafOfModules.CochainTensorComparison

universe s h
namespace SheafOfModules.CochainTensorComparison

end SheafOfModules.CochainTensorComparison

namespace CategoryTheory.CochainPullback
set_option autoImplicit false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

attribute [instance] RingedPullback.additive

variable {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

/-- Every algebraically presented ringed geometric morphism has the module
functor and adjunction used in RingedPullback; these are presentation data.
Source: Stacks 03D2, 03CY and 03D7
(blueprint: def-pur-cochain-tensor-coherence-data).
Proof: transport module operations along the left-exact inverse image. Extend
scalars by the existing sheafified tensor construction, on maps by id tensor h.
Transpose module homomorphisms through the set adjunction and the tensor
universal property, followed by module sheafification. The resulting natural
hom bijection gives the right adjoint and adjunction. Left adjoints between
abelian categories are additive. No flatness or site-universe equality is used. -/
theorem ringedPullbackPresentation_exists
    (uInv : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (uPush : Sheaf K (Type w) ⥤ Sheaf J (Type w))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (RI : Sheaf K CommRingCat.{w})
    (I : SheafOfModules.AlgebraicInverseImage uInv R RI) (c : RI ⟶ S) :
    ∃ (L : Modules R ⥤ Modules S)
      (hobj : ∀ M, L.obj M = SheafOfModules.changeOfRings c (I.modules.obj M)),
      (∀ {M N : Modules R} (b : M ⟶ N), L.map b = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map b) ≫
          eqToHom (hobj N).symm) ∧
      ∃ V : Modules S ⥤ Modules R, Nonempty (L ⊣ V) ∧ L.Additive := by
  obtain ⟨P, ⟨aP⟩⟩ :=
    SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists R RI
      uInv uPush adj I
  let L := I.modules ⋙ SheafOfModules.CochainScalarConstruction.tensorFunctor c
  let aL := aP.comp (SheafOfModules.CochainScalarConstruction.tensorAdjunction c)
  let : PreservesColimits L := aL.leftAdjoint_preservesColimits
  have hAdd : L.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
    exact Functor.additive_of_preservesBinaryBiproducts L
  exact ⟨L, fun _ ↦ rfl, fun _ ↦ rfl, _, ⟨aL⟩, hAdd⟩

attribute [local semireducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The adjunction-conjugate module comparison for a composite.
Source: Stacks 0D6D (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def compositionModule
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (right : h.V ≅ g.V ⋙ f.V) : h.L ≅ f.L ⋙ g.L :=
  (conjugateIsoEquiv (f.moduleAdj.comp g.moduleAdj) h.moduleAdj).symm right.symm

/-- Presentation of the actual composite, normalized on inverse-image generators.
The two right-adjoint comparisons give the inverse-image adjunction comparison
and its module analogue. The equation is the scalar-association formula
`1 ⊗ x ↦ 1 ⊗ (1 ⊗ x)` on every generalized element; linearity then gives
`t ⊗ x ↦ t ⊗ (1 ⊗ x)`. It determines the comparison, rather than merely
requiring an arbitrary endomorphism to commute with tensor.
Source: Stacks 0D6D and 03EL
(blueprint: def-pur-cochain-tensor-coherence-data). -/
structure CompositePresentation
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    (kf : Comparison f) (kg : Comparison g) (kh : Comparison h) where
  rightSets : h.uPush ≅ g.uPush ⋙ f.uPush
  rightModules : h.V ≅ g.V ⋙ f.V
  scalarAssociation : ∀ (M : Modules R) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying R).obj M),
    h.uInv.map x ≫ h.I.moduleUnderlying.inv.app M ≫ kh.q M ≫
        (underlying T).map ((compositionModule f g h rightModules).hom.app M) =
      ((conjugateIsoEquiv (f.adj.comp g.adj) h.adj).symm
        rightSets.symm).hom.app Z ≫
        g.uInv.map (f.uInv.map x ≫ f.I.moduleUnderlying.inv.app M ≫ kf.q M) ≫
          g.I.moduleUnderlying.inv.app (f.L.obj M) ≫ kg.q (f.L.obj M)

/-- Termwise lift of the canonical adjunction/scalar-association comparison.
Source: Stacks 0D6D (blueprint: def-pur-cochain-tensor-coherence-data). -/
noncomputable def composition
    {E : Type uE} [Category.{vE} E] [EssentiallySmall.{w} E]
    {H : GrothendieckTopology E}
    [H.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {T : Sheaf H CommRingCat.{w}} (f : RingedPullback R S)
    (g : RingedPullback S T) (h : RingedPullback R T)
    {kf : Comparison f} {kg : Comparison g} {kh : Comparison h}
    (a : CompositePresentation f g h kf kg kh) (P : Complex R) :
    (pull h).obj P ≅ (pull g).obj ((pull f).obj P) :=
  (Functor.mapHomologicalComplexCompIso
    (compositionModule f g h a.rightModules).symm (.up ℤ)).symm.app P

end CategoryTheory.CochainPullback
